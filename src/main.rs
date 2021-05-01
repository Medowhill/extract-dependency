use std::fs::{self, File};
use std::path::PathBuf;
use std::{
    collections::{HashMap, HashSet},
    io::Write,
};

use rustc_ast::{
    visit::{walk_crate, walk_item, Visitor},
    AngleBracketedArg, BareFnTy, FieldDef, FnRetTy, GenericArg, GenericArgs, Item, ItemKind, MutTy,
    ParenthesizedArgs, Path, Ty, TyAliasKind, TyKind, VariantData,
};
use rustc_session::parse::ParseSess;
use rustc_span::edition::Edition;

use clap::Clap;

#[derive(Clap)]
struct Args {
    input: Vec<PathBuf>,
}

fn main() -> std::io::Result<()> {
    let mut args: Args = Args::parse();
    assert_eq!(args.input.len(), 2);
    let out = args.input.pop().unwrap();
    let dir = args.input.pop().unwrap();
    let files: Vec<PathBuf> = files(dir, "rs");

    let mut collector = Collector { items: HashMap::new() };

    rustc_span::with_session_globals(Edition::Edition2018, || {
        let parse_sess = ParseSess::with_silent_emitter();

        for f in files {
            collector.collect(&f, &parse_sess);
        }
    });

    let mut graph = collector.items;
    graph.remove("Id");
    let mut s = HashSet::new();
    s.insert("UnsafeCell".to_string());
    graph.insert("Cell".to_string(), s);

    let mut g = graph.clone();
    let mut reachable = HashSet::new();
    reachable.insert("UnsafeCell".to_string());

    loop {
        let mut added = vec![];
        for (k, v) in &g {
            if !v.is_disjoint(&reachable) {
                added.push(k.clone());
            }
        }
        if added.is_empty() {
            break;
        }
        for t in added.drain(..) {
            g.remove(&t);
            reachable.insert(t);
        }
    }

    let mut file = File::create(out)?;

    file.write_all(b"digraph G {\n")?;
    for r in &reachable {
        if let Some(ks) = graph.get(r) {
            for k in ks.intersection(&reachable) {
                file.write_fmt(format_args!("  \"{}\" -> \"{}\";\n", r, k))?;
            }
        }
    }
    file.write_all(b"}")?;

    Ok(())
}

fn files(path: PathBuf, ext: &str) -> Vec<PathBuf> {
    if path.is_dir() {
        fs::read_dir(path)
            .unwrap()
            .into_iter()
            .flat_map(|entry| files(entry.unwrap().path(), ext))
            .collect()
    } else if path.extension().unwrap() == ext {
        vec![path]
    } else {
        vec![]
    }
}

struct Collector {
    items: HashMap<String, HashSet<String>>,
}

impl Collector {
    fn collect(&mut self, file: &PathBuf, sess: &ParseSess) {
        let krate = rustc_parse::parse_crate_from_file(&file, &sess).unwrap();
        walk_crate(self, &krate);
    }
}

impl<'ast> Visitor<'ast> for Collector {
    fn visit_item(&mut self, item: &'ast Item) {
        let k = item.ident.to_string();
        let res = match &item.kind {
            ItemKind::Struct(variant, _) => self.items.insert(k.clone(), variant.type_names()),
            ItemKind::TyAlias(kind) => self.items.insert(k.clone(), kind.type_names()),
            _ => None,
        };
        if let Some(v) = res {
            println!("[DUP] {}: {:?}", k, v);
        }

        walk_item(self, item);
    }
}

trait ContainTypes {
    fn type_names(&self) -> HashSet<String>;
}

impl ContainTypes for VariantData {
    fn type_names(&self) -> HashSet<String> {
        match self {
            VariantData::Struct(fs, _) | VariantData::Tuple(fs, _) => {
                fs.iter().flat_map(|f| f.type_names()).collect()
            }
            _ => HashSet::new(),
        }
    }
}

impl ContainTypes for FieldDef {
    fn type_names(&self) -> HashSet<String> {
        self.ty.type_names()
    }
}

impl ContainTypes for Ty {
    fn type_names(&self) -> HashSet<String> {
        match &self.kind {
            TyKind::Slice(ty) | TyKind::Array(ty, _) | TyKind::Paren(ty) => ty.type_names(),
            TyKind::Ptr(mt) | TyKind::Rptr(_, mt) => mt.type_names(),
            TyKind::BareFn(f) => f.type_names(),
            TyKind::Tup(tys) => tys.iter().flat_map(|ty| ty.type_names()).collect(),
            TyKind::Path(_, p) => p.type_names(),
            TyKind::ImplTrait(_, _)
            | TyKind::TraitObject(_, _)
            | TyKind::Typeof(_)
            | TyKind::MacCall(_)
            | TyKind::ImplicitSelf
            | TyKind::Never
            | TyKind::Infer
            | TyKind::Err
            | TyKind::CVarArgs => HashSet::new(),
        }
    }
}

impl ContainTypes for MutTy {
    fn type_names(&self) -> HashSet<String> {
        // self.ty.type_names()
        HashSet::new()
    }
}

impl ContainTypes for BareFnTy {
    fn type_names(&self) -> HashSet<String> {
        // let FnDecl { inputs, output } = self.decl.deref();
        // let mut set: HashSet<String> = inputs.iter().flat_map(|p| p.ty.type_names()).collect();
        // for tn in output.type_names() {
        //     set.insert(tn);
        // }
        // set
        HashSet::new()
    }
}

impl ContainTypes for FnRetTy {
    fn type_names(&self) -> HashSet<String> {
        match self {
            FnRetTy::Ty(ty) => ty.type_names(),
            _ => HashSet::new(),
        }
    }
}

impl ContainTypes for Path {
    fn type_names(&self) -> HashSet<String> {
        let seg = self.segments.last().unwrap();
        let mut set = seg.args.as_ref().map(|a| a.type_names()).unwrap_or(HashSet::new());
        set.insert(seg.ident.to_string());
        set
    }
}

impl ContainTypes for GenericArgs {
    fn type_names(&self) -> HashSet<String> {
        match self {
            GenericArgs::AngleBracketed(a) => a.args.iter().flat_map(|a| a.type_names()).collect(),
            GenericArgs::Parenthesized(a) => a.type_names(),
        }
    }
}

impl ContainTypes for AngleBracketedArg {
    fn type_names(&self) -> HashSet<String> {
        match self {
            AngleBracketedArg::Arg(a) => a.type_names(),
            AngleBracketedArg::Constraint(c) => match &c.gen_args {
                Some(a) => a.type_names(),
                None => HashSet::new(),
            },
        }
    }
}

impl ContainTypes for GenericArg {
    fn type_names(&self) -> HashSet<String> {
        match self {
            GenericArg::Type(ty) => ty.type_names(),
            _ => HashSet::new(),
        }
    }
}

impl ContainTypes for ParenthesizedArgs {
    fn type_names(&self) -> HashSet<String> {
        let mut set: HashSet<String> = self.inputs.iter().flat_map(|ty| ty.type_names()).collect();
        for tn in self.output.type_names() {
            set.insert(tn);
        }
        set
    }
}

impl ContainTypes for TyAliasKind {
    fn type_names(&self) -> HashSet<String> {
        self.3.as_ref().map(|ty| ty.type_names()).unwrap_or(HashSet::new())
    }
}
