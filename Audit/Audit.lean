/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lean

/-!
# ATLAS axiom / sorry auditor

A standalone executable that loads the compiled `Atlas` library and reports,
for every declaration defined in an `Atlas.*` module, whether it is:

* `proved`       -- depends only on the benign Lean/Mathlib axioms
                    (`propext`, `Classical.choice`, `Quot.sound`);
* `sorry`        -- transitively depends on `sorryAx`, i.e. an incomplete
                    proof;
* `other-axiom`  -- depends on some other axiom, surfaced for review.

Each book's `report.json` already carries an LLM-judged `proof_integrity`
score. This audit is different: it is computed by the same dependency
traversal the Lean kernel trusts, so it is ground truth about what is
actually proved rather than a model's estimate.

Run with `lake exe atlas_audit`. It writes `audit/proved.json` and prints a
per-book summary. Pass `--strict` to exit non-zero when any declaration
depends on a non-benign, non-`sorry` axiom.
-/

open Lean

namespace AtlasAudit

/-- Axioms that are standard in classical Mathlib and do not weaken a proof. -/
def benignAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- The `sorry` placeholder axiom. A declaration that reaches it is unproved. -/
def sorryAxiom : Name := `sorryAx

inductive Status where
  | proved
  | sorryStub
  | otherAxiom
  deriving BEq

def Status.toString : Status → String
  | .proved => "proved"
  | .sorryStub => "sorry"
  | .otherAxiom => "other-axiom"

/-- Collect the transitive axioms a declaration depends on, reusing core's
`CollectAxioms` traversal directly. The traversal is pure
(`ReaderT Environment (StateM State)`), so no `CoreM` context is needed. -/
def axiomsOf (env : Environment) (c : Name) : Array Name :=
  let (_, s) := ((Lean.CollectAxioms.collect c).run env).run {}
  s.axioms

def classify (axs : Array Name) : Status :=
  if axs.contains sorryAxiom then .sorryStub
  else if axs.all (fun a => benignAxioms.contains a) then .proved
  else .otherAxiom

/-- A module belongs to ATLAS when its root component is `Atlas`. -/
def isAtlasModule (m : Name) : Bool := m.getRoot == `Atlas

/-- Book name = second component of the module path, e.g.
`Atlas.RealAnalysis.code.Foo` maps to `RealAnalysis`. -/
def bookOf (m : Name) : Name :=
  match m.components with
  | _ :: book :: _ => book
  | _ => m

structure Tally where
  proved : Nat := 0
  sorryStub : Nat := 0
  otherAxiom : Nat := 0

def Tally.total (t : Tally) : Nat := t.proved + t.sorryStub + t.otherAxiom

def Tally.bump (t : Tally) : Status → Tally
  | .proved => { t with proved := t.proved + 1 }
  | .sorryStub => { t with sorryStub := t.sorryStub + 1 }
  | .otherAxiom => { t with otherAxiom := t.otherAxiom + 1 }

/-- Right-pad a string to `n` columns for fixed-width table output. -/
def pad (s : String) (n : Nat) : String :=
  if s.length >= n then s
  else s ++ String.ofList (List.replicate (n - s.length) ' ')

/-- Left-pad a number to `n` columns. -/
def lpad (k : Nat) (n : Nat) : String :=
  let s := toString k
  if s.length >= n then s
  else String.ofList (List.replicate (n - s.length) ' ') ++ s

end AtlasAudit

open AtlasAudit

/-- Find or initialize the tally for `book` in the assoc array of books.
There are ~26 books, so a linear scan is cheaper than a hash map and avoids
any version drift in the hash-map API. -/
def bumpBook (books : Array (Name × Tally)) (book : Name) (st : Status) :
    Array (Name × Tally) := Id.run do
  for h : i in [0:books.size] do
    let (b, t) := books[i]
    if b == book then
      return books.set i (b, t.bump st)
  return books.push (book, (Tally.bump {} st))

unsafe def main (args : List String) : IO Unit := do
  let strict := args.contains "--strict"
  let outDir : System.FilePath :=
    match args.filter (fun a => !a.startsWith "--") with
    | p :: _ => p
    | [] => "audit"
  initSearchPath (← findSysroot)
  let imports : Array Import := #[{ module := `Atlas }]
  withImportModules imports {} (trustLevel := 1024) fun env => do
    let names := env.header.moduleNames
    let datas := env.header.moduleData
    let mut perDecl : Array Json := #[]
    let mut books : Array (Name × Tally) := #[]
    let mut otherAxiomCount := 0
    for h : i in [0:names.size] do
      let modName := names[i]
      if isAtlasModule modName then
        let book := bookOf modName
        let data := datas[i]!
        for declName in data.constNames do
          if declName.isInternalDetail then
            continue
          let axs := axiomsOf env declName
          let status := classify axs
          books := bumpBook books book status
          if status == .otherAxiom then
            otherAxiomCount := otherAxiomCount + 1
          perDecl := perDecl.push <| Json.mkObj [
            ("declaration", toJson declName.toString),
            ("book", toJson book.toString),
            ("module", toJson modName.toString),
            ("status", toJson status.toString),
            ("axioms", toJson (axs.map (·.toString)))
          ]
    let sorted := books.qsort (fun a b => a.1.toString < b.1.toString)
    let mut bookJson : Array Json := #[]
    let mut totProved := 0
    let mut totSorry := 0
    let mut totOther := 0
    IO.println (pad "Book" 36 ++ lpad' "proved" ++ lpad' "sorry"
      ++ lpad' "other" ++ lpad' "total")
    IO.println (String.ofList (List.replicate 60 '-'))
    for (book, t) in sorted do
      totProved := totProved + t.proved
      totSorry := totSorry + t.sorryStub
      totOther := totOther + t.otherAxiom
      IO.println (pad book.toString 36 ++ lpad t.proved 8 ++ lpad t.sorryStub 8
        ++ lpad t.otherAxiom 8 ++ lpad t.total 8)
      bookJson := bookJson.push <| Json.mkObj [
        ("book", toJson book.toString),
        ("proved", toJson t.proved),
        ("sorry", toJson t.sorryStub),
        ("other_axiom", toJson t.otherAxiom),
        ("total", toJson t.total)
      ]
    IO.println (String.ofList (List.replicate 60 '-'))
    IO.println s!"TOTAL  proved={totProved}  sorry={totSorry}  \
      other-axiom={totOther}"
    let report := Json.mkObj [
      ("generated_by", toJson "atlas_audit"),
      ("benign_axioms", toJson (benignAxioms.map (·.toString))),
      ("summary", Json.mkObj [
        ("proved", toJson totProved),
        ("sorry", toJson totSorry),
        ("other_axiom", toJson totOther)
      ]),
      ("books", toJson bookJson),
      ("declarations", toJson perDecl)
    ]
    IO.FS.createDirAll outDir
    IO.FS.writeFile (outDir / "proved.json") (report.pretty ++ "\n")
    IO.println s!"Wrote {outDir}/proved.json ({perDecl.size} declarations)"
    if strict && otherAxiomCount > 0 then
      IO.eprintln s!"STRICT: {otherAxiomCount} declaration(s) depend on a \
        non-benign, non-sorry axiom."
      IO.Process.exit 1
where
  /-- Right-align a fixed header label into an 8-column field. -/
  lpad' (s : String) : String :=
    if s.length >= 8 then s
    else String.ofList (List.replicate (8 - s.length) ' ') ++ s
