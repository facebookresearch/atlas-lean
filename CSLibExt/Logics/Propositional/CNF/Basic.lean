/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conjunctive normal form: basic representation
-/
module

/-!
# Conjunctive normal form: basic representation

A `CNFClause` is a list of literals `(variable index, polarity)`; a `CNF`
formula is a list of clauses; `CNFSat` is satisfiability. Semantics and
restriction live in the neighbouring `Semantics` and `Restriction` modules.
The namespace is `Cslib.Logic.PL`; the pre-rename `Cslib.CookLevin` names
survive as `export` aliases in the legacy AutomatedReasoning shims and in
`Computability/CookLevin.lean`.
-/

@[expose] public section

namespace Cslib.Logic.PL

/-- A CNF clause: a list of literals `(variable index, polarity)`. -/
abbrev CNFClause := List (Nat × Bool)

/-- A CNF formula: a conjunction of clauses. -/
abbrev CNF := List CNFClause

/-- Boolean satisfiability of a CNF formula: some assignment satisfies every clause. -/
def CNFSat (φ : CNF) : Prop :=
  ∃ v : Nat → Bool, ∀ C ∈ φ, ∃ (x : Nat) (b : Bool), (x, b) ∈ C ∧ v x = b

end Cslib.Logic.PL
