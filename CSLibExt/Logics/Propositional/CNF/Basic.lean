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

/-- **CNF clause.** A CNF clause is a finite list of literals, each a pair $(x, b)$ of a variable
index $x \in \mathbb{N}$ and a polarity $b \in \{\mathrm{true}, \mathrm{false}\}$. -/
abbrev CNFClause := List (Nat × Bool)

/-- **CNF formula.** A CNF formula is a finite list of CNF clauses, read as the conjunction of its
clauses. -/
abbrev CNF := List CNFClause

/-- **Satisfiability of a CNF formula.** A CNF formula $\varphi$ is satisfiable when there is an
assignment $v : \mathbb{N} \to \{\mathrm{true}, \mathrm{false}\}$ such that every clause $C$ of
$\varphi$ contains a literal $(x, b)$ with $v(x) = b$. -/
def CNFSat (φ : CNF) : Prop :=
  ∃ v : Nat → Bool, ∀ C ∈ φ, ∃ (x : Nat) (b : Bool), (x, b) ∈ C ∧ v x = b

end Cslib.Logic.PL
