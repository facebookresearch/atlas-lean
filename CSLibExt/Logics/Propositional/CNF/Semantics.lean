/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Semantics of conjunctive normal form
-/
module

public import CSLibExt.Logics.Propositional.CNF.Basic

/-!
# Semantics of conjunctive normal form

This file gives names to the literal, clause, and formula semantics implicit in
`Cslib.Logic.PL.CNFSat`.  The definitions deliberately use the existing CNF
representation, so verified decision procedures can operate directly on the
formulas used by the Cook--Levin development.
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace CNFLiteral

/-- **Satisfaction of a literal.** An assignment $v : \mathbb{N} \to \{\mathrm{true},
\mathrm{false}\}$ satisfies a literal $(x, b)$, with variable $x \in \mathbb{N}$ and polarity
$b \in \{\mathrm{true}, \mathrm{false}\}$, when $v(x) = b$. -/
def Satisfies (assignment : Nat → Bool) (literal : Nat × Bool) : Prop :=
  assignment literal.1 = literal.2

@[simp]
theorem satisfies_def {assignment : Nat → Bool} {literal : Nat × Bool} :
    CNFLiteral.Satisfies assignment literal ↔ assignment literal.1 = literal.2 := by
  rfl

end CNFLiteral

namespace CNFClause

/-- **Satisfaction of a clause.** An assignment $v : \mathbb{N} \to \{\mathrm{true},
\mathrm{false}\}$ satisfies a CNF clause $C$ when at least one literal of $C$ is satisfied by $v$,
that is, $C$ contains a literal $(x, b)$ with $v(x) = b$. -/
def Satisfies (assignment : Nat → Bool) (clause : CNFClause) : Prop :=
  ∃ literal ∈ clause, CNFLiteral.Satisfies assignment literal

@[simp]
theorem satisfies_def {assignment : Nat → Bool} {clause : CNFClause} :
    clause.Satisfies assignment ↔
      ∃ literal ∈ clause, assignment literal.1 = literal.2 := by
  rfl

@[simp]
theorem satisfies_nil (assignment : Nat → Bool) :
    CNFClause.Satisfies assignment [] ↔ False := by
  simp [Satisfies]

@[simp]
theorem satisfies_cons {assignment : Nat → Bool} {literal : Nat × Bool}
    {clause : CNFClause} :
    CNFClause.Satisfies assignment (literal :: clause) ↔
      CNFLiteral.Satisfies assignment literal ∨ clause.Satisfies assignment := by
  simp [Satisfies]

end CNFClause

namespace CNF

/-- **Satisfaction of a CNF formula.** An assignment $v : \mathbb{N} \to \{\mathrm{true},
\mathrm{false}\}$ satisfies a CNF formula $\varphi$ when $v$ satisfies every clause of $\varphi$. -/
def Satisfies (assignment : Nat → Bool) (formula : CNF) : Prop :=
  ∀ clause ∈ formula, CNFClause.Satisfies assignment clause

@[simp]
theorem satisfies_def {assignment : Nat → Bool} {formula : CNF} :
    formula.Satisfies assignment ↔
      ∀ clause ∈ formula, CNFClause.Satisfies assignment clause := by
  rfl

@[simp]
theorem satisfies_nil (assignment : Nat → Bool) :
    CNF.Satisfies assignment [] := by
  simp [Satisfies]

@[simp]
theorem satisfies_cons {assignment : Nat → Bool} {clause : CNFClause} {formula : CNF} :
    CNF.Satisfies assignment (clause :: formula) ↔
      clause.Satisfies assignment ∧ formula.Satisfies assignment := by
  simp [Satisfies]

theorem satisfies_append {assignment : Nat → Bool} {φ ψ : CNF} :
    (φ ++ ψ).Satisfies assignment ↔ φ.Satisfies assignment ∧ ψ.Satisfies assignment := by
  simp only [Satisfies, List.mem_append, or_imp, forall_and]

end CNF

/-- **Satisfiability means having a satisfying assignment.** A CNF formula $\varphi$ is
satisfiable if and only if there is an assignment $v : \mathbb{N} \to \{\mathrm{true},
\mathrm{false}\}$ that satisfies $\varphi$. -/
theorem cnfSat_iff_exists_satisfies {formula : CNF} :
    CNFSat formula ↔ ∃ assignment, formula.Satisfies assignment := by
  constructor
  · rintro ⟨assignment, hformula⟩
    refine ⟨assignment, ?_⟩
    intro clause hclause
    obtain ⟨x, polarity, hliteral, hsatisfied⟩ := hformula clause hclause
    exact ⟨(x, polarity), hliteral, hsatisfied⟩
  · rintro ⟨assignment, hformula⟩
    refine ⟨assignment, ?_⟩
    intro clause hclause
    obtain ⟨⟨x, polarity⟩, hliteral, hsatisfied⟩ := hformula clause hclause
    exact ⟨x, polarity, hliteral, hsatisfied⟩

end Cslib.Logic.PL
