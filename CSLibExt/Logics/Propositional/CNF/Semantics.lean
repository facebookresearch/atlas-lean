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

/-- A literal is satisfied when the assignment gives its variable its recorded polarity. -/
def Satisfies (assignment : Nat → Bool) (literal : Nat × Bool) : Prop :=
  assignment literal.1 = literal.2

@[simp]
theorem satisfies_def {assignment : Nat → Bool} {literal : Nat × Bool} :
    CNFLiteral.Satisfies assignment literal ↔ assignment literal.1 = literal.2 := by
  rfl

end CNFLiteral

namespace CNFClause

/-- A clause is satisfied when at least one of its literals is satisfied. -/
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

/-- A CNF formula is satisfied when each of its clauses is satisfied. -/
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

/-- The named CNF semantics coincides with the pre-existing satisfiability predicate. -/
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
