/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Restricting conjunctive normal forms
-/
module

public import Mathlib.Data.Finset.Card

public import CSLibExt.Logics.Propositional.CNF.Semantics

/-!
# Restricting conjunctive normal forms

Assigning a literal removes clauses made true by that assignment and removes
the assigned variable from all remaining clauses.  The main theorem states
that this simplification preserves satisfaction by every assignment extending
the selected literal.
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace CNFClause

/-- **Variables of a clause.** The variables of a CNF clause $C$ form the finite set of natural
numbers $x$ such that $C$ contains a literal $(x, b)$ for some polarity $b$. -/
def vars (clause : CNFClause) : Finset Nat :=
  (clause.map Prod.fst).toFinset

@[simp]
theorem mem_vars {x : Nat} {clause : CNFClause} :
    x ∈ clause.vars ↔ ∃ polarity, (x, polarity) ∈ clause := by
  simp [vars]

/-- **Restriction of a clause by a literal.** Given a literal $\ell = (x, b)$, the restriction
of a clause by $\ell$ is the clause obtained by deleting every literal whose variable is $x$, of
either polarity, keeping the other literals in order. -/
def restrict (literal : Nat × Bool) (clause : CNFClause) : CNFClause :=
  clause.filter fun candidate ↦ candidate.1 != literal.1

@[simp]
theorem mem_restrict {literal candidate : Nat × Bool} {clause : CNFClause} :
    candidate ∈ clause.restrict literal ↔
      candidate ∈ clause ∧ candidate.1 ≠ literal.1 := by
  simp [restrict]

theorem vars_restrict_subset (literal : Nat × Bool) (clause : CNFClause) :
    (clause.restrict literal).vars ⊆ clause.vars := by
  intro x hx
  obtain ⟨polarity, hmem⟩ := mem_vars.mp hx
  exact mem_vars.mpr ⟨polarity, (mem_restrict.mp hmem).1⟩

@[simp]
theorem fst_not_mem_vars_restrict (literal : Nat × Bool) (clause : CNFClause) :
    literal.1 ∉ (clause.restrict literal).vars := by
  intro hmem
  obtain ⟨polarity, hliteral⟩ := mem_vars.mp hmem
  exact (mem_restrict.mp hliteral).2 rfl

/-- **Satisfaction of a restricted clause.** Let $C$ be a clause, $\ell = (x, b)$ a literal that
does not occur in $C$, and $v$ an assignment of Booleans to variables with $v(x) = b$. Then $v$
satisfies the restriction of $C$ by $\ell$ if and only if $v$ satisfies $C$. -/
theorem satisfies_restrict_iff {assignment : Nat → Bool} {literal : Nat × Bool}
    {clause : CNFClause} (hassignment : assignment literal.1 = literal.2)
    (hnot_mem : literal ∉ clause) :
    (clause.restrict literal).Satisfies assignment ↔ clause.Satisfies assignment := by
  constructor
  · rintro ⟨candidate, hcandidate, hsatisfied⟩
    exact ⟨candidate, (mem_restrict.mp hcandidate).1, hsatisfied⟩
  · rintro ⟨candidate, hcandidate, hsatisfied⟩
    refine ⟨candidate, mem_restrict.mpr ⟨hcandidate, ?_⟩, hsatisfied⟩
    intro heq
    have hpolarity : candidate.2 = literal.2 := by
      calc
        candidate.2 = assignment candidate.1 := hsatisfied.symm
        _ = assignment literal.1 := by rw [heq]
        _ = literal.2 := hassignment
    apply hnot_mem
    have heq_literal : candidate = literal := Prod.ext heq hpolarity
    simpa [heq_literal] using hcandidate

end CNFClause

namespace CNF

/-- **Variables of a CNF formula.** The variables of a CNF formula $\varphi$ form the union of the
sets of variables of its clauses, that is, the finite set of natural numbers $x$ such that some
clause of $\varphi$ contains a literal $(x, b)$ for some polarity $b$. -/
def vars : CNF → Finset Nat
  | [] => ∅
  | clause :: formula => clause.vars ∪ vars formula

@[simp]
theorem vars_nil : CNF.vars [] = ∅ := by
  rfl

@[simp]
theorem vars_cons (clause : CNFClause) (formula : CNF) :
    CNF.vars (clause :: formula) = clause.vars ∪ formula.vars := by
  rfl

@[simp]
theorem mem_vars {x : Nat} {formula : CNF} :
    x ∈ formula.vars ↔ ∃ clause ∈ formula, ∃ polarity, (x, polarity) ∈ clause := by
  induction formula with
  | nil => simp
  | cons clause formula ih =>
      simp only [vars_cons, Finset.mem_union, CNFClause.mem_vars, ih, List.mem_cons]
      aesop

/-- **Restriction of a CNF formula by a literal.** Given a literal $\ell = (x, b)$, the
restriction of a CNF formula $\varphi$ by $\ell$ is obtained by deleting every clause of $\varphi$
that contains $\ell$ and replacing every other clause by its restriction by $\ell$, the clause
obtained by deleting every literal whose variable is $x$, of either polarity; the remaining
clauses keep their order.

The deleted clauses are true under every assignment that gives $x$ the value $b$. -/
def restrict (literal : Nat × Bool) : CNF → CNF
  | [] => []
  | clause :: formula =>
      if literal ∈ clause then
        restrict literal formula
      else
        clause.restrict literal :: restrict literal formula

@[simp]
theorem restrict_nil (literal : Nat × Bool) : CNF.restrict literal [] = [] := by
  rfl

@[simp]
theorem restrict_cons (literal : Nat × Bool) (clause : CNFClause) (formula : CNF) :
    CNF.restrict literal (clause :: formula) =
      if literal ∈ clause then
        CNF.restrict literal formula
      else
        clause.restrict literal :: CNF.restrict literal formula := by
  rfl

/-- **Restriction does not add variables.** For every CNF formula $\varphi$ and every literal
$\ell$, every variable of the restriction of $\varphi$ by $\ell$ is a variable of $\varphi$. -/
theorem vars_restrict_subset (literal : Nat × Bool) (formula : CNF) :
    (formula.restrict literal).vars ⊆ formula.vars := by
  induction formula with
  | nil => simp
  | cons clause formula ih =>
      rw [restrict_cons]
      split
      next =>
        intro x hx
        simp only [vars_cons, Finset.mem_union]
        exact Or.inr (ih hx)
      next =>
        intro x hx
        simp only [vars_cons, Finset.mem_union] at hx ⊢
        exact hx.elim (fun h ↦ Or.inl (CNFClause.vars_restrict_subset literal clause h))
          (fun h ↦ Or.inr (ih h))

/-- **The restricted variable no longer occurs.** For every CNF formula $F$ and every literal
$\ell = (x, b)$, the variable $x$ does not occur in the restriction of $F$ by $\ell$. -/
@[simp]
theorem not_mem_vars_restrict (literal : Nat × Bool) (formula : CNF) :
    literal.1 ∉ (formula.restrict literal).vars := by
  induction formula with
  | nil => simp
  | cons clause formula ih =>
      rw [restrict_cons]
      split
      next => exact ih
      next =>
        simp only [vars_cons, Finset.mem_union, not_or]
        exact ⟨CNFClause.fst_not_mem_vars_restrict literal clause, ih⟩

/-- **Restricting by an occurring variable shrinks the variable set.** Let $\varphi$ be a CNF
formula and $(x, b)$ a literal. If $x$ is a variable of $\varphi$, then the set of variables of
the restriction of $\varphi$ by $(x, b)$ is a proper subset of the set of variables of
$\varphi$. -/
theorem vars_restrict_ssubset {literal : Nat × Bool} {formula : CNF}
    (hmem : literal.1 ∈ formula.vars) :
    (formula.restrict literal).vars ⊂ formula.vars := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨vars_restrict_subset literal formula, ?_⟩
  intro heq
  apply not_mem_vars_restrict literal formula
  rw [heq]
  exact hmem

/-- **Restriction reduces the number of variables.** Let $F$ be a CNF formula and let
$\ell = (x, b)$ be a literal whose variable $x$ occurs in $F$. Then the restriction of $F$
by $\ell$ has strictly fewer distinct variables than $F$. -/
theorem card_vars_restrict_lt {literal : Nat × Bool} {formula : CNF}
    (hmem : literal.1 ∈ formula.vars) :
    (formula.restrict literal).vars.card < formula.vars.card :=
  Finset.card_lt_card (vars_restrict_ssubset hmem)

/-- **Satisfaction of a restricted CNF formula.** Let $\varphi$ be a CNF formula, $\ell = (x, b)$
a literal, and $v$ an assignment of Booleans to variables with $v(x) = b$. Then $v$ satisfies the
restriction of $\varphi$ by $\ell$ if and only if $v$ satisfies $\varphi$. -/
theorem satisfies_restrict_iff {assignment : Nat → Bool} {literal : Nat × Bool}
    {formula : CNF} (hassignment : assignment literal.1 = literal.2) :
    (formula.restrict literal).Satisfies assignment ↔ formula.Satisfies assignment := by
  induction formula with
  | nil => simp
  | cons clause formula ih =>
      rw [restrict_cons]
      split
      next hmem =>
        rw [CNF.satisfies_cons (assignment := assignment) (clause := clause)
          (formula := formula)]
        rw [ih]
        constructor
        · intro hformula
          exact ⟨⟨literal, hmem, hassignment⟩, hformula⟩
        · exact And.right
      next hmem =>
        rw [CNF.satisfies_cons (assignment := assignment)
          (clause := clause.restrict literal) (formula := CNF.restrict literal formula)]
        rw [CNF.satisfies_cons (assignment := assignment) (clause := clause)
          (formula := formula)]
        rw [CNFClause.satisfies_restrict_iff hassignment hmem, ih]

/-- **Satisfaction depends only on the occurring variables.** Let $F$ be a CNF formula and let
$v_1, v_2$ be assignments of Booleans to variables with $v_1(x) = v_2(x)$ for every variable $x$
occurring in $F$. If $v_1$ satisfies $F$, then $v_2$ satisfies $F$. -/
theorem satisfies_congr {formula : CNF} {assignment₁ assignment₂ : Nat → Bool}
    (hagrees : ∀ x ∈ formula.vars, assignment₁ x = assignment₂ x)
    (hsatisfies : formula.Satisfies assignment₁) :
    formula.Satisfies assignment₂ := by
  intro clause hclause
  obtain ⟨⟨x, polarity⟩, hliteral, heq⟩ := hsatisfies clause hclause
  refine ⟨(x, polarity), hliteral, ?_⟩
  change assignment₂ x = polarity
  change assignment₁ x = polarity at heq
  rw [← heq]
  exact (hagrees x (mem_vars.mpr ⟨clause, hclause, polarity, hliteral⟩)).symm

/-- **Lifting a satisfying assignment from a restriction.** Let $F$ be a CNF formula,
$\ell = (x, b)$ a literal and $v$ an assignment of Booleans to variables. If $v$ satisfies the
restriction of $F$ by $\ell$, then the assignment that agrees with $v$ except that it sends $x$
to $b$ satisfies $F$. -/
theorem satisfies_of_satisfies_restrict {formula : CNF} {assignment : Nat → Bool}
    {literal : Nat × Bool} (hsatisfies : (formula.restrict literal).Satisfies assignment) :
    formula.Satisfies (Function.update assignment literal.1 literal.2) := by
  have hagrees : ∀ x ∈ (formula.restrict literal).vars,
      assignment x = Function.update assignment literal.1 literal.2 x := by
    intro x hx
    have hne : x ≠ literal.1 := by
      intro heq
      subst x
      exact not_mem_vars_restrict literal formula hx
    simp [Function.update, hne]
  have hrestricted := satisfies_congr hagrees hsatisfies
  apply (satisfies_restrict_iff (literal := literal) (formula := formula)
    (assignment := Function.update assignment literal.1 literal.2) (by simp)).mp
  exact hrestricted

/-- **Splitting on a variable.** For every CNF formula $F$ and every variable $x$, the formula
$F$ is satisfiable if and only if the restriction of $F$ by the literal $(x, \mathrm{true})$ is
satisfiable or the restriction of $F$ by the literal $(x, \mathrm{false})$ is satisfiable. -/
theorem sat_iff_restrict_true_or_false (formula : CNF) (x : Nat) :
    CNFSat formula ↔
      CNFSat (formula.restrict (x, true)) ∨ CNFSat (formula.restrict (x, false)) := by
  rw [cnfSat_iff_exists_satisfies, cnfSat_iff_exists_satisfies,
    cnfSat_iff_exists_satisfies]
  constructor
  · rintro ⟨assignment, hsatisfies⟩
    cases hvalue : assignment x with
    | false =>
        exact Or.inr ⟨assignment,
          (satisfies_restrict_iff (literal := (x, false)) hvalue).mpr hsatisfies⟩
    | true =>
        exact Or.inl ⟨assignment,
          (satisfies_restrict_iff (literal := (x, true)) hvalue).mpr hsatisfies⟩
  · rintro (⟨assignment, hsatisfies⟩ | ⟨assignment, hsatisfies⟩)
    · exact ⟨Function.update assignment x true,
        satisfies_of_satisfies_restrict hsatisfies⟩
    · exact ⟨Function.update assignment x false,
        satisfies_of_satisfies_restrict hsatisfies⟩

/-- **Unit propagation preserves satisfiability.** Let $F$ be a CNF formula that contains the
unit clause whose only literal is $\ell$. Then $F$ is satisfiable if and only if the restriction
of $F$ by $\ell$ is satisfiable. -/
theorem sat_iff_restrict_of_unit {formula : CNF} {literal : Nat × Bool}
    (hunit : [literal] ∈ formula) :
    CNFSat formula ↔ CNFSat (formula.restrict literal) := by
  rw [cnfSat_iff_exists_satisfies, cnfSat_iff_exists_satisfies]
  constructor
  · rintro ⟨assignment, hsatisfies⟩
    have hclause := hsatisfies [literal] hunit
    have hliteral : assignment literal.1 = literal.2 := by
      simpa using hclause
    exact ⟨assignment, (satisfies_restrict_iff hliteral).mpr hsatisfies⟩
  · rintro ⟨assignment, hsatisfies⟩
    exact ⟨Function.update assignment literal.1 literal.2,
      satisfies_of_satisfies_restrict hsatisfies⟩


end CNF

end Cslib.Logic.PL
