/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Correctness of the DPLL solver
-/
module

public import CSLibExt.Algorithms.SAT.DPLL.Solver

/-!
# Correctness of the DPLL solver

The main theorem proves that the executable Boolean DPLL procedure accepts
exactly the satisfiable formulas represented by `Cslib.Logic.PL.CNFSat`.
-/

@[expose] public section


namespace Cslib.Algorithms.SAT.DPLL

open Cslib.Logic.PL

theorem firstUnit_eq_some_mem {formula : CNF} {literal : Nat × Bool}
    (hunit : firstUnit formula = some literal) : [literal] ∈ formula := by
  induction formula with
  | nil => simp [firstUnit] at hunit
  | cons clause formula ih =>
      cases clause with
      | nil =>
          exact List.mem_cons_of_mem [] (ih hunit)
      | cons head tail =>
          cases tail with
          | nil =>
              simp only [firstUnit, Option.some.injEq] at hunit
              subst head
              simp
          | cons next rest =>
              exact List.mem_cons_of_mem _ (ih hunit)

theorem firstVariable_eq_some_mem_vars {formula : CNF} {x : Nat}
    (hfirst : firstVariable formula = some x) : x ∈ formula.vars := by
  induction formula with
  | nil => simp [firstVariable] at hfirst
  | cons clause formula ih =>
      cases clause with
      | nil =>
          simp only [CNF.vars_cons, Finset.mem_union]
          exact Or.inr (ih hfirst)
      | cons literal clause =>
          simp only [firstVariable, Option.some.injEq] at hfirst
          subst x
          simp only [CNF.vars_cons, Finset.mem_union, CNFClause.mem_vars]
          exact Or.inl ⟨literal.2, by simp⟩

theorem firstVariable_eq_none_all_empty {formula : CNF}
    (hfirst : firstVariable formula = none) : ∀ clause ∈ formula, clause = [] := by
  induction formula with
  | nil => simp
  | cons clause formula ih =>
      cases clause with
      | nil =>
          intro candidate hcandidate
          rcases List.mem_cons.mp hcandidate with rfl | htail
          · rfl
          · exact ih hfirst candidate htail
      | cons literal clause => simp [firstVariable] at hfirst

@[simp]
theorem any_isEmpty_eq_true_iff {formula : CNF} :
    formula.any List.isEmpty = true ↔ [] ∈ formula := by
  simp [List.any_eq_true, List.isEmpty_iff]

theorem not_sat_of_mem_empty {formula : CNF} (hempty : [] ∈ formula) :
    ¬CNFSat formula := by
  rw [cnfSat_iff_exists_satisfies]
  rintro ⟨assignment, hsatisfies⟩
  have := hsatisfies [] hempty
  simp at this

/-- DPLL is correct whenever its fuel covers every variable still present in
the formula.  This stronger statement is the induction invariant behind the
public solver theorem. -/
theorem decideWithFuel_eq_true_iff {fuel : Nat} {formula : CNF}
    (hfuel : formula.vars.card ≤ fuel) :
    decideWithFuel fuel formula = true ↔ CNFSat formula := by
  induction fuel generalizing formula with
  | zero =>
      have hcard : formula.vars.card = 0 := Nat.eq_zero_of_le_zero hfuel
      have hvars : formula.vars = ∅ := Finset.card_eq_zero.mp hcard
      cases hformula : formula with
      | nil => simp [decideWithFuel, CNFSat]
      | cons clause tail =>
          have hfirst : firstVariable formula = none := by
            cases hresult : firstVariable formula with
            | none => rfl
            | some x =>
                have hx := firstVariable_eq_some_mem_vars hresult
                rw [hvars] at hx
                simp at hx
          have hall := firstVariable_eq_none_all_empty hfirst
          have hclause : clause = [] := hall clause (by simp [hformula])
          subst clause
          simp [decideWithFuel, CNFSat]
  | succ fuel ih =>
      by_cases hempty : formula.isEmpty = true
      · have hformula : formula = [] := List.isEmpty_iff.mp hempty
        subst formula
        simp [decideWithFuel, CNFSat]
      · by_cases hbad : formula.any List.isEmpty = true
        · have hnot_sat := not_sat_of_mem_empty (any_isEmpty_eq_true_iff.mp hbad)
          have hdecide : decideWithFuel (fuel + 1) formula = false := by
            simp [decideWithFuel, hempty, hbad]
          rw [hdecide]
          simp only [Bool.false_eq_true, false_iff]
          exact hnot_sat
        · cases hunit : firstUnit formula with
          | some literal =>
              have hunit_mem := firstUnit_eq_some_mem hunit
              have hvar_mem : literal.1 ∈ formula.vars :=
                CNF.mem_vars.mpr ⟨[literal], hunit_mem, literal.2, by simp⟩
              have hlt := CNF.card_vars_restrict_lt
                (literal := literal) (formula := formula) hvar_mem
              have hrecursive : (formula.restrict literal).vars.card ≤ fuel :=
                Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hfuel)
              have hdecide : decideWithFuel (fuel + 1) formula =
                  decideWithFuel fuel (formula.restrict literal) := by
                simp [decideWithFuel, hempty, hbad, hunit]
              rw [hdecide, ih hrecursive]
              exact (CNF.sat_iff_restrict_of_unit hunit_mem).symm
          | none =>
              cases hfirst : firstVariable formula with
              | none =>
                  have hall := firstVariable_eq_none_all_empty hfirst
                  have hformula_ne : formula ≠ [] := by
                    intro heq
                    subst formula
                    simp at hempty
                  obtain ⟨clause, hclause⟩ := List.exists_mem_of_ne_nil formula hformula_ne
                  have : clause = [] := hall clause hclause
                  subst clause
                  exact (hbad (any_isEmpty_eq_true_iff.mpr hclause)).elim
              | some x =>
                  have hx := firstVariable_eq_some_mem_vars hfirst
                  have htrue_lt := CNF.card_vars_restrict_lt
                    (literal := (x, true)) (formula := formula) hx
                  have hfalse_lt := CNF.card_vars_restrict_lt
                    (literal := (x, false)) (formula := formula) hx
                  have htrue_fuel : (formula.restrict (x, true)).vars.card ≤ fuel :=
                    Nat.lt_succ_iff.mp (lt_of_lt_of_le htrue_lt hfuel)
                  have hfalse_fuel : (formula.restrict (x, false)).vars.card ≤ fuel :=
                    Nat.lt_succ_iff.mp (lt_of_lt_of_le hfalse_lt hfuel)
                  have hdecide : decideWithFuel (fuel + 1) formula =
                      (decideWithFuel fuel (formula.restrict (x, true)) ||
                        decideWithFuel fuel (formula.restrict (x, false))) := by
                    simp [decideWithFuel, hempty, hbad, hunit, hfirst]
                  rw [hdecide, Bool.or_eq_true, ih htrue_fuel, ih hfalse_fuel]
                  exact (CNF.sat_iff_restrict_true_or_false formula x).symm

/-- The executable DPLL procedure accepts exactly the satisfiable CNF formulas. -/
theorem dpll_eq_true_iff {formula : CNF} :
    dpll formula = true ↔ CNFSat formula := by
  apply decideWithFuel_eq_true_iff
  exact le_rfl

end Cslib.Algorithms.SAT.DPLL
