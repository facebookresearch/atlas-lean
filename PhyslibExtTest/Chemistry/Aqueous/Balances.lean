/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Aqueous.Balances

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!

# Tests for aqueous balances and the proton condition

-/

@[expose] public section

open Matrix Chemistry.Aqueous

open scoped BigOperators

namespace PhyslibExtTest.Chemistry.Aqueous

/-!

## A. Acetic acid: charge plus mass balances imply the proton condition

Species `[HAc, Ac-, H3O+, OH-, H2O]`, component rows `[Ac, H]`, reference level
`{H2O, HAc}` with exhibited coefficients `(1, 0)`: the proton row is the charge
row.

-/

/-- Charges of `[HAc, Ac-, H3O+, OH-, H2O]`. -/
def aceticCharge : Fin 5 → ℤ := ![0, -1, 1, -1, 0]

/-- Component rows `[Ac, H]` for `[HAc, Ac-, H3O+, OH-, H2O]`. -/
def aceticB : Matrix (Fin 2) (Fin 5) ℚ :=
  ![![1, 1, 0, 0, 0], ![1, 0, 1, -1, 0]]

/-- Component totals `[Ac, H]`. -/
def aceticT : Fin 2 → ℝ := ![0.1, 0.1]

/-- Concentrations of `[HAc, Ac-, H3O+, OH-, H2O]`. -/
def aceticC : Fin 5 → ℝ := ![0.09, 0.01, 0.0101, 0.0001, 55.5]

lemma acetic_charge : ChargeBalanced aceticCharge aceticC := by
  simp only [ChargeBalanced, Fin.sum_univ_succ]
  simp [aceticCharge, aceticC]
  norm_num

lemma acetic_mass : MassBalanced aceticB aceticT aceticC := by
  intro k
  fin_cases k <;> simp only [Fin.sum_univ_succ] <;> simp [aceticB, aceticT, aceticC]
    <;> norm_num

/-- The proton condition holds with exhibited reference coefficients `(1, 0)`. -/
example : ∃ (a₀ : ℚ) (w : Fin 2 → ℚ),
    ProtonCondition (protonExcess aceticCharge aceticB a₀ w) aceticC :=
  ⟨1, 0, protonCondition_of_balances aceticCharge aceticB aceticT aceticC 1 0
    acetic_charge acetic_mass (by simp)⟩

/-- With coefficients `(1, 0)` the proton row is the charge row. -/
example : protonExcess aceticCharge aceticB 1 0 = fun i => (aceticCharge i : ℚ) := by
  funext i
  simp [protonExcess]

/-!

## B. Sodium acetate: nontrivial reference coefficients

Species `[Na+, HAc, Ac-, H3O+, OH-]`, component rows `[Ac, Na, H]`, reference
level `{H2O, Ac-, Na+}` with exhibited coefficients `(1, ![1, -1, 0])`: the
proton row is charge plus the Ac row minus the Na row.

-/

/-- Charges of `[Na+, HAc, Ac-, H3O+, OH-]`. -/
def naAcCharge : Fin 5 → ℤ := ![1, 0, -1, 1, -1]

/-- Component rows `[Ac, Na, H]` for `[Na+, HAc, Ac-, H3O+, OH-]`. -/
def naAcB : Matrix (Fin 3) (Fin 5) ℚ :=
  ![![0, 1, 1, 0, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 1, -1]]

/-- Component totals `[Ac, Na, H]`; the proton total is zero for the salt. -/
def naAcT : Fin 3 → ℝ := ![0.1, 0.1, 0]

/-- Concentrations of `[Na+, HAc, Ac-, H3O+, OH-]`. -/
def naAcC : Fin 5 → ℝ := ![0.1, 0.005, 0.095, 0.0001, 0.0051]

lemma naAc_charge : ChargeBalanced naAcCharge naAcC := by
  simp only [ChargeBalanced, Fin.sum_univ_succ]
  simp [naAcCharge, naAcC]
  norm_num

lemma naAc_mass : MassBalanced naAcB naAcT naAcC := by
  intro k
  fin_cases k <;> simp only [Fin.sum_univ_succ] <;> simp [naAcB, naAcT, naAcC]
    <;> norm_num

/-- The proton condition holds with exhibited coefficients `(1, ![1, -1, 0])`. -/
example : ∃ (a₀ : ℚ) (w : Fin 3 → ℚ),
    ProtonCondition (protonExcess naAcCharge naAcB a₀ w) naAcC :=
  ⟨1, ![1, -1, 0], protonCondition_of_balances naAcCharge naAcB naAcT naAcC 1
    ![1, -1, 0] naAc_charge naAc_mass (by
      simp only [Fin.sum_univ_succ]
      simp [naAcT] <;> norm_num)⟩

/-!

## C. Formation count: four species, two components, kernel dimension two

-/

/-- Two independent component rows over four species. -/
def countB : Matrix (Fin 2) (Fin 4) ℚ :=
  !![1, 0, 1, 0; 0, 1, 0, 1]

lemma countB_rank : countB.rank = 2 := by
  have hrange : LinearMap.range countB.mulVecLin = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rw [LinearMap.mem_range]
    refine ⟨![x 0, x 1, 0, 0], ?_⟩
    rw [Matrix.mulVecLin_apply]
    funext j
    fin_cases j <;> simp only [Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> simp [countB] <;> norm_num
  show Module.finrank ℚ (LinearMap.range countB.mulVecLin) = 2
  rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

/-- Four species and rank two give two independent formation reactions. -/
example : independentFormationCount countB = 2 := by
  rw [independentFormationCount_eq, countB_rank, Fintype.card_fin]

/-!

## D. Basis change: an invertible `P` preserves the solution set

-/

/-- An invertible change of component basis. -/
def changeP : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]

/-- A component matrix and totals. -/
def changeB : Matrix (Fin 2) (Fin 3) ℚ := !![1, 0, 1; 0, 1, 1]

def changeT : Fin 2 → ℚ := ![2, 3]

lemma changeP_unit : IsUnit changeP.det := by
  have hdet : changeP.det = 1 := by
    simp [changeP, Matrix.det_fin_two]
  rw [hdet]
  exact isUnit_one

/-- The solution set is the same before and after the basis change. -/
example : {c | changeB *ᵥ c = changeT}
    = {c | (changeP * changeB) *ᵥ c = changeP *ᵥ changeT} :=
  solutionSet_basisChange changeB changeT changeP changeP_unit

/-- A solution before the change is a solution after it. -/
example (c : Fin 3 → ℚ) (h : changeB *ᵥ c = changeT) :
    (changeP * changeB) *ᵥ c = changeP *ᵥ changeT := by
  have hset := solutionSet_basisChange changeB changeT changeP changeP_unit
  have hmem : c ∈ {c | changeB *ᵥ c = changeT} := h
  rw [hset] at hmem
  exact hmem

/-!

## E. A singular `P` collapses constraints

With `P = !![1, 0; 1, 0]`, `B` the identity and `T = ![0, 1]`, the original
system has the unique solution `![0, 1]` while the transformed system only
constrains the first coordinate.

-/

/-- A singular change of component basis. -/
def singP : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 1, 0]

def singB : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1]

def singT : Fin 2 → ℚ := ![0, 1]

/-- `singP` is singular. -/
example : singP.det = 0 := by
  simp [singP, Matrix.det_fin_two]

/-- The transformed constraint set is strictly larger. -/
example : {c | singB *ᵥ c = singT}
    ≠ {c | (singP * singB) *ᵥ c = singP *ᵥ singT} := by
  intro hcon
  have hmem : ![0, 5] ∈ {c | (singP * singB) *ᵥ c = singP *ᵥ singT} := by
    show (singP * singB) *ᵥ ![0, 5] = singP *ᵥ singT
    funext j
    fin_cases j <;> simp [Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_succ, singP, singB, singT] <;> norm_num
  rw [← hcon] at hmem
  have hmem' : singB *ᵥ ![0, 5] = singT := hmem
  have hcontra : (singB *ᵥ ![0, 5]) 1 = singT 1 := congrFun hmem' 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, singB, singT]
    at hcontra <;> norm_num at hcontra

/-!

## F. Omitting a spectator ion breaks charge balance

Species `[Na+, Cl-]`: the full charge sum vanishes, but the sum with the `Na+`
term omitted is nonzero.

-/

/-- Charges of `[Na+, Cl-]`. -/
def naclCharge : Fin 2 → ℤ := ![1, -1]

/-- Concentrations of `[Na+, Cl-]`. -/
def naclC : Fin 2 → ℝ := ![0.05, 0.05]

lemma nacl_charge : ChargeBalanced naclCharge naclC := by
  simp only [ChargeBalanced, Fin.sum_univ_succ]
  simp [naclCharge, naclC] <;> norm_num

/-- The charge sum with the `Na+` term omitted is nonzero. -/
example : (∑ i ∈ ({1} : Finset (Fin 2)), ((naclCharge i : ℤ):ℝ) * naclC i) ≠ 0 := by
  rw [Finset.sum_singleton]
  simp only [naclCharge, naclC, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Int.cast_neg, Int.cast_one]
  norm_num

/-!

## G. A formal solution can violate nonnegativity

The homogeneous balances do not enforce `0 ≤ c`: here both hold while one
concentration is negative.

-/

/-- A single component row coinciding with the charge row. -/
def negB : Matrix (Fin 1) (Fin 2) ℚ := !![1, -1]

/-- Concentrations with a negative entry satisfying both homogeneous balances. -/
def negC : Fin 2 → ℝ := ![-0.05, -0.05]

/-- Both homogeneous balances hold, yet `0 ≤ c` fails. -/
example : ChargeBalanced naclCharge negC ∧ HomMassBalanced negB negC
    ∧ ¬ ∀ i, 0 ≤ negC i := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [ChargeBalanced, Fin.sum_univ_succ]
    simp [naclCharge, negC] <;> norm_num
  · intro k
    fin_cases k
    simp only [Fin.sum_univ_succ]
    simp [negB, negC] <;> norm_num
  · intro hall
    have h0 := hall 0
    simp only [negC, Matrix.cons_val_zero] at h0
    norm_num at h0

end PhyslibExtTest.Chemistry.Aqueous

#print axioms Chemistry.Aqueous.ChargeBalanced
#print axioms Chemistry.Aqueous.MassBalanced
#print axioms Chemistry.Aqueous.HomMassBalanced
#print axioms Chemistry.Aqueous.ChargeBalanced.add
#print axioms Chemistry.Aqueous.ChargeBalanced.smul
#print axioms Chemistry.Aqueous.ChargeBalanced.zero
#print axioms Chemistry.Aqueous.HomMassBalanced.add
#print axioms Chemistry.Aqueous.HomMassBalanced.smul
#print axioms Chemistry.Aqueous.HomMassBalanced.zero
#print axioms Chemistry.Aqueous.MassBalanced.sub
#print axioms Chemistry.Aqueous.balances_add
#print axioms Chemistry.Aqueous.balances_smul
#print axioms Chemistry.Aqueous.protonExcess
#print axioms Chemistry.Aqueous.ProtonCondition
#print axioms Chemistry.Aqueous.protonCondition_of_balances
#print axioms Chemistry.Aqueous.independentFormationCount
#print axioms Chemistry.Aqueous.independentFormationCount_eq
#print axioms Chemistry.Aqueous.solutionSet_basisChange
#print axioms Chemistry.Aqueous.protonExcess_basisChange
#print axioms Chemistry.Aqueous.protonWeightTotal_basisChange
#print axioms Chemistry.Aqueous.protonSet_basisChange
