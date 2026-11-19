/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Aqueous.Balances

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!

# Tests for aqueous balances and the proton condition

The concentrations below satisfy the balances; they are not computed from equilibrium
constants.

-/

@[expose] public section

open Matrix Chemistry.Aqueous

open scoped BigOperators

namespace PhyslibExtTest.Chemistry.Aqueous

/-!

## A. Charge and mass balances

Acetic acid has species `[HAc, Ac-, H3O+, OH-, H2O]` and component rows `[Ac, H]`; sodium
acetate has species `[Na+, HAc, Ac-, H3O+, OH-, H2O]` and component rows `[Ac, Na, H]`. The
`H` rows count protons relative to `Ac-` and `H2O`.

-/

/-- Charges of `[HAc, Ac-, H3O+, OH-, H2O]`. -/
def aceticCharge : Fin 5 → ℤ := ![0, -1, 1, -1, 0]

/-- Component rows `[Ac, H]` for `[HAc, Ac-, H3O+, OH-, H2O]`. -/
def aceticB : Matrix (Fin 2) (Fin 5) ℚ :=
  ![![1, 1, 0, 0, 0], ![1, 0, 1, -1, 0]]

/-- Component totals `[Ac, H]` of `0.1` M acetic acid. -/
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

/-- Charges of `[Na+, HAc, Ac-, H3O+, OH-, H2O]`. -/
def naAcCharge : Fin 6 → ℤ := ![1, 0, -1, 1, -1, 0]

/-- Component rows `[Ac, Na, H]` for `[Na+, HAc, Ac-, H3O+, OH-, H2O]`. -/
def naAcB : Matrix (Fin 3) (Fin 6) ℚ :=
  ![![0, 1, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, -1, 0]]

/-- Component totals `[Ac, Na, H]` of `0.1` M sodium acetate. -/
def naAcT : Fin 3 → ℝ := ![0.1, 0.1, 0]

/-- Concentrations of `[Na+, HAc, Ac-, H3O+, OH-, H2O]`. -/
def naAcC : Fin 6 → ℝ := ![0.1, 0.005, 0.095, 0.0001, 0.0051, 55.5]

lemma naAc_charge : ChargeBalanced naAcCharge naAcC := by
  simp only [ChargeBalanced, Fin.sum_univ_succ]
  simp [naAcCharge, naAcC]
  norm_num

lemma naAc_mass : MassBalanced naAcB naAcT naAcC := by
  intro k
  fin_cases k <;> simp only [Fin.sum_univ_succ] <;> simp [naAcB, naAcT, naAcC]
    <;> norm_num

/-- Charges of `[Na+, Cl-]`. -/
def naclCharge : Fin 2 → ℤ := ![1, -1]

/-- Concentrations of `[Na+, Cl-]`. -/
def naclC : Fin 2 → ℝ := ![0.05, 0.05]

lemma nacl_charge : ChargeBalanced naclCharge naclC := by
  simp only [ChargeBalanced, Fin.sum_univ_succ]
  simp [naclCharge, naclC]

/-- Omitting the spectator `Na+` from the charge sum makes it nonzero. -/
example : (∑ i ∈ ({1} : Finset (Fin 2)), ((naclCharge i : ℤ) : ℝ) * naclC i) ≠ 0 := by
  rw [Finset.sum_singleton]
  simp only [naclCharge, naclC, Matrix.cons_val_one]
  norm_num

/-!

## B. Linearity in the concentrations

The homogeneous balances do not enforce `0 ≤ c`: here both hold while one concentration is
negative.

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
    simp [naclCharge, negC]
  · intro k
    fin_cases k
    simp only [Fin.sum_univ_succ]
    simp [negB, negC]
  · intro hall
    have h0 := hall 0
    simp only [negC, Matrix.cons_val_zero] at h0
    norm_num at h0

/-- The difference of two solutions of the mass balances solves the homogeneous system. -/
example : HomMassBalanced aceticB (aceticC - aceticC) :=
  acetic_mass.sub acetic_mass

/-!

## C. The proton condition

-/

/-- The reference level `{HAc, H2O}` for acetic acid: the proton excess is the charge. -/
def aceticRef : ProtonReferenceLevel aceticCharge aceticB where
  w := 0
  zeroLevel := {0, 4}
  water := 4
  hydronium := 2
  hydroxide := 3
  charge_water := by decide
  charge_hydronium := by decide
  charge_hydroxide := by decide
  water_mem_zeroLevel := by simp
  balanceCombination_eq_zero := by
    intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl <;> simp [balanceCombination, aceticCharge]
  balanceCombination_hydronium := by simp [balanceCombination, aceticCharge]
  balanceCombination_hydroxide := by simp [balanceCombination, aceticCharge]

/-- The proton row of `aceticRef` is the charge row. -/
example : aceticRef.protonExcess = fun i => (aceticCharge i : ℚ) := by
  funext i
  simp [ProtonReferenceLevel.protonExcess, balanceCombination, aceticRef]

/-- Charge and mass balances imply the proton condition for acetic acid. -/
example : aceticRef.ProtonCondition aceticC :=
  aceticRef.protonCondition_of_balances acetic_charge acetic_mass (by simp [aceticRef])

/-- The recipe of `0.1` M acetic acid: zero-level species only. -/
def aceticRecipe : Fin 5 → ℝ := ![0.1, 0, 0, 0, 55.5]

/-- The proton condition follows from the recipe. -/
example : aceticRef.ProtonCondition aceticC :=
  aceticRef.protonCondition_of_recipe (n₀ := aceticRecipe) acetic_charge acetic_mass
    (by simp only [ChargeBalanced, Fin.sum_univ_succ]; simp [aceticCharge, aceticRecipe])
    (by
      intro k
      fin_cases k <;> simp only [Fin.sum_univ_succ] <;> simp [aceticB, aceticT, aceticRecipe])
    (by intro i hi; fin_cases i <;> simp_all [aceticRef, aceticRecipe])

/-- For acetic acid the proton condition reads `[H3O+] = [Ac-] + [OH-]`. -/
example (c : Fin 5 → ℝ) : aceticRef.ProtonCondition c ↔ c 2 = c 1 + c 3 := by
  simp only [ProtonReferenceLevel.ProtonCondition, ProtonReferenceLevel.protonExcess,
    balanceCombination, Fin.sum_univ_succ]
  simp [aceticRef, aceticCharge]
  constructor <;> intro h <;> linarith

/-- The textbook form of the proton condition holds for the acetic-acid concentrations. -/
example : ∑ i ∈ Finset.univ.filter (fun i => 0 < aceticRef.protonExcess i),
      (aceticRef.protonExcess i : ℝ) * aceticC i =
    ∑ i ∈ Finset.univ.filter (fun i => aceticRef.protonExcess i < 0),
      -(aceticRef.protonExcess i : ℝ) * aceticC i :=
  (aceticRef.protonCondition_iff aceticC).1
    (aceticRef.protonCondition_of_balances acetic_charge acetic_mass (by simp [aceticRef]))

/-- The proton condition constrains the concentrations: hydronium alone violates it. -/
example : ¬ aceticRef.ProtonCondition (Pi.single 2 1) :=
  aceticRef.not_protonCondition_single_hydronium

/-- The reference level `{Na+, Ac-, H2O}` for sodium acetate: the proton excess is the charge
plus the `Ac` row minus the `Na` row. -/
def naAcRef : ProtonReferenceLevel naAcCharge naAcB where
  w := ![1, -1, 0]
  zeroLevel := {0, 2, 5}
  water := 5
  hydronium := 3
  hydroxide := 4
  charge_water := by decide
  charge_hydronium := by decide
  charge_hydroxide := by decide
  water_mem_zeroLevel := by simp
  balanceCombination_eq_zero := by
    intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl | rfl <;>
      simp [balanceCombination, naAcCharge, naAcB, Fin.sum_univ_succ]
  balanceCombination_hydronium := by
    simp [balanceCombination, naAcCharge, naAcB, Fin.sum_univ_succ]
  balanceCombination_hydroxide := by
    simp [balanceCombination, naAcCharge, naAcB, Fin.sum_univ_succ]

/-- Charge and mass balances imply the proton condition for sodium acetate. -/
example : naAcRef.ProtonCondition naAcC :=
  naAcRef.protonCondition_of_balances naAc_charge naAc_mass (by
    norm_num [naAcRef, naAcT, Fin.sum_univ_succ])

/-- The recipe of `0.1` M sodium acetate: zero-level species only. -/
def naAcRecipe : Fin 6 → ℝ := ![0.1, 0, 0.1, 0, 0, 55.5]

/-- The proton condition follows from the recipe. -/
example : naAcRef.ProtonCondition naAcC :=
  naAcRef.protonCondition_of_recipe (n₀ := naAcRecipe) naAc_charge naAc_mass
    (by simp only [ChargeBalanced, Fin.sum_univ_succ]; simp [naAcCharge, naAcRecipe])
    (by
      intro k
      fin_cases k <;> simp only [Fin.sum_univ_succ] <;> simp [naAcB, naAcT, naAcRecipe])
    (by intro i hi; fin_cases i <;> simp_all [naAcRef, naAcRecipe])

/-- `HAc` is the zero-level `Ac-` plus one proton, so its proton excess is `1`. -/
example : naAcRef.protonExcess 1 = 1 :=
  naAcRef.protonExcess_eq_of_content (Pi.single 2 1) 1
    (by intro j hj; fin_cases j <;> simp_all [naAcRef])
    (by simp [naAcRef, naAcCharge, Fin.sum_univ_succ])
    (by intro k; fin_cases k <;> simp [naAcRef, naAcB, Fin.sum_univ_succ])

/-- For sodium acetate the proton condition reads `[H3O+] + [HAc] = [OH-]`. -/
example (c : Fin 6 → ℝ) : naAcRef.ProtonCondition c ↔ c 3 + c 1 = c 4 := by
  simp only [ProtonReferenceLevel.ProtonCondition, ProtonReferenceLevel.protonExcess,
    balanceCombination, Fin.sum_univ_succ]
  simp [naAcRef, naAcCharge, naAcB]
  constructor <;> intro h <;> linarith

/-!

## D. The formation-equilibrium count

-/

/-- Two independent component rows over four species. -/
def countB : Matrix (Fin 2) (Fin 4) ℚ :=
  !![1, 0, 1, 0; 0, 1, 0, 1]

/-- Charges equal to the first component row minus the second. -/
def countCharge : Fin 4 → ℤ := ![1, -1, 1, -1]

lemma countB_rank : countB.rank = 2 := by
  have hrange : LinearMap.range countB.mulVecLin = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rw [LinearMap.mem_range]
    refine ⟨![x 0, x 1, 0, 0], ?_⟩
    rw [Matrix.mulVecLin_apply]
    funext j
    fin_cases j <;> simp only [Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> simp [countB]
  change Module.finrank ℚ (LinearMap.range countB.mulVecLin) = 2
  rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

/-- Four species, rank two, and charges carried by the components (`zc = ![1, -1]`) give two
independent formation reactions. -/
lemma countB_formationCount : independentFormationCount countCharge countB = 2 := by
  rw [independentFormationCount_eq_of_charge_eq countCharge countB ![1, -1] (by
    intro i
    fin_cases i <;> simp [countCharge, countB, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]),
    countB_rank, Fintype.card_fin]

/-- Charges of a cation and an anion, `[M+, X-]`. -/
def ionCharge : Fin 2 → ℤ := ![1, -1]

/-- A zero component matrix over the two ions. -/
def ionB : Matrix (Fin 1) (Fin 2) ℚ := 0

/-- The kernel of the zero component matrix alone is two-dimensional. -/
example : Module.finrank ℚ (LinearMap.ker ionB.mulVecLin) = 2 := by
  rw [ionB, Matrix.mulVecLin_zero, LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun]

/-- Charge conservation leaves one formation reaction, along `![1, 1]`. -/
example : independentFormationCount ionCharge ionB = 1 := by
  have hker : LinearMap.ker (balanceMatrix ionCharge ionB).mulVecLin =
      Submodule.span ℚ {![1, 1]} := by
    ext ν
    rw [mem_ker_balanceMatrix_iff, isBalanced_balanceMatrix_iff, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨h1, -⟩
      refine ⟨ν 0, ?_⟩
      simp [Fin.sum_univ_succ, ionCharge] at h1
      funext j
      fin_cases j
      · simp
      · simp
        linarith
    · rintro ⟨a, rfl⟩
      exact ⟨by simp [Fin.sum_univ_succ, ionCharge], by simp [ionB]⟩
  rw [independentFormationCount, hker, finrank_span_singleton]
  intro h
  have h0 := congrFun h 0
  simp at h0

/-- Creating a lone cation conserves every (zero) component row but not charge. -/
example : ionB *ᵥ ![1, 0] = 0 ∧
    ¬ _root_.Chemistry.Stoichiometry.IsBalanced (balanceMatrix ionCharge ionB) ![1, 0] := by
  refine ⟨by simp [ionB], ?_⟩
  rw [isBalanced_balanceMatrix_iff]
  rintro ⟨h, -⟩
  simp [Fin.sum_univ_succ, ionCharge] at h

/-- The acid dissociation `HAc + H2O → H3O+ + Ac-` conserves charge and both components. -/
example : _root_.Chemistry.Stoichiometry.IsBalanced (balanceMatrix aceticCharge aceticB)
    ![-1, 1, 1, 0, -1] := by
  rw [isBalanced_balanceMatrix_iff]
  refine ⟨by simp [Fin.sum_univ_succ, aceticCharge], ?_⟩
  funext k
  fin_cases k <;> simp [aceticB, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The same reaction, read as real concentrations, satisfies both homogeneous balances. -/
example : ChargeBalanced aceticCharge (fun i => ((![-1, 1, 1, 0, -1] : Fin 5 → ℚ) i : ℝ)) ∧
    HomMassBalanced aceticB (fun i => ((![-1, 1, 1, 0, -1] : Fin 5 → ℚ) i : ℝ)) := by
  rw [← isBalanced_balanceMatrix_iff_balances, isBalanced_balanceMatrix_iff]
  refine ⟨by simp [Fin.sum_univ_succ, aceticCharge], ?_⟩
  funext k
  fin_cases k <;> simp [aceticB, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-!

## E. Change of component basis

-/

/-- An invertible change of component basis. -/
def changeP : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]

/-- A component matrix. -/
def changeB : Matrix (Fin 2) (Fin 3) ℚ := !![1, 0, 1; 0, 1, 1]

/-- Real component totals. -/
def changeT : Fin 2 → ℝ := ![2, 3]

lemma changeP_unit : IsUnit changeP.det := by
  have hdet : changeP.det = 1 := by
    simp [changeP, Matrix.det_fin_two]
  rw [hdet]
  exact isUnit_one

/-- The mass-balanced concentrations are the same before and after the basis change. -/
example : {c | MassBalanced changeB changeT c}
    = {c | MassBalanced (changeP * changeB) (changeP.map (Rat.cast : ℚ → ℝ) *ᵥ changeT) c} :=
  solutionSet_basisChange changeB changeT changeP changeP_unit

/-- The concentrations `![1, 2, 1]` balance `changeB` against `changeT`. -/
lemma change_mass : MassBalanced changeB changeT ![1, 2, 1] := by
  intro k
  fin_cases k <;> simp [changeB, changeT, Fin.sum_univ_succ] <;> norm_num

/-- After the basis change the same concentrations balance the new totals `![5, 3]`. -/
example : MassBalanced (changeP * changeB) ![5, 3] ![1, 2, 1] := by
  have h := (massBalanced_basisChange_iff changeB changeT changeP changeP_unit
    ![1, 2, 1]).2 change_mass
  have hT : changeP.map (Rat.cast : ℚ → ℝ) *ᵥ changeT = ![5, 3] := by
    funext k
    fin_cases k <;> norm_num [changeP, changeT, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rwa [hT] at h

/-- The acetic-acid reference level in the basis `changeP * aceticB` keeps its proton excess. -/
example : (aceticRef.basisChange changeP changeP_unit).protonExcess = aceticRef.protonExcess :=
  aceticRef.protonExcess_basisChange changeP changeP_unit

/-- The real balances and the weighted totals transport to the new basis, where they again give
the proton condition. -/
example : (aceticRef.basisChange changeP changeP_unit).ProtonCondition aceticC := by
  refine (aceticRef.basisChange changeP changeP_unit).protonCondition_of_balances acetic_charge
    ((massBalanced_basisChange_iff aceticB aceticT changeP changeP_unit aceticC).2 acetic_mass)
    ?_
  rw [ProtonReferenceLevel.protonWeightTotal_basisChange]
  simp [aceticRef]

/-- The transported proton condition is the same constraint. -/
example : {c | (aceticRef.basisChange changeP changeP_unit).ProtonCondition c}
    = {c | aceticRef.ProtonCondition c} :=
  aceticRef.protonSet_basisChange changeP changeP_unit

/-- The formation count is unchanged by the basis change. -/
example : independentFormationCount countCharge (changeP * countB) = 2 := by
  rw [independentFormationCount_basisChange countCharge countB changeP changeP_unit,
    countB_formationCount]

/-- A singular change of component basis. -/
def singP : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 1, 0]

/-- The identity component matrix. -/
def singB : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1]

/-- Real component totals. -/
def singT : Fin 2 → ℝ := ![0, 1]

/-- `singP` is singular. -/
example : singP.det = 0 := by
  simp [singP, Matrix.det_fin_two]

/-- After the singular change the mass-balance solution set is strictly larger: `![0, 5]`
solves the transformed system but not the original. -/
example : {c | MassBalanced singB singT c}
    ≠ {c | MassBalanced (singP * singB) (singP.map (Rat.cast : ℚ → ℝ) *ᵥ singT) c} := by
  intro hcon
  have hmem : (![0, 5] : Fin 2 → ℝ) ∈
      {c | MassBalanced (singP * singB) (singP.map (Rat.cast : ℚ → ℝ) *ᵥ singT) c} := by
    intro k
    fin_cases k <;> simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ, singP,
      singB, singT]
  rw [← hcon] at hmem
  have h1 := hmem 1
  norm_num [Fin.sum_univ_succ, singB, singT] at h1

end PhyslibExtTest.Chemistry.Aqueous

#print axioms Chemistry.Aqueous.ChargeBalanced
#print axioms Chemistry.Aqueous.MassBalanced
#print axioms Chemistry.Aqueous.HomMassBalanced
#print axioms Chemistry.Aqueous.massBalanced_iff_mulVec
#print axioms Chemistry.Aqueous.ChargeBalanced.add
#print axioms Chemistry.Aqueous.ChargeBalanced.smul
#print axioms Chemistry.Aqueous.ChargeBalanced.zero
#print axioms Chemistry.Aqueous.HomMassBalanced.add
#print axioms Chemistry.Aqueous.HomMassBalanced.smul
#print axioms Chemistry.Aqueous.HomMassBalanced.zero
#print axioms Chemistry.Aqueous.MassBalanced.sub
#print axioms Chemistry.Aqueous.balances_add
#print axioms Chemistry.Aqueous.balances_smul
#print axioms Chemistry.Aqueous.balanceCombination
#print axioms Chemistry.Aqueous.sum_balanceCombination_mul_eq
#print axioms Chemistry.Aqueous.ProtonReferenceLevel
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.protonExcess
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.ProtonCondition
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.protonExcess_eq_zero
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.protonExcess_water
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.protonExcess_hydronium
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.protonExcess_hydroxide
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.protonExcess_eq_of_content
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.sum_protonExcess_mul_eq
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.protonCondition_of_balances
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.weightedTotal_eq_zero_of_recipe
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.protonCondition_of_recipe
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.protonCondition_iff
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.not_protonCondition_single_hydronium
#print axioms Chemistry.Aqueous.balanceMatrix
#print axioms Chemistry.Aqueous.balanceMatrix_none
#print axioms Chemistry.Aqueous.balanceMatrix_some
#print axioms Chemistry.Aqueous.isBalanced_balanceMatrix_iff
#print axioms Chemistry.Aqueous.isBalanced_balanceMatrix_iff_balances
#print axioms Chemistry.Aqueous.independentFormationCount
#print axioms Chemistry.Aqueous.mem_ker_balanceMatrix_iff
#print axioms Chemistry.Aqueous.independentFormationCount_eq
#print axioms Chemistry.Aqueous.independentFormationCount_eq_of_charge_eq
#print axioms Chemistry.Aqueous.massBalanced_basisChange_iff
#print axioms Chemistry.Aqueous.solutionSet_basisChange
#print axioms Chemistry.Aqueous.independentFormationCount_basisChange
#print axioms Chemistry.Aqueous.balanceCombination_basisChange
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.basisChange
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.protonExcess_basisChange
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.protonWeightTotal_basisChange
#print axioms Chemistry.Aqueous.ProtonReferenceLevel.protonSet_basisChange
