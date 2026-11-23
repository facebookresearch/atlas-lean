/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Thermodynamics.Thermochemistry

import Mathlib.Tactic.NormNum

/-!

# Tests for thermochemistry: Hess, formation enthalpies, Kirchhoff, calorimetry

-/

@[expose] public section

open Matrix Chemistry.Thermodynamics intervalIntegral

namespace PhyslibExtTest.Chemistry.Thermodynamics

/-- Abstract molar enthalpies on two species (arbitrary units, no real substance). -/
def testH : Fin 2 → ℝ := ![10, 20]

/-- Two abstract reactions on two species. -/
def testReactions : Fin 2 → Fin 2 → ℝ := ![![1, -1], ![0, 2]]

/-- Combination coefficients for the two reactions. -/
def testCoeffs : Fin 2 → ℝ := ![3, -1]

example : reactionEnthalpy testH (testReactions 0 + testReactions 1)
    = reactionEnthalpy testH (testReactions 0) + reactionEnthalpy testH (testReactions 1) :=
  hess_add _ _ _

example : reactionEnthalpy testH ((3 : ℝ) • testReactions 0)
    = 3 * reactionEnthalpy testH (testReactions 0) :=
  hess_smul _ _ _

example : reactionEnthalpy testH (∑ r, testCoeffs r • testReactions r)
    = ∑ r, testCoeffs r * reactionEnthalpy testH (testReactions r) :=
  hess_law _ _ _

example : reactionEnthalpy testH (∑ r, testCoeffs r • testReactions r) = -70 := by
  norm_num [reactionEnthalpy_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_two, testH, testCoeffs, testReactions]

example : (∑ r, testCoeffs r * reactionEnthalpy testH (testReactions r)) = -70 := by
  norm_num [reactionEnthalpy_apply, Fin.sum_univ_two, testH, testCoeffs, testReactions]

example : reactionEnthalpy testH 0 = 0 :=
  reactionEnthalpy_zero _

/-- Abstract formation enthalpies: species 0 and 1 are reference-state elements. -/
def testHf : Fin 3 → ℝ := ![0, 0, 5]

/-- Abstract reaction consuming the reference-state species to form species 2. -/
def testNu : Fin 3 → ℝ := ![-2, -1, 1]

example : IsReferenceState {0, 1} testHf := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> norm_num [testHf]

example : reactionEnthalpy testHf testNu = 5 := by
  norm_num [reactionEnthalpy_apply, Fin.sum_univ_three, testHf, testNu]

example : (∑ i ∈ ({0, 1} : Finset (Fin 3)), testNu i * testHf i) = 0 :=
  reference_species_contrib_eq_zero _ _ _ (by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> norm_num [testHf])

/-- One balance coordinate over two species. -/
def testA : Matrix (Fin 1) (Fin 2) ℝ := fun _ => ![1, -1]

/-- Abstract reaction balanced for `testA`. -/
def testNu2 : Fin 2 → ℝ := ![1, 1]

/-- Abstract formation enthalpies for the shift test. -/
def testHf2 : Fin 2 → ℝ := ![5, 7]

/-- Abstract element potential for the shift test. -/
def teste : Fin 1 → ℝ := ![2]

lemma testShiftBalanced : Chemistry.Stoichiometry.IsBalanced testA testNu2 := by
  unfold Chemistry.Stoichiometry.IsBalanced
  funext b
  have hb : b = 0 := Fin.eq_zero b
  subst hb
  show (∑ i, testA 0 i * testNu2 i) = 0
  norm_num [Fin.sum_univ_two, testA, testNu2]

example : reactionEnthalpy (fun i => testHf2 i + ∑ b, testA b i * teste b) testNu2
    = reactionEnthalpy testHf2 testNu2 :=
  reactionEnthalpy_shift_of_isBalanced _ _ _ _ testShiftBalanced

example : reactionEnthalpy testHf2 testNu2 = 12 := by
  norm_num [reactionEnthalpy_apply, Fin.sum_univ_two, testHf2, testNu2]

example : reactionEnthalpy (fun i => testHf2 i + ∑ b, testA b i * teste b) testNu2 = 12 := by
  norm_num [reactionEnthalpy_apply, Fin.sum_univ_two, Fin.sum_univ_one, testHf2, testA,
    teste, testNu2]

example : (∫ _ in (0 : ℝ)..2, (1 : ℝ)) = (2 : ℝ) := by
  rw [intervalIntegral.integral_const, smul_eq_mul]
  norm_num

example : (fun T : ℝ => T) 2 = (fun T : ℝ => T) 0 + ∫ _ in (0 : ℝ)..2, (1 : ℝ) := by
  have hderiv : ∀ T ∈ Set.uIcc (0 : ℝ) 2,
      HasDerivAt (fun T : ℝ => T) ((fun _ => (1 : ℝ)) T) T := by
    intro T _
    exact hasDerivAt_id T
  have hint : IntervalIntegrable (fun _ => (1 : ℝ)) MeasureTheory.volume 0 2 :=
    Continuous.intervalIntegrable continuous_const 0 2
  have h := kirchhoff_law (fun T : ℝ => T) (fun _ => (1 : ℝ)) 0 2 hderiv hint
  exact h

example : (fun T : ℝ => T) 0 = (fun T : ℝ => T) 2 + ∫ _ in (2 : ℝ)..0, (1 : ℝ) := by
  have hderiv : ∀ T ∈ Set.uIcc (0 : ℝ) 2,
      HasDerivAt (fun T : ℝ => T) ((fun _ => (1 : ℝ)) T) T := by
    intro T _
    exact hasDerivAt_id T
  have hint : IntervalIntegrable (fun _ => (1 : ℝ)) MeasureTheory.volume 0 2 :=
    Continuous.intervalIntegrable continuous_const 0 2
  have h := kirchhoff_swapped (fun T : ℝ => T) (fun _ => (1 : ℝ)) 0 2 hderiv hint
  exact h

example (H : ℝ → ℝ) (T1 T2 : ℝ) (hderiv : ∀ T ∈ Set.uIcc T1 T2, HasDerivAt H 0 T) :
    H T2 = H T1 := by
  have hint : IntervalIntegrable (fun _ => (0 : ℝ)) MeasureTheory.volume T1 T2 :=
    Continuous.intervalIntegrable continuous_const T1 T2
  have hderiv' : ∀ T ∈ Set.uIcc T1 T2, HasDerivAt H ((fun _ => (0 : ℝ)) T) T := hderiv
  have h := kirchhoff_law H (fun _ => (0 : ℝ)) T1 T2 hderiv' hint
  have hint0 : (∫ T in T1..T2, (fun _ => (0 : ℝ)) T) = 0 := intervalIntegral.integral_zero
  rw [hint0, add_zero] at h
  exact h

example : (∫ _ in (1 : ℝ)..1, (5 : ℝ)) = (0 : ℝ) :=
  intervalIntegral.integral_same

example : calorimeterHeat (209 / 50 : ℝ) (5 / 2) = 209 / 20 := by
  norm_num [calorimeterHeat]

example : (-(209 / 20) : ℝ) < 0 ↔ (0 : ℝ) < 5 / 2 :=
  calorimetry_exothermic_iff_temp_rise (209 / 50) (5 / 2) (-(209 / 20)) (by norm_num)
    (by norm_num [calorimeterHeat])

example (C dT q_rxn : ℝ) (hisol : q_rxn + calorimeterHeat C dT = 0) :
    q_rxn = -calorimeterHeat C dT :=
  calorimetry_reaction_heat C dT q_rxn hisol

example (C : ℝ) : calorimeterHeat C 0 = 0 := by
  simp [calorimeterHeat]

end PhyslibExtTest.Chemistry.Thermodynamics

#print axioms Chemistry.Thermodynamics.hess_law
#print axioms Chemistry.Thermodynamics.hess_add
#print axioms Chemistry.Thermodynamics.hess_smul
#print axioms Chemistry.Thermodynamics.hess_double
#print axioms Chemistry.Thermodynamics.reactionEnthalpy_zero
#print axioms Chemistry.Thermodynamics.reference_species_contrib_eq_zero
#print axioms Chemistry.Thermodynamics.reactionEnthalpy_shift_of_isBalanced
#print axioms Chemistry.Thermodynamics.kirchhoff_law
#print axioms Chemistry.Thermodynamics.kirchhoff_of_continuous
#print axioms Chemistry.Thermodynamics.kirchhoff_swapped
#print axioms Chemistry.Thermodynamics.calorimetry_reaction_heat
#print axioms Chemistry.Thermodynamics.calorimetry_temp_change
#print axioms Chemistry.Thermodynamics.calorimetry_exothermic_iff_temp_rise
