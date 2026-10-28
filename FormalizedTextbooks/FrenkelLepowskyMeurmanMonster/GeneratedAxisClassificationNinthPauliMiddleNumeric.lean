/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliImageCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputCertificates

/-! Exact middle numerators are bound to every original tensor coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The signed finite sum is exactly the full original Q-image output, including central phases. -/
theorem generatedNinth_pauli_output_fast_actual (b : Fin 8) (n : Fin 4096) :
    generatedNinthPauliOutputInteger b n = generatedNinthPauliOutputFast b n := by
  unfold generatedNinthPauliOutputInteger generatedNinthPauliOutputFast
  apply Finset.sum_congr rfl
  intro q _
  by_cases hc : generatedNinthPauliInputCoefficients b q = 0
  · simp only [hc, ite_true, zero_mul]
  · rw [ite_eq_right hc]
    change generatedNinthPauliInputCoefficients b q *
      nortonUIntegerQ (generatedNinthQImage (generatedNinthPauliQ
        (generatedNinthPauliWitnessLabels q 0) (generatedNinthPauliWitnessLabels q 1)))
          (generatedNinthColumnSpinData 9) n = _
    rw [generatedNinth_pauli_image_certificate]
    have hi : generatedNinthPauliImage q = generatedNinthPauliLift
        (generatedNinthPauliImageLabels q).1 (generatedNinthPauliImageLabels q).2.1
          (generatedNinthPauliImageLabels q).2.2 := rfl
    rw [hi, generatedNinth_pauli_lift_integer]
    have hc9 : generatedNinthColumnSpinData 9 = generatedNinthColumnSpinPacked 9 := by
      funext m
      exact (generatedNinth_column_spin_packed 9 m).symm
    rw [hc9]
    simp only [nortonUIntegerSign, mul_assoc]

/-- Every selected tensor column equals its original checked integer numerator over32sqrt2. -/
theorem generatedNinth_middle_pauli_numeric_basis (b : Fin 8) (t : SpinIndex) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.2 t (generatedNinthInputBasisColumn b) =
        (generatedNinthPauliMiddleInteger b (nortonUIntegerLabel t) : ℝ) /
          (32 * Real.sqrt 2) := by
  rw [generatedNinth_middle_pauli_basis, generatedNinth_pauli_output_fast_actual,
    generatedNinth_pauli_output_certificate]
  have hd : (generatedNinthPauliInputDenominator b : ℝ) ≠ 0 := by
    exact_mod_cast generatedNinth_pauli_input_denominator_ne_zero b
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  simp only [Int.cast_mul]
  field_simp [hd, hs]

/-- The complete original middle tensor numerator assembled from eight independent source inputs. -/
def generatedNinthMiddleNumerator (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ b : Fin 8, generatedNinthInputBasisCoefficients i b * generatedNinthPauliMiddleInteger b n

/-- Every actual middle tensor coordinate has the original checked numerator over32sqrt2. -/
theorem generatedNinth_middle_numeric (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.2 t i =
        (generatedNinthMiddleNumerator (nortonUIntegerLabel t) i : ℝ) /
          (32 * Real.sqrt 2) := by
  rw [generatedNinth_middle_tensor_eight]
  simp_rw [generatedNinth_middle_pauli_numeric_basis]
  unfold generatedNinthMiddleNumerator
  simp only [Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
