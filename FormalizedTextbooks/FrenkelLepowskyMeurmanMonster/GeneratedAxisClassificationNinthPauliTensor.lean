/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutput
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMiddleEight

/-! Every actual middle tensor coordinate follows from the original Q-translated input states. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every original input-reconstruction denominator is nonzero. -/
theorem generatedNinth_pauli_input_denominator_ne_zero :
    ∀ b : Fin 8, generatedNinthPauliInputDenominator b ≠ 0 := by
  decide +kernel

/-- Every selected actual middle tensor column retains its original Q-translated output. -/
theorem generatedNinth_middle_pauli_basis (b : Fin 8) (t : SpinIndex) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.2 t (generatedNinthInputBasisColumn b) =
        (generatedNinthPauliOutputInteger b (nortonUIntegerLabel t) : ℝ) /
          (32 * (generatedNinthPauliInputDenominator b : ℝ) * Real.sqrt 2) := by
  rw [generatedNinth_middle_column_integer]
  have h : (generatedNinthPauliInputDenominator b : ℝ) *
      (generatedNinthIntegerSpin (generatedNinthColumnInputInteger
        (generatedNinthInputBasisColumn b)) (nortonUIntegerLabel t) : ℝ) =
          1024 * (generatedNinthPauliOutputInteger b (nortonUIntegerLabel t) : ℝ) := by
    exact_mod_cast generatedNinth_pauli_output_integer b (nortonUIntegerLabel t)
  have hd : (generatedNinthPauliInputDenominator b : ℝ) ≠ 0 := by
    exact_mod_cast generatedNinth_pauli_input_denominator_ne_zero b
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hf : (generatedNinthIntegerSpin (generatedNinthColumnInputInteger
      (generatedNinthInputBasisColumn b)) (nortonUIntegerLabel t) : ℝ) =
        1024 * (generatedNinthPauliOutputInteger b (nortonUIntegerLabel t) : ℝ) /
          (generatedNinthPauliInputDenominator b : ℝ) :=
    (eq_div_iff hd).mpr (by simpa only [mul_comm] using h)
  rw [hf]
  field_simp [hd, hs]
  ring

/-- Every actual middle tensor coordinate is the exact original eight-column linear combination. -/
theorem generatedNinth_middle_pauli_tensor (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.2 t i =
        ∑ b : Fin 8, (generatedNinthInputBasisCoefficients i b : ℝ) *
          ((generatedNinthPauliOutputInteger b (nortonUIntegerLabel t) : ℝ) /
            (32 * (generatedNinthPauliInputDenominator b : ℝ) * Real.sqrt 2)) := by
  rw [generatedNinth_middle_tensor_eight]
  apply Finset.sum_congr rfl
  intro b _
  rw [generatedNinth_middle_pauli_basis]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
