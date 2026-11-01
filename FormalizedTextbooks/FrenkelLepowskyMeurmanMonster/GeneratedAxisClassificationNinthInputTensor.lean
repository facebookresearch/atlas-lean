/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpinInteger

/-! Integral coordinates of the genuine fifth tensor entering the ninth local word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The exact 64 signed Y states in one original fifth tensor column. -/
def generatedNinthInputTensorInteger (j : Fin 24) : NortonUIntegerVector := fun n =>
  let t := golayLabelCoefficients n
  ∑ k : Fin 64,
    nortonUIntegerSign (generatedFifthOddCoefficientPhaseData k) *
      nortonUIntegerSign (t 11) *
      (if (golayEncodedMask (generatedFifthOddRootOutputData k).1.val).testBit j.val
        then -1 else 1) *
      (if n.val % 2048 = (generatedFifthOddRootOutputData k).1.val then 1 else 0) *
      (if j = (generatedFifthOddRootOutputData k).2 then 1 else 0)

private theorem generatedNinth_input_dictionary_code (t : SpinIndex) :
    (spinDictionaryCode t).val = (nortonUIntegerLabel t).val % 2048 := by
  have h : spinDictionaryLabel t = nortonUIntegerLabel t := by
    apply golayLabelCoefficients_injective
    rw [nortonUIntegerLabel_inverse]
    exact (Equiv.ofBijective golayLabelCoefficients
      golayLabelCoefficients_bijective).apply_symm_apply t
  exact congrArg (fun d : Fin 4096 => d.val % 2048) h

private theorem generatedNinth_input_dictionary_eq (t : SpinIndex) (d : Fin 2048) :
    spinDictionaryCode t = d ↔ (nortonUIntegerLabel t).val % 2048 = d.val := by
  rw [Fin.ext_iff, generatedNinth_input_dictionary_code]

/-- Each true input column is the integral vector divided by square root two. -/
theorem generatedNinth_input_tensor_embed (j : Fin 24) :
    (fun t => (griessConwayEncode generatedFifthAxis).2.2 t j) =
      (1 / Real.sqrt 2 : ℝ) • nortonUIntegerEmbed (generatedNinthInputTensorInteger j) := by
  funext t
  rw [generatedFifth_tensor_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, trialityYTensor,
    nortonUIntegerEmbed, generatedNinthInputTensorInteger, nortonUIntegerLabel_inverse,
    Int.cast_sum, Int.cast_mul, nortonUIntegerSign_real, Int.cast_ite,
    Int.cast_neg, Int.cast_one, Int.cast_zero, generatedNinth_input_dictionary_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hj : j = (generatedFifthOddRootOutputData k).2
  · simp only [hj, ite_true]
    ring
  · simp only [hj, ite_false, mul_zero, zero_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
