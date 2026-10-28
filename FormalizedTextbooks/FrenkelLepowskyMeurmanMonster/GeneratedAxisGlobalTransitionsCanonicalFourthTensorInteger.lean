/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthTensorInteger
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTensor

/-! The exact full actual fourth tensor has a computable integer numerator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The complete integer numerator of the genuine fourth tensor, including its zero coordinates. -/
def generatedAxisGlobalCanonicalFourthTensorInteger (k : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ r : Fin 56,
    generatedAxisGlobalIntSign
      (generatedFourthOddCoefficientPhaseData r + golayLabelCoefficients k 11) *
    (if (golayEncodedMask (generatedFourthOddRootOutputData r).1.val).testBit i.val then -1 else 1) *
    (if k.val % 2048 = (generatedFourthOddRootOutputData r).1.val ∧
        i = (generatedFourthOddRootOutputData r).2 then 1 else 0)

/-- Every displayed integer coefficient is the actual full physical tensor coefficient. -/
theorem generatedAxisGlobalCanonicalFourthTensorInteger_coefficient (k : Fin 4096) (i : Fin 24) :
    Real.sqrt 2 * (griessConwayEncode generatedFourthAxis).2.2 (golayLabelCoefficients k) i =
      (generatedAxisGlobalCanonicalFourthTensorInteger k i : ℝ) := by
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  rw [generatedFourth_tensor_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    generatedAxisGlobalCanonicalFourthTensorInteger, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hdict (d : Fin 2048) : spinDictionaryCode (golayLabelCoefficients k) = d ↔
      k.val % 2048 = d.val := by
    simp only [spinDictionaryCode, spinDictionaryLabel_coeff, Fin.ext_iff]
  rw [trialityYTensor]
  simp only [hdict, Int.cast_mul, generatedAxisGlobalIntSign_real, qSign_add]
  by_cases hd : k.val % 2048 = (generatedFourthOddRootOutputData r).1.val
  all_goals by_cases hi : i = (generatedFourthOddRootOutputData r).2
  all_goals simp [hd, hi]
  all_goals field_simp
  all_goals split_ifs <;> ring

/-- The complete original tensor equals its exact integer packet divided by square root two. -/
theorem generatedAxisGlobalCanonicalFourthTensorInteger_eq :
    (griessConwayEncode generatedFourthAxis).2.2 =
      fun t i => (generatedAxisGlobalCanonicalFourthTensorInteger (generatedAxisGlobalSpinLabel t) i : ℝ) /
        Real.sqrt 2 := by
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  funext t i
  have h := generatedAxisGlobalCanonicalFourthTensorInteger_coefficient (generatedAxisGlobalSpinLabel t) i
  rw [generatedAxisGlobalSpinLabel_decode] at h
  apply (eq_div_iff hn).mpr
  nlinarith [h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
