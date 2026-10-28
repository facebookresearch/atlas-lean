/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddCoordinates

/-! Original triality tensor coordinates when the incoming physical tensor vanishes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- For a tensor-zero input, the original odd-short coefficient becomes its actual Y tensor. -/
theorem generatedFourthQ_triality_tensor_coordinate (x : GriessSpace)
    (hx : (griessConwayEncode x).2.2 = 0) (t : SpinIndex) (j : Fin 24) :
    (griessConwayEncode (sExtra x)).2.2 t j =
      (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (spinDictionaryCode t, j))) *
        trialityYTensor (spinDictionaryCode t) j t j := by
  have he : x = griessConwayDecode
      ((griessConwayEncode x).1, ((griessConwayEncode x).2.1, 0)) := by
    rw [← hx]
    exact (griessConwayDecode_encode x).symm
  conv_lhs => rw [he]
  have h1 : trialityCycle.symm 1 = 0 := by decide
  have h2 : trialityCycle.symm 2 = 1 := by decide
  simp [griessConwayEncode, sExtra, griessTriality, griessConwayDecode,
    trialityBlockAction, trialityCycleAction, h1, h2, trialityYTensor]
  split_ifs <;> ring

/-- The finite original Y-basis sum evaluates to the unique incident dictionary entry. -/
theorem generatedFourthQ_tensor_sum_coordinate (X : GriessShortIndex → ℝ)
    (t : SpinIndex) (j : Fin 24) :
    (∑ d : Fin 2048, ∑ i : Fin 24,
      X (Sum.inr (Sum.inr (d, i))) • trialityYTensor d i) t j =
      X (Sum.inr (Sum.inr (spinDictionaryCode t, j))) *
        trialityYTensor (spinDictionaryCode t) j t j := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (spinDictionaryCode t)]
  · rw [Finset.sum_eq_single j]
    · intro i _ hi
      simp [trialityYTensor, Ne.symm hi]
    · simp
  · intro d _ hd
    apply Finset.sum_eq_zero
    intro i _
    simp [trialityYTensor, Ne.symm hd]
  · simp

/-- The full outgoing physical tensor is the finite sum of original odd-short Y states. -/
theorem generatedFourthQ_triality_tensor_sum (x : GriessSpace)
    (hx : (griessConwayEncode x).2.2 = 0) :
    (griessConwayEncode (sExtra x)).2.2 =
      ∑ d : Fin 2048, ∑ i : Fin 24,
        (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (d, i))) • trialityYTensor d i := by
  funext t j
  rw [generatedFourthQ_triality_tensor_coordinate x hx,
    generatedFourthQ_tensor_sum_coordinate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
