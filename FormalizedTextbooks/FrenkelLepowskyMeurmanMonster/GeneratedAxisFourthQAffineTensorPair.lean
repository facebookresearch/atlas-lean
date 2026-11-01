/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineTensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineDictionary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineParameterData

/-! Bind each actual signed pair of Y tensor states to the corresponding affine spin state. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The corresponding original affine state, placed in its actual spatial column. -/
def generatedFourthQAffineTensorState (k : Fin 28) : SpinIndex → Fin 24 → ℝ :=
  fun t i => if i = generatedFourthQAffineTensorColumns k then
    generatedAxisFourthQAffineSpinState generatedAxisFourthQAffineParameterPlane
      (generatedAxisFourthQAffineParameterBases (generatedFourthQAffineTensorFamilyIndex k))
      (generatedAxisFourthQAffineParameterCharacters (generatedFourthQAffineTensorFamilyIndex k)) t
    else 0

/-- The actual low base labels agree with their twenty-two common-family representatives. -/
theorem generatedFourthQAffineTensor_base_binding : ∀ k : Fin 28,
    golayLabelCoefficients ⟨(generatedFourthQAffineTensorBaseLabels k).val, by omega⟩ =
      generatedAxisFourthQAffineParameterBases (generatedFourthQAffineTensorFamilyIndex k) := by
  decide +kernel

/-- The actual characters agree with the same common-family representatives. -/
theorem generatedFourthQAffineTensor_character_binding : ∀ k : Fin 28,
    golayLabelCoefficients (generatedFourthQAffineTensorCharacterLabels k) =
      generatedAxisFourthQAffineParameterCharacters
        (generatedFourthQAffineTensorFamilyIndex k) := by
  decide +kernel

/-- Bit eleven is the actual label-2048 plane vector. -/
theorem generatedFourthQAffineTensor_omega :
    golayLabelCoefficients 2048 = (Pi.single 11 1 : SpinIndex) := by
  decide +kernel

/-- Every actual affine character has the required odd bit-eleven character. -/
theorem generatedFourthQAffineTensor_character_last : ∀ k : Fin 28,
    spinDot (golayLabelCoefficients (generatedFourthQAffineTensorCharacterLabels k))
      (Pi.single 11 1) = 1 := by
  decide +kernel

/-- The two actual low dictionary labels in each pair are distinct. -/
theorem generatedFourthQAffineTensor_low_labels_ne : ∀ k : Fin 28,
    generatedFourthQAffineTensorBaseLabels k ≠
      (generatedFourthOddRootOutputData (generatedFourthQAffineTensorPairIndex (k, 1))).1 := by
  decide +kernel

private theorem fourth_signed_Y_coordinate (c : ZMod 2) (d : Fin 2048) (j : Fin 24)
    (t : SpinIndex) (i : Fin 24) :
    qSign c * trialityYTensor d j t i =
      qSign (c + golayBooleanCast ((golayEncodedMask d.val).testBit j.val)) * qSign (t 11) *
        (if spinDictionaryCode t = d then 1 else 0) * (if i = j then 1 else 0) / Real.sqrt 2 := by
  by_cases hd : spinDictionaryCode t = d <;> by_cases hi : i = j <;>
    cases h : (golayEncodedMask d.val).testBit j.val <;>
      simp [trialityYTensor, h, hd, hi, golayBooleanCast, qSign_add, qSign_one] <;> ring

/-- Each pair of actual original signed Y terms is exactly its nonzero scaled affine state. -/
theorem generatedFourthQAffineTensor_pair (k : Fin 28) :
    (∑ s : Fin 2,
      qSign (generatedFourthOddCoefficientPhaseData
        (generatedFourthQAffineTensorPairIndex (k, s))) •
        trialityYTensor (generatedFourthOddRootOutputData
          (generatedFourthQAffineTensorPairIndex (k, s))).1
          (generatedFourthOddRootOutputData (generatedFourthQAffineTensorPairIndex (k, s))).2) =
      (qSign (generatedFourthQAffineTensorScalePhases k) / Real.sqrt 2) •
        generatedFourthQAffineTensorState k := by
  let d := generatedFourthQAffineTensorBaseLabels k
  let e := (generatedFourthOddRootOutputData (generatedFourthQAffineTensorPairIndex (k, 1))).1
  let j := generatedFourthQAffineTensorColumns k
  let b := golayLabelCoefficients (generatedFourthQAffineTensorCharacterLabels k)
  have he : golayLabelCoefficients ⟨e.val, by omega⟩ =
      golayLabelCoefficients ⟨d.val, by omega⟩ + golayLabelCoefficients 14 :=
    (generatedFourthQAffineTensor_second_output k).1
  have hS (u : SpinIndex) : u ∈ generatedAxisFourthQAffineParameterPlane ↔
      u = 0 ∨ u = golayLabelCoefficients 14 ∨ u = Pi.single 11 1 ∨
        u = golayLabelCoefficients 14 + Pi.single 11 1 := by
    simpa only [generatedFourthQAffineTensor_omega] using
      generatedAxisFourthQAffineParameter_plane_mem_four_iff u
  have hc0 : generatedFourthOddCoefficientPhaseData
        (generatedFourthQAffineTensorPairIndex (k, 0)) +
      golayBooleanCast ((golayEncodedMask d.val).testBit j.val) =
        generatedFourthQAffineTensorScalePhases k := by
    simpa only [generatedFourthQAffineTensor_first_output, Fin.val_zero,
      Nat.cast_zero, zero_mul, add_zero] using generatedFourthQAffineTensor_sign_certificate k 0
  have hc1 : generatedFourthOddCoefficientPhaseData
        (generatedFourthQAffineTensorPairIndex (k, 1)) +
      golayBooleanCast ((golayEncodedMask e.val).testBit j.val) =
        generatedFourthQAffineTensorScalePhases k + spinDot b (golayLabelCoefficients 14) := by
    simpa only [Fin.val_one, Nat.cast_one, one_mul] using
      generatedFourthQAffineTensor_sign_certificate k 1
  funext t i
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    generatedFourthQAffineTensor_first_output, (generatedFourthQAffineTensor_second_output k).2]
  rw [fourth_signed_Y_coordinate, fourth_signed_Y_coordinate]
  change qSign _ * qSign (t 11) * (if spinDictionaryCode t = d then 1 else 0) *
        (if i = j then 1 else 0) / Real.sqrt 2 +
      qSign _ * qSign (t 11) * (if spinDictionaryCode t = e then 1 else 0) *
        (if i = j then 1 else 0) / Real.sqrt 2 = _
  rw [hc0, hc1, qSign_add]
  have hs := generatedFourthQ_affine_dictionary_state
    generatedAxisFourthQAffineParameterPlane d e (golayLabelCoefficients 14) b he hS
    (generatedFourthQAffineTensor_character_last k) t
  rw [generatedFourthQAffineTensor_base_binding] at hs
  have hbb : generatedAxisFourthQAffineParameterCharacters
      (generatedFourthQAffineTensorFamilyIndex k) = b :=
    (generatedFourthQAffineTensor_character_binding k).symm
  simp only [generatedFourthQAffineTensorState, hbb]
  change _ = qSign (generatedFourthQAffineTensorScalePhases k) / Real.sqrt 2 *
    (if i = j then generatedAxisFourthQAffineSpinState generatedAxisFourthQAffineParameterPlane
      (generatedAxisFourthQAffineParameterBases (generatedFourthQAffineTensorFamilyIndex k)) b t
      else 0)
  have hde : d ≠ e := generatedFourthQAffineTensor_low_labels_ne k
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte]
    change _ = qSign (generatedFourthQAffineTensorScalePhases k) / Real.sqrt 2 * _
    rw [hs]
    by_cases hd : spinDictionaryCode t = d
    · simp only [hd, hde, ↓reduceIte, mul_one, mul_zero, zero_div, add_zero]
      ring
    · by_cases he' : spinDictionaryCode t = e
      · simp only [he', Ne.symm hde, ↓reduceIte, mul_one, mul_zero, zero_div, zero_add]
        ring
      · simp only [hd, he', ↓reduceIte, mul_one, mul_zero, zero_div, add_zero]
  · simp only [hij, ↓reduceIte, mul_zero, zero_div, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
