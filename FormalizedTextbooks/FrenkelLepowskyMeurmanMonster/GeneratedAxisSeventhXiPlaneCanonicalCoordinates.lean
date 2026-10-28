/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorTrialityFullCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorOddShortTriality

/-! Exact integer-coordinate normalizations for the complete canonical seventh packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true

/-- The complete preferred-label short numerator includes all original input central phases. -/
def generatedSeventhXiMiddleShortNumerator (r : GriessShortIndex) : ℤ :=
  ∑ s : Fin 2, ∑ p : Fin 276,
    generatedSeventhXiShortInputWeight s p *
      nortonUIntegerSign (generatedSeventhXiShortPhaseBit s p : ZMod 2) *
        (if r = generatedSeventhXiShortOutputLabel s p then 1 else 0)

/-- Every genuine canonical middle short coordinate has the integer denominator four. -/
theorem generatedSeventhXi_canonical_middle_short (r : GriessShortIndex) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalMiddle).2.1 r =
      (generatedSeventhXiMiddleShortNumerator r : ℝ) / 4 := by
  rw [generatedSeventhXiPlaneCanonicalMiddle_encode]
  change (griessConwayEncode
    (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.1 r = _
  rw [generatedSeventhXi_middle_short_weighted]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    generatedSeventhXiMiddleShortNumerator, Int.cast_sum, Int.cast_mul,
    Int.cast_ite, Int.cast_one, Int.cast_zero, nortonUIntegerSign_real,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

/-- All 4096 canonical tensor rows have the checked integer spin numerator. -/
theorem generatedSeventhXi_canonical_middle_tensor (d : Fin 4096) (i : Fin 24) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalMiddle).2.2
      (golayLabelCoefficients d) i =
      -(generatedSeventhXiPlaneSpinInteger d : ℝ) *
        (generatedSeventhFrameVectorData 7 0 i : ℝ) / (16 * Real.sqrt 2) := by
  rw [generatedSeventhXiPlaneCanonicalMiddle_encode]
  change -generatedSeventhXiPlaneNormalizedSpin (golayLabelCoefficients d) *
    (generatedSeventhFrameVectorData 7 0 i : ℝ) / Real.sqrt 2 = _
  rw [generatedSeventhXiPlaneSpinInteger_coordinate]
  ring

/-- The canonical outgoing odd row has the exact sum of the two checked Omega spin coefficients. -/
theorem generatedSeventhXi_canonical_axis_odd (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1
      (Sum.inr (Sum.inr (d, i))) =
      -qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (generatedSeventhFrameVectorData 7 0 i : ℝ) *
        ((generatedSeventhXiPlaneSpinInteger ⟨d.val, by omega⟩ : ℝ) +
         (generatedSeventhXiPlaneSpinInteger ⟨d.val + 2048, by omega⟩ : ℝ)) / 32 := by
  rw [generatedSeventhXiPlaneCanonicalAxis,
    monsterNortonTensor_extra_odd_short_coordinates,
    generatedSeventhXi_canonical_middle_tensor, generatedSeventhXi_canonical_middle_tensor]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hr : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hs]
  rw [hr]
  ring

/-- Each outgoing tensor row retains the complete preferred-short and checked spin contributions. -/
theorem generatedSeventhXi_canonical_axis_tensor (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2 t i =
      let d := spinDictionaryCode t
      let σ : ℝ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
      σ * (qSign (t 11) * 8 *
          (generatedSeventhXiMiddleShortNumerator (Sum.inr (Sum.inr (d, i))) : ℝ) -
        qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          (generatedSeventhFrameVectorData 7 0 i : ℝ) *
          ((generatedSeventhXiPlaneSpinInteger ⟨d.val, by omega⟩ : ℝ) -
           (generatedSeventhXiPlaneSpinInteger ⟨d.val + 2048, by omega⟩ : ℝ))) /
        (32 * Real.sqrt 2) := by
  rw [generatedSeventhXiPlaneCanonicalAxis, monsterNortonTensorTrialityCoordinates_actual]
  unfold monsterNortonTensorTrialityCoordinates
  dsimp only
  rw [generatedSeventhXi_canonical_middle_short,
    generatedSeventhXi_canonical_middle_tensor, generatedSeventhXi_canonical_middle_tensor]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hr : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hs]
  rw [hr]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
