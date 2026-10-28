/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole positive-triality pairings read its actual short and physical tensor coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorCoordinatePairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorPositiveTrialityPacket

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The full pure-tensor triality packet has its exact original odd-short pairing. -/
theorem monsterNortonTensorPositivePacket_odd_form (a : SpinSpace) (b : Fin 24 → ℝ)
    (d : Fin 2048) (j : Fin 24) :
    griessForm (monsterNortonTensorPositivePacket (conwayTensorCoordinates (a ⊗ₜ[ℝ] b)))
      (monsterNortonPureShort (Sum.inr (Sum.inr (d, j)))) =
        qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          ((a (golayLabelCoefficients ⟨d.val, by omega⟩) +
            a (golayLabelCoefficients ⟨d.val + 2048, by omega⟩)) * b j) / Real.sqrt 2 := by
  rw [monsterNortonForm_pureShort_right, monsterNortonTensorPositivePacket]
  change (griessConwayEncode (griessConwayDecode (0,
    (monsterNortonTensorPositiveShort (conwayTensorCoordinates (a ⊗ₜ[ℝ] b)),
      monsterNortonTensorTrialityCoordinates 0 (conwayTensorCoordinates (a ⊗ₜ[ℝ] b)))))).2.1
        (Sum.inr (Sum.inr (d, j))) = _
  rw [griessConwayEncode_decode _ (by intros; rfl)]
  simp only [monsterNortonTensorPositiveShort, conwayTensorCoordinates_tmul]
  ring

/-- The full pure-tensor triality packet retains the exact physical tensor pairing. -/
theorem monsterNortonTensorPositivePacket_tensor_form (a : SpinSpace) (b : Fin 24 → ℝ)
    (t : SpinIndex) (j : Fin 24) :
    griessForm (monsterNortonTensorPositivePacket (conwayTensorCoordinates (a ⊗ₜ[ℝ] b)))
      (monsterNortonTensorUnit t j) =
        qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
          (if (golayEncodedMask (spinDictionaryCode t).val).testBit j.val then (-1 : ℝ) else 1) *
          ((a (golayLabelCoefficients ⟨(spinDictionaryCode t).val, by omega⟩) -
            a (golayLabelCoefficients ⟨(spinDictionaryCode t).val + 2048, by omega⟩)) * b j) /
          2 := by
  rw [monsterNortonForm_tensorUnit_right, monsterNortonTensorPositivePacket,
    griessConwayEncode_decode _ (by intros; rfl)]
  simp only [monsterNortonTensorTrialityCoordinates, conwayTensorCoordinates_tmul,
    Pi.zero_apply, mul_zero, add_zero]
  rw [mul_div_assoc, div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
