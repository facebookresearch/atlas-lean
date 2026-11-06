/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete physical positive-triality packet of an arbitrary pure tensor. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorOddShortTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorTrialityFullCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTrialityMatrixZero

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete short contribution obtained from the old physical tensor sum. -/
noncomputable def monsterNortonTensorPositiveShort (T : SpinIndex → Fin 24 → ℝ) :
    GriessShortIndex → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (d, i)) =>
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (T (golayLabelCoefficients ⟨d.val, by omega⟩) i +
          T (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2

/-- Both complete physical constituents of the positive-triality image of a pure tensor. -/
noncomputable def monsterNortonTensorPositivePacket (T : SpinIndex → Fin 24 → ℝ) : GriessSpace :=
  griessConwayDecode (0, (monsterNortonTensorPositiveShort T,
    monsterNortonTensorTrialityCoordinates 0 T))

/-- The packet is the entire actual image; all matrix, pair, and octad zero rows are proved. -/
theorem monsterNortonTensorPositivePacket_actual (T : SpinIndex → Fin 24 → ℝ) :
    sExtra (griessConwayDecode (0, (0, T))) = monsterNortonTensorPositivePacket T := by
  have hi : griessConwayEncode (griessConwayDecode (0, (0, T))) = (0, (0, T)) :=
    griessConwayEncode_decode _ (by intro i j; rfl)
  have hm : ∀ i j,
      (griessConwayEncode (griessConwayDecode (0, (0, T)))).1 i j = 0 := by
    intro i j
    rw [hi]
    rfl
  have hp : ∀ s p,
      (griessConwayEncode (griessConwayDecode (0, (0, T)))).2.1 (Sum.inl (s, p)) = 0 := by
    intro s p
    rw [hi]
    rfl
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [monsterNortonTensorPositivePacket, griessConwayEncode_decode _ (by intro i j; rfl)]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i j
    exact monsterNortonTensor_extra_matrix_zero _ hm hp i j
  · funext r
    rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, i⟩)
    · exact monsterNortonTensor_extra_pair_short_zero _ hm hp s p
    · rw [monsterNortonTensor_extra_octad_coordinates]
      have hz : (fun e =>
          (griessConwayEncode (griessConwayDecode (0, (0, T)))).2.1
            (Sum.inr (Sum.inl (d, e)))) = 0 := by
        rw [hi]
        rfl
      rw [hz, map_zero]
      rfl
    · rw [monsterNortonTensor_extra_odd_short_coordinates, hi]
      rfl
  · funext t i
    rw [monsterNortonTensorTrialityCoordinates_actual, hi]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
