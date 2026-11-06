/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhSeventhMatrixFrame
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhSpatialStabilizer

/-! Actual full matrix stabilizers are identified by a proved genuine original frame conjugation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Entire actual matrix fixation is preserved by the genuine original frame conjugation. -/
theorem generatedEleventh_spatial_seventh_conjugation (g : leechIsomSubgroup) :
    generatedEleventhSeventhMatrixFrame * g * generatedEleventhSeventhMatrixFrame⁻¹ ∈
        generatedSeventhSpatialStabilizer ↔ g ∈ generatedEleventhSpatialStabilizer := by
  change conwayMatrixAction _ (griessConwayEncode generatedSeventhAxis).1 = _ ↔
    conwayMatrixAction g (griessConwayEncode generatedEleventhAxis).1 = _
  rw [← generatedEleventh_seventh_matrix_conjugation, map_mul, map_mul, map_inv]
  change conwayMatrixAction generatedEleventhSeventhMatrixFrame (conwayMatrixAction g
    ((conwayMatrixAction generatedEleventhSeventhMatrixFrame).symm
      (conwayMatrixAction generatedEleventhSeventhMatrixFrame
        (griessConwayEncode generatedEleventhAxis).1))) =
    conwayMatrixAction generatedEleventhSeventhMatrixFrame
      (griessConwayEncode generatedEleventhAxis).1 ↔ _
  rw [LinearEquiv.symm_apply_apply]
  exact (conwayMatrixAction generatedEleventhSeventhMatrixFrame).injective.eq_iff

/-- Genuine conjugation identifies the entire actual matrix-fixer groups with lattice signs. -/
def generatedEleventhSeventhSpatialEquiv :
    generatedEleventhSpatialStabilizer ≃* generatedSeventhSpatialStabilizer where
  toFun g := ⟨generatedEleventhSeventhMatrixFrame * g.val *
    generatedEleventhSeventhMatrixFrame⁻¹,
      (generatedEleventh_spatial_seventh_conjugation g.val).mpr g.property⟩
  invFun h := ⟨generatedEleventhSeventhMatrixFrame⁻¹ * h.val *
    generatedEleventhSeventhMatrixFrame, by
      apply (generatedEleventh_spatial_seventh_conjugation _).mp
      convert h.property using 1
      group⟩
  left_inv g := by apply Subtype.ext; group
  right_inv h := by apply Subtype.ext; group
  map_mul' g h := by
    apply Subtype.ext
    change generatedEleventhSeventhMatrixFrame * (g.val * h.val) *
      generatedEleventhSeventhMatrixFrame⁻¹ =
        (generatedEleventhSeventhMatrixFrame * g.val * generatedEleventhSeventhMatrixFrame⁻¹) *
          (generatedEleventhSeventhMatrixFrame * h.val * generatedEleventhSeventhMatrixFrame⁻¹)
    group

/-- The complete actual matrix stabilizer has precisely 159252480 genuine Co0 elements. -/
theorem generatedEleventh_spatial_stabilizer_card :
    Nat.card generatedEleventhSpatialStabilizer = 159252480 := by
  rw [Nat.card_congr generatedEleventhSeventhSpatialEquiv.toEquiv]
  exact generatedSeventhSpatialStabilizer_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
