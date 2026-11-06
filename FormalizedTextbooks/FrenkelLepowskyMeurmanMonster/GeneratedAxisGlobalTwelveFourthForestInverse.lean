/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthForestColumns
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskBounds

/-! Compact inverse masks act by the inverse of the actual Fourth stabilizer lifts, and stay
in the actual 24-coordinate mask domain. Thus a descending parent remains in the genuine
binary Ω orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The genuine forward operator sends every checked inverse column to its coordinate unit. -/
theorem generatedAxisGlobalTwelveFourthInverseColumns_forward (k : Fin 5) (j : Fin 24) :
    generatedAxisGlobalTwelveFourthBinaryMatrix k *ᵥ
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveFourthInverseColumns k j) =
        Pi.single j 1 := by
  rw [generatedAxisGlobalTwelveFourthBinaryColumns_action,
    ← generatedAxisGlobalTwelveFourthBinaryRows_action,
    ((generatedAxisGlobalTwelveFourthInverse_certificate k).1 j).2,
    generatedAxisGlobalMaskDecode_two_pow]

/-- Direct inverse row evaluation is the inverse action of the actual Conway element. -/
theorem generatedAxisGlobalTwelveFourthInverseRows_action (k : Fin 5) (b : ℕ) :
    co1BinaryAction (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalTwelveFourthSpatial k))⁻¹
      (monsterCo1GeometryBinaryMaskDecode b) =
    monsterCo1GeometryBinaryMaskDecode
      (generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveFourthInverseRows k) b) := by
  rw [map_inv]
  change (co1BinaryAction
    (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalTwelveFourthSpatial k))).symm
    (monsterCo1GeometryBinaryMaskDecode b) = _
  rw [generatedAxisGlobalMaskColumnMatrix_inverse_apply _ _ _
    (generatedAxisGlobalTwelveFourthSpatial_binary k)
    (generatedAxisGlobalTwelveFourthInverseColumns_forward k)]
  rw [(generatedAxisGlobalTwelveFourthInverse_certificate k).2,
    generatedAxisGlobalMaskRowsAction_ofFn,
    generatedAxisGlobalMaskColumnAction_decode]

/-- The compact inverse parent is exactly the actual local stabilizer inverse action. -/
theorem generatedAxisGlobalTwelveFourthGenerator_inverse_binary (k : Fin 5)
    (x : generatedAxisGlobalBinaryOrbit) :
    (generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveFourthGenerator k).val⁻¹ x).val =
      monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveFourthInverseRows k)
          ((generatedAxisGlobalMaskFiniteEquiv 24).symm x.val).val) := by
  change co1BinaryAction (projH (generatedAxisGlobalTwelveFourthGenerator k).val⁻¹) x.val = _
  rw [map_inv, generatedAxisGlobalTwelveFourthGenerator_projection]
  have hb := (generatedAxisGlobalMaskFiniteEquiv 24).apply_symm_apply x.val
  change monsterCo1GeometryBinaryMaskDecode
    ((generatedAxisGlobalMaskFiniteEquiv 24).symm x.val).val = x.val at hb
  conv_lhs => rw [← hb]
  exact generatedAxisGlobalTwelveFourthInverseRows_action k _

/-- The checked inverse action has no bits outside the genuine 24 coordinates. -/
theorem generatedAxisGlobalTwelveFourthInverseRows_lt (k : Fin 5) (b : ℕ) :
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveFourthInverseRows k) b <
      2 ^ 24 := by
  apply generatedAxisGlobalMaskRowsAction_lt
  rw [(generatedAxisGlobalTwelveFourthInverse_certificate k).2]
  intro p hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  exact ((generatedAxisGlobalTwelveFourthInverse_certificate k).1 j).1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
