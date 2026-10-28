/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthInverseData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthGenerators

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite

/-! Compact inverse masks act by the inverse of the actual fifth stabilizer
lift. Thus a descending parent remains in the genuine binary Ω orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The genuine forward operator sends every checked inverse column to its coordinate unit. -/
theorem generatedAxisGlobalFifthInverseColumns_forward (k : Fin 19) (j : Fin 24) :
    generatedAxisGlobalFifthBinaryMatrix k *ᵥ
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalFifthInverseColumns k j) =
        Pi.single j 1 := by
  rw [generatedAxisGlobalFifthBinaryColumns_action,
    ← generatedAxisGlobalFifthBinaryRows_action,
    ((generatedAxisGlobalFifthInverse_certificate k).1 j).2,
    generatedAxisGlobalMaskDecode_two_pow]

/-- The inverse columns give a proved right inverse of the genuine generator matrix. -/
theorem generatedAxisGlobalFifthInverseMatrix_right_inverse (k : Fin 19) :
    generatedAxisGlobalFifthBinaryMatrix k *
      generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalFifthInverseColumns k) = 1 :=
  generatedAxisGlobalMaskColumnMatrix_right_inverse _ _
    (generatedAxisGlobalFifthInverseColumns_forward k)

/-- Direct inverse row evaluation is the inverse action of the actual Conway element. -/
theorem generatedAxisGlobalFifthInverseRows_action (k : Fin 19) (b : ℕ) :
    co1BinaryAction
      (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthSpatial k))⁻¹
      (monsterCo1GeometryBinaryMaskDecode b) =
    monsterCo1GeometryBinaryMaskDecode
      (generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows k) b) := by
  rw [map_inv]
  change (co1BinaryAction
    (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthSpatial k))).symm
    (monsterCo1GeometryBinaryMaskDecode b) = _
  rw [generatedAxisGlobalMaskColumnMatrix_inverse_apply _ _ _
    (generatedAxisGlobalFifthSpatial_binary k)
    (generatedAxisGlobalFifthInverseColumns_forward k)]
  rw [(generatedAxisGlobalFifthInverse_certificate k).2,
    generatedAxisGlobalMaskRowsAction_ofFn, generatedAxisGlobalMaskColumnAction_decode]

/-- The compact inverse parent is exactly the actual local stabilizer inverse action. -/
theorem generatedAxisGlobalFifthGenerator_inverse_binary (k : Fin 19)
    (x : generatedAxisGlobalBinaryOrbit) :
    (generatedAxisGlobalBinaryAct (generatedAxisGlobalFifthGenerator k).val⁻¹ x).val =
      monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows k)
          ((generatedAxisGlobalMaskFiniteEquiv 24).symm x.val).val) := by
  change co1BinaryAction (projH (generatedAxisGlobalFifthGenerator k).val⁻¹) x.val = _
  rw [map_inv, generatedAxisGlobalFifthGenerator_projection]
  have hb := (generatedAxisGlobalMaskFiniteEquiv 24).apply_symm_apply x.val
  change monsterCo1GeometryBinaryMaskDecode
    ((generatedAxisGlobalMaskFiniteEquiv 24).symm x.val).val = x.val at hb
  conv_lhs => rw [← hb]
  exact generatedAxisGlobalFifthInverseRows_action k _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
