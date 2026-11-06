/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddInverseData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddGenerators

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite

/-! Compact inverse masks act by the inverse of the actual odd stabilizer
lift. Thus a descending parent remains in the genuine binary Ω orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The genuine forward operator sends every checked inverse column to its coordinate unit. -/
theorem generatedAxisGlobalOddInverseColumns_forward (k : Fin 14) (j : Fin 24) :
    generatedAxisGlobalOddBinaryMatrix k *ᵥ
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddInverseColumns k j) =
        Pi.single j 1 := by
  rw [generatedAxisGlobalOddBinaryColumns_action,
    ← generatedAxisGlobalOddBinaryRows_action,
    ((generatedAxisGlobalOddInverse_certificate k).1 j).2,
    generatedAxisGlobalMaskDecode_two_pow]

/-- The inverse columns give a proved right inverse of the genuine generator matrix. -/
theorem generatedAxisGlobalOddInverseMatrix_right_inverse (k : Fin 14) :
    generatedAxisGlobalOddBinaryMatrix k *
      generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalOddInverseColumns k) = 1 :=
  generatedAxisGlobalMaskColumnMatrix_right_inverse _ _
    (generatedAxisGlobalOddInverseColumns_forward k)

/-- Direct inverse row evaluation is the inverse action of the actual Conway element. -/
theorem generatedAxisGlobalOddInverseRows_action (k : Fin 14) (b : ℕ) :
    co1BinaryAction
      (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalOddSpatial k))⁻¹
      (monsterCo1GeometryBinaryMaskDecode b) =
    monsterCo1GeometryBinaryMaskDecode
      (generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddInverseRows k) b) := by
  rw [map_inv]
  change (co1BinaryAction
    (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalOddSpatial k))).symm
    (monsterCo1GeometryBinaryMaskDecode b) = _
  rw [generatedAxisGlobalMaskColumnMatrix_inverse_apply _ _ _
    (generatedAxisGlobalOddSpatial_binary k)
    (generatedAxisGlobalOddInverseColumns_forward k)]
  rw [(generatedAxisGlobalOddInverse_certificate k).2,
    generatedAxisGlobalMaskRowsAction_ofFn, generatedAxisGlobalMaskColumnAction_decode]

/-- The compact inverse parent is exactly the actual local stabilizer inverse action. -/
theorem generatedAxisGlobalOddGenerator_inverse_binary (k : Fin 14)
    (x : generatedAxisGlobalBinaryOrbit) :
    (generatedAxisGlobalBinaryAct (generatedAxisGlobalOddGenerator k).val⁻¹ x).val =
      monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddInverseRows k)
          ((generatedAxisGlobalMaskFiniteEquiv 24).symm x.val).val) := by
  change co1BinaryAction (projH (generatedAxisGlobalOddGenerator k).val⁻¹) x.val = _
  rw [map_inv, generatedAxisGlobalOddGenerator_projection]
  have hb := (generatedAxisGlobalMaskFiniteEquiv 24).apply_symm_apply x.val
  change monsterCo1GeometryBinaryMaskDecode
    ((generatedAxisGlobalMaskFiniteEquiv 24).symm x.val).val = x.val at hb
  conv_lhs => rw [← hb]
  exact generatedAxisGlobalOddInverseRows_action k _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
