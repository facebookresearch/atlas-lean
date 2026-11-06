/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The final actual triality and V steps return the full tensor input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01Fourteenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegralTensorColumn

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem after_v_xyz :
    monsterNortonLine01TensorAfterV =
      (1 / 2 : ℝ) • trialityXYZBasis 1
        (finProdFinEquiv ((1038 : Fin 2048), (0 : Fin 24))) -
      (1 / 2 : ℝ) • trialityXYZBasis 2
        (finProdFinEquiv ((1038 : Fin 2048), (0 : Fin 24))) := by
  have hc : (golayEncodedMask (1038 : Fin 2048).val).testBit (0 : Fin 24).val = false := by
    decide +kernel
  have hp : qSign (golayMaskWeight (golayEncodedMask (1038 : Fin 2048).val) / 4 : ℕ) = -1 := by
    have hw : ((golayMaskWeight (golayEncodedMask (1038 : Fin 2048).val) / 4 : ℕ) :
        ZMod 2) = 1 := by
      decide +kernel
    rw [hw]
    rfl
  have hs : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 / 2 := by
    have h : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith [h]
  have hl : (⟨(1038 : Fin 2048).val, by omega⟩ : Fin 4096) = 1038 := by decide +kernel
  have hd := monsterNortonTensorDeltaLow_source (1038 : Fin 2048) (0 : Fin 24)
  rw [hl] at hd
  rw [monsterNortonLine01TensorAfterV, monsterNortonIntegralTensorVector_first_column,
    monsterNortonUIntegerEmbed_single, monsterNortonTensorLift_apply,
    hd, hc, hp]
  simp only [Bool.false_eq_true, ite_false, one_smul, neg_one_smul,
    smul_smul, hs, ← sub_eq_add_neg, smul_sub]

/-- The fifteenth actual triality step is exactly the initial vector's first V image. -/
theorem monsterNortonLine01Fifteenth_actual :
    sExtra monsterNortonLine01FourteenthVector = monsterNortonLine01TensorAfterV := by
  rw [monsterNortonLine01FourteenthVector, map_sub, map_smul, map_smul,
    sExtra_XYZ_basis, sExtra_XYZ_basis, show trialityCycle 0 = 1 by decide +kernel,
    show trialityCycle 1 = 2 by decide +kernel, after_v_xyz]

private theorem involutive_action (g : ↥G) (h : g * g = 1) (x : GriessSpace) :
    g.val (g.val x) = x := by
  have hx := congrArg (fun k : ↥G => (G.subtype k) x) h
  rw [map_mul, map_one] at hx
  exact hx

/-- Literal Norton V returns this entire Griess state to the original nonzero tensor input. -/
theorem monsterNortonLine01Sixteenth_actual :
    y555NortonV.val monsterNortonLine01TensorAfterV = monsterNortonLine01TensorStart := by
  rw [← monsterNortonLine01TensorV_actual]
  apply involutive_action y555NortonV
  rw [← pow_two, y555NortonV_square]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
