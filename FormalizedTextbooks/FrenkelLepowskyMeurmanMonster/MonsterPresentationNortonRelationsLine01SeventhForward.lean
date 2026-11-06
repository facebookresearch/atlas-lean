/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Binding the complete seventh spin packets to their genuine next Norton U images. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhForwardBatch0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhForwardBatch1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhForwardBatch2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhForwardBatch3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SpinSupportTranslation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem xor_cancel (a b : Fin 4096) :
    monsterNortonBitXor (monsterNortonBitXor a b) b = a := by
  apply Fin.ext
  simp [monsterNortonBitXor, Nat.xor_assoc]

/-- All reached inverse coefficients are the actual seventh packet coefficients with exact scale. -/
theorem monsterNortonLine01SeventhForward_inverse_coefficients (i : Fin 16) (p : Fin 128) :
    8 * monsterNortonUCompactInverseNumerator (monsterNortonLine01SeventhForwardPacket i)
      (monsterNortonLine01TensorSpinLabel p) =
        -monsterNortonLine01TensorSeventhCoefficientLookup i p := by
  fin_cases i
  · exact monsterNortonLine01SeventhForward_inverse_batch0 0 p
  · exact monsterNortonLine01SeventhForward_inverse_batch0 1 p
  · exact monsterNortonLine01SeventhForward_inverse_batch0 2 p
  · exact monsterNortonLine01SeventhForward_inverse_batch0 3 p
  · exact monsterNortonLine01SeventhForward_inverse_batch1 0 p
  · exact monsterNortonLine01SeventhForward_inverse_batch1 1 p
  · exact monsterNortonLine01SeventhForward_inverse_batch1 2 p
  · exact monsterNortonLine01SeventhForward_inverse_batch1 3 p
  · exact monsterNortonLine01SeventhForward_inverse_batch2 0 p
  · exact monsterNortonLine01SeventhForward_inverse_batch2 1 p
  · exact monsterNortonLine01SeventhForward_inverse_batch2 2 p
  · exact monsterNortonLine01SeventhForward_inverse_batch2 3 p
  · exact monsterNortonLine01SeventhForward_inverse_batch3 0 p
  · exact monsterNortonLine01SeventhForward_inverse_batch3 1 p
  · exact monsterNortonLine01SeventhForward_inverse_batch3 2 p
  · exact monsterNortonLine01SeventhForward_inverse_batch3 3 p

/-- The actual inverse packet equality holds at all 4096 coordinates, including zeros. -/
theorem monsterNortonLine01SeventhForward_inverse_actual (i : Fin 16) (n : Fin 4096) :
    8 * monsterNortonUCompactInverseNumerator (monsterNortonLine01SeventhForwardPacket i) n =
      -monsterNortonLine01TensorSeventhPacket i n := by
  by_cases hn : monsterNortonLine01SpinSupport n
  · have he : monsterNortonLine01TensorSpinLabel
        (monsterNortonLine01CompactOutputLookup (monsterNortonBitXor n 1038)) = n := by
      unfold monsterNortonLine01TensorSpinLabel
      change monsterNortonBitXor _ 1038 = n
      rw [hn, xor_cancel]
    unfold monsterNortonLine01TensorSeventhPacket
    rw [ite_eq_left hn]
    conv_lhs => rw [← he]
    exact monsterNortonLine01SeventhForward_inverse_coefficients _ _
  · have ho : ¬ monsterNortonLine01CompactOutputSupport n :=
      fun h => hn ((monsterNortonLine01SpinSupport_output n).mpr h)
    unfold monsterNortonLine01TensorSeventhPacket
    rw [ite_eq_right hn, monsterNortonLine01SeventhForward_inverse_zero _ _ ho]
    ring

private theorem scalar_inverse (a b : ℝ) (h : (8 : ℝ) * a = -b) :
    (-1 / 8 : ℝ) * a = (1 / 64 : ℝ) * b := by
  linarith

/-- The actual inverse spin factor sends the proposed packet to the scaled seventh packet. -/
theorem monsterNortonLine01SeventhForward_spin_inverse (i : Fin 16) :
    (monsterNortonUFiber.val.1⁻¹).val
      (nortonUIntegerEmbed (monsterNortonLine01SeventhForwardPacket i)) =
        (1 / 64 : ℝ) • nortonUIntegerEmbed (monsterNortonLine01TensorSeventhPacket i) := by
  rw [monsterNortonUCompactInverseSpin_actual_embed]
  ext t
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed]
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (monsterNortonLine01SeventhForward_inverse_actual i (nortonUIntegerLabel t))
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_neg] at h
  exact scalar_inverse _ _ h

private theorem inverse_scaled_forward (e : SpinSpace ≃ₗ[ℝ] SpinSpace) (u v : SpinSpace)
    (h : e.symm u = (1 / 64 : ℝ) • v) : e v = (64 : ℝ) • u := by
  have hk := e.apply_symm_apply u
  rw [h, map_smul] at hk
  ext t
  have ht := congrFun hk t
  simp only [Pi.smul_apply, smul_eq_mul] at ht ⊢
  linarith

/-- The actual Norton spin factor sends each seventh packet to the checked forward packet. -/
theorem monsterNortonLine01SeventhForward_spin_actual (i : Fin 16) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed (monsterNortonLine01TensorSeventhPacket i)) =
      (64 : ℝ) • nortonUIntegerEmbed (monsterNortonLine01SeventhForwardPacket i) := by
  exact inverse_scaled_forward monsterNortonUFiber.val.1.val _ _
    (monsterNortonLine01SeventhForward_spin_inverse i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
