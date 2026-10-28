/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Column-xor evaluation of the actual compact binary permutation matrices. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseParity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseLabels

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The twelve integer column masks of each actual compact binary permutation. -/
def monsterNortonUCompactBitColumns : Fin 2 → Fin 12 → ℕ :=
  ![![0x5bb, 0xc01, 0xc0f, 0x52, 0x752, 0x58a, 0x427, 0x172, 0x941, 0xd1f, 0xdb4, 0xcb5],
    ![0x409, 0xeaa, 0x2b4, 0x10, 0x7e8, 0x20, 0x40, 0x80, 0x100, 0x200, 0x400, 0x800]]

/-- The actual binary permutation evaluated through twelve selected column xors. -/
def monsterNortonUCompactColumnPermutation (k : Fin 2) (n : Fin 4096) : Fin 4096 :=
  ⟨((if n.val.testBit 0 then monsterNortonUCompactBitColumns k 0 else 0) ^^^
    (if n.val.testBit 1 then monsterNortonUCompactBitColumns k 1 else 0) ^^^
    (if n.val.testBit 2 then monsterNortonUCompactBitColumns k 2 else 0) ^^^
    (if n.val.testBit 3 then monsterNortonUCompactBitColumns k 3 else 0) ^^^
    (if n.val.testBit 4 then monsterNortonUCompactBitColumns k 4 else 0) ^^^
    (if n.val.testBit 5 then monsterNortonUCompactBitColumns k 5 else 0) ^^^
    (if n.val.testBit 6 then monsterNortonUCompactBitColumns k 6 else 0) ^^^
    (if n.val.testBit 7 then monsterNortonUCompactBitColumns k 7 else 0) ^^^
    (if n.val.testBit 8 then monsterNortonUCompactBitColumns k 8 else 0) ^^^
    (if n.val.testBit 9 then monsterNortonUCompactBitColumns k 9 else 0) ^^^
    (if n.val.testBit 10 then monsterNortonUCompactBitColumns k 10 else 0) ^^^
    (if n.val.testBit 11 then monsterNortonUCompactBitColumns k 11 else 0)) % 4096,
    Nat.mod_lt _ (by norm_num)⟩

private def bin (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem bin_xor (a b : Bool) : bin (Bool.xor a b) = bin a + bin b := by
  cases a <;> cases b <;> decide

private theorem selected_bit (n : Fin 4096) (m : ℕ) (j : ℕ) (i : Fin 12) :
    bin ((if n.val.testBit j then m else 0).testBit i.val) =
      bin (n.val.testBit j) * bin (m.testBit i.val) := by
  cases h : n.val.testBit j <;> simp [bin]

private theorem columns_actual (k : Fin 2) (i j : Fin 12) :
    (monsterNortonUCompactPermutationRows k i).testBit j.val =
      (monsterNortonUCompactBitColumns k j).testBit i.val := by
  revert k i j
  decide +kernel

set_option maxHeartbeats 1000000 in
-- Expand the twelve packed column terms before identifying their binary matrix coefficients.
/-- The column-xor evaluator is exactly the actual permutation on every spin label. -/
theorem monsterNortonUCompactColumnPermutation_actual (k : Fin 2) (n : Fin 4096) :
    nortonUIntegerLabel (monsterNortonUCompactPermutation k (golayLabelCoefficients n)) =
      monsterNortonUCompactColumnPermutation k n := by
  apply golayLabelCoefficients_injective
  rw [nortonUIntegerLabel_inverse]
  funext i
  rw [monsterNortonUCompactPermutation_apply, Matrix.mulVec, dotProduct]
  change (∑ j : Fin 12, bin ((monsterNortonUCompactPermutationRows k i).testBit j.val) *
    bin (n.val.testBit j.val)) = bin
      ((((if n.val.testBit 0 then monsterNortonUCompactBitColumns k 0 else 0) ^^^
    (if n.val.testBit 1 then monsterNortonUCompactBitColumns k 1 else 0) ^^^
    (if n.val.testBit 2 then monsterNortonUCompactBitColumns k 2 else 0) ^^^
    (if n.val.testBit 3 then monsterNortonUCompactBitColumns k 3 else 0) ^^^
    (if n.val.testBit 4 then monsterNortonUCompactBitColumns k 4 else 0) ^^^
    (if n.val.testBit 5 then monsterNortonUCompactBitColumns k 5 else 0) ^^^
    (if n.val.testBit 6 then monsterNortonUCompactBitColumns k 6 else 0) ^^^
    (if n.val.testBit 7 then monsterNortonUCompactBitColumns k 7 else 0) ^^^
    (if n.val.testBit 8 then monsterNortonUCompactBitColumns k 8 else 0) ^^^
    (if n.val.testBit 9 then monsterNortonUCompactBitColumns k 9 else 0) ^^^
    (if n.val.testBit 10 then monsterNortonUCompactBitColumns k 10 else 0) ^^^
    (if n.val.testBit 11 then monsterNortonUCompactBitColumns k 11 else 0)) % 4096).testBit i.val)
  rw [Nat.testBit_mod_two_pow _ 12 i.val]
  have hi : decide (i.val < 12) = true := decide_eq_true_eq.mpr i.isLt
  simp only [hi, Bool.true_and]
  simp_rw [Nat.testBit_xor, bin_xor]
  simp_rw [selected_bit]
  simp_rw [columns_actual]
  norm_num [Fin.sum_univ_succ]
  ring

/-- Both proved evaluators describe exactly the same actual binary permutation. -/
theorem monsterNortonUCompactRow_eq_column (k : Fin 2) (n : Fin 4096) :
    monsterNortonUCompactBitPermutation k n = monsterNortonUCompactColumnPermutation k n :=
  (monsterNortonUCompactBitPermutation_actual k n).symm.trans
    (monsterNortonUCompactColumnPermutation_actual k n)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
