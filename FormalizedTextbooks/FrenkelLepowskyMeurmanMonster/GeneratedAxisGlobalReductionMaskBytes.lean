/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskXor

public import Mathlib.Tactic.NormNum

/-! Exact decomposition of column action into bounded byte lookups. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Splitting the low bits from the shifted quotient is exact mask addition. -/
theorem generatedAxisGlobalMask_split (b n : ℕ) :
    b = (b % 2 ^ n) ^^^ ((b / 2 ^ n) <<< n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    Nat.testBit_div_two_pow]
  by_cases hi : i < n
  · simp [hi, show ¬n ≤ i by omega]
  · have hn : n ≤ i := by omega
    simp [hi, hn, Nat.sub_add_cancel hn]

/-- Every mask is exactly its three low bytes and its remaining high bits. -/
theorem generatedAxisGlobalMask_three_bytes (b : ℕ) :
    b = (b % 256) ^^^ (((b / 256) % 256) <<< 8) ^^^ ((b / 65536) <<< 16) := by
  have h := generatedAxisGlobalMask_split b 8
  have h' := generatedAxisGlobalMask_split (b / 256) 8
  norm_num only [show 2 ^ 8 = (256 : ℕ) by decide] at h h'
  rw [h'] at h
  have hs (a : ℕ) : (a <<< 8) <<< 8 = a <<< 16 := by
    norm_num [Nat.shiftLeft_eq, Nat.mul_assoc]
  rw [Nat.shiftLeft_xor_distrib, hs] at h
  rw [Nat.div_div_eq_div_mul] at h
  norm_num only [show 256 * 256 = (65536 : ℕ) by decide] at h
  exact h.trans (Nat.xor_assoc _ _ _).symm

/-- Ordinary row action is the XOR of the three exact byte actions. -/
theorem generatedAxisGlobalMaskRowsAction_three_bytes (rows : List (ℕ × ℕ)) (b : ℕ) :
    generatedAxisGlobalMaskRowsAction rows b =
      generatedAxisGlobalMaskRowsAction rows (b % 256) ^^^
        generatedAxisGlobalMaskRowsAction rows (((b / 256) % 256) <<< 8) ^^^
          generatedAxisGlobalMaskRowsAction rows ((b / 65536) <<< 16) := by
  conv_lhs => rw [generatedAxisGlobalMask_three_bytes b]
  rw [generatedAxisGlobalMaskRowsAction_xor, generatedAxisGlobalMaskRowsAction_xor]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
