/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPackedIntegerUniqueness

/-! Exact whole-word identities for the original sixteen signed nine-bit tensor slots. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxHeartbeats 8000000

/-- The original signed nine-bit digit of a complete packed word. -/
def generatedRootEightPackedSignedDigit (w : ℕ) (i : Fin 16) : ℤ :=
  let a := w / 512 ^ i.val % 512
  if a < 256 then (a : ℤ) else (a : ℤ) - 512

/-- All sixteen original sign bits, retained in their original positions. -/
def generatedRootEightPackedSignMask : ℕ := 11172193289283443295955271776512682085187840

/-- The original signed polynomial of all sixteen slots. -/
def generatedRootEightPackedSignedWord (w : ℕ) : ℤ :=
  (w : ℤ) - 2 * ((w &&& generatedRootEightPackedSignMask : ℕ) : ℤ)

private theorem sign_mask_digits : ∀ i : Fin 16,
    generatedRootEightPackedSignMask / 512 ^ i.val % 512 = 256 := by
  decide +kernel

private theorem signed_digit_identity : ∀ a : Fin 512,
    (if a.val < 256 then (a.val : ℤ) else (a.val : ℤ) - 512) =
      (a.val : ℤ) - 2 * ((a.val &&& 256 : ℕ) : ℤ) := by
  decide +kernel

/-- Original sign-mask extraction commutes with every original radix digit. -/
theorem generatedRootEight_packed_signed_mask_digit (w : ℕ) (i : Fin 16) :
    (w &&& generatedRootEightPackedSignMask) / 512 ^ i.val % 512 =
      (w / 512 ^ i.val % 512) &&& 256 := by
  have h := sign_mask_digits i
  have hp : 512 ^ i.val = 2 ^ (9 * i.val) := by
    rw [pow_mul]; norm_num
  rw [hp, Nat.and_div_two_pow]
  change (_ &&& _) % 2 ^ 9 = _
  rw [Nat.and_mod_two_pow]
  simpa only [← hp] using congrArg (fun a => (w / 512 ^ i.val % 512) &&& a) h

/-- The whole signed word is exactly the polynomial of every original signed coordinate. -/
theorem generatedRootEight_packed_signed_word (w : ℕ) (hw : w < 512 ^ 16) :
    (∑ i : Fin 16, generatedRootEightPackedSignedDigit w i * (512 : ℤ) ^ i.val) =
      generatedRootEightPackedSignedWord w := by
  have hn := generatedRootEight_packed_natural_digits 512 w 16
  rw [Nat.mod_eq_of_lt hw] at hn
  have hm := generatedRootEight_packed_natural_digits 512 (w &&& generatedRootEightPackedSignMask) 16
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left hw)] at hm
  have hnc := congrArg (fun n : ℕ => (n : ℤ)) hn
  have hmc := congrArg (fun n : ℕ => (n : ℤ)) hm
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hnc hmc
  unfold generatedRootEightPackedSignedDigit generatedRootEightPackedSignedWord
  simp_rw [signed_digit_identity ⟨_, Nat.mod_lt _ (by decide)⟩,
    ← generatedRootEight_packed_signed_mask_digit, sub_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simpa only [hnc, hmc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
