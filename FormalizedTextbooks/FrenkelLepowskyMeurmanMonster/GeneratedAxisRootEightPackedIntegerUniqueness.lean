/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib

/-! Exact bounded integer digit identities for complete packed tensor certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxHeartbeats 8000000

/-- Every bounded natural packed word is the complete sum of all its original radix digits. -/
theorem generatedRootEight_packed_natural_digits (B w n : ℕ) :
    (∑ i : Fin n, (w / B ^ i.val % B) * B ^ i.val) = w % B ^ n := by
  induction n with
  | zero => simp only [Fin.sum_univ_zero, pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, pow_succ, Nat.mod_mul]
    ring

/-- A zero packed polynomial with every signed coefficient smaller than its radix has only zero digits. -/
theorem generatedRootEight_packed_integer_zero (B : ℤ) (hB : 0 < B)
    {n : ℕ} (f : Fin n → ℤ) (hb : ∀ i, |f i| < B)
    (h : ∑ i : Fin n, f i * B ^ i.val = 0) : ∀ i, f i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    let t : ℤ := ∑ i : Fin n, f i.succ * B ^ i.val
    have hp : f 0 + B * t = 0 := by
      rw [Fin.sum_univ_succ] at h
      simp only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one, pow_succ] at h
      have hs : (∑ i : Fin n, f i.succ * (B ^ i.val * B)) = B * t := by
        dsimp [t]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rwa [hs] at h
    have hd : B ∣ f 0 := by
      refine ⟨-t, ?_⟩
      nlinarith [hp]
    obtain ⟨k, hk⟩ := hd
    have hklt : |k| < 1 := by
      have hz := hb 0
      rw [hk, abs_mul, abs_of_pos hB] at hz
      nlinarith
    have hk0 : k = 0 := by
      have hz := abs_lt.mp hklt
      omega
    have hf0 : f 0 = 0 := by rw [hk, hk0, mul_zero]
    have ht : t = 0 := by
      rw [hf0, zero_add] at hp
      exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt hB)
    have hi := ih (fun i => f i.succ) (fun i => hb i.succ) ht
    exact Fin.cases hf0 hi

/-- Common integral scale permits the same exact uniqueness proof with larger original signed digits. -/
theorem generatedRootEight_packed_scaled_integer_zero (B G : ℤ) (hB : 0 < B) (hG : 0 < G)
    {n : ℕ} (f : Fin n → ℤ) (hd : ∀ i, G ∣ f i) (hb : ∀ i, |f i| < G * B)
    (h : ∑ i : Fin n, f i * B ^ i.val = 0) : ∀ i, f i = 0 := by
  choose k hk using hd
  have hbk : ∀ i, |k i| < B := by
    intro i
    have hz := hb i
    rw [hk i, abs_mul, abs_of_pos hG] at hz
    nlinarith
  have hp : G * (∑ i : Fin n, k i * B ^ i.val) = 0 := by
    rw [Finset.mul_sum]
    simp_rw [← mul_assoc, ← hk]
    exact h
  have hpk := (mul_eq_zero.mp hp).resolve_left (ne_of_gt hG)
  have hz := generatedRootEight_packed_integer_zero B hB k hbk hpk
  intro i
  rw [hk i, hz i, mul_zero]

/-- A complete zero low-bit mask certifies the original low bits of every radix digit. -/
theorem generatedRootEight_packed_gap_mask_digit (w m b q i : ℕ) (hqb : q ≤ b)
    (hm : (m / 2 ^ (b * i)) % 2 ^ q = 2 ^ q - 1) (hw : w &&& m = 0) :
    (w / 2 ^ (b * i) % 2 ^ b) % 2 ^ q = 0 := by
  have h := congrArg (fun x : ℕ => x / 2 ^ (b * i) % 2 ^ q) hw
  simp only [Nat.and_div_two_pow, Nat.and_mod_two_pow, hm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod, Nat.zero_div, Nat.zero_mod] at h
  have hd : 2 ^ q ∣ 2 ^ b := by
    refine ⟨2 ^ (b - q), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  rw [Nat.mod_mod_of_dvd _ hd]
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
