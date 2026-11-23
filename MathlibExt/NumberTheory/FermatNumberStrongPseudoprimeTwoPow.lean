/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Fermat
public import MathlibExt.NumberTheory.StrongPseudoprime

/-!
# Composite Fermat numbers are strong pseudoprimes to every power of two

Let `F = Nat.fermatNumber k = 2 ^ 2 ^ k + 1` be composite. Then `F - 1 = 2 ^ 2 ^ k * 1`, and
`2 ^ 2 ^ k = -1` in `ZMod F`, so the unit `2` has order dividing `2 ^ (k + 1)`. Reduce the
exponent `t` modulo `2 ^ (k + 1)` to a natural number `m`. If `m = 0`, the base is `1`.
Otherwise write `m = 2 ^ j * s` with `s` odd, so that `j ≤ k`; then
`(2 ^ m) ^ 2 ^ (k - j) = (2 ^ 2 ^ k) ^ s = -1` with `k - j < 2 ^ k`.
-/

namespace MetaMathlibExt

/-- **Composite Fermat numbers are strong pseudoprimes to every power of $2$.** Let $k$ be a
natural number such that the Fermat number $F_k = 2^{2^k} + 1$ is composite. Then for every
integer $t$, $F_k$ is a strong pseudoprime to the base $2^t$, where the power is taken in the
unit group of $\mathbb{Z}/F_k\mathbb{Z}$ (in which $2$ is a unit because $F_k$ is odd).

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 5 (`integers-2024-A23-cor-5`). -/
public theorem fermatNumber_isStrongPseudoprime_two_zpow {k : ℕ}
    (hk : ¬(Nat.fermatNumber k).Prime) (u : (ZMod (Nat.fermatNumber k))ˣ)
    (hu : (u : ZMod (Nat.fermatNumber k)) = 2) (t : ℤ) :
    IsStrongPseudoprime (Nat.fermatNumber k) ((u ^ t : (ZMod (Nat.fermatNumber k))ˣ) : ZMod _) := by
  -- `F_k = 2 ^ 2 ^ k + 1` vanishes in `ZMod F_k`, so `2 ^ 2 ^ k = -1` there.
  have h2 : (2 : ZMod (Nat.fermatNumber k)) ^ 2 ^ k = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast ZMod.natCast_self (Nat.fermatNumber k)
  have hu1 : u ^ 2 ^ (k + 1) = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, hu, pow_succ, pow_mul, h2, neg_one_sq, Units.val_one]
  -- Replace the integer exponent `t` by its residue `m` modulo `2 ^ (k + 1)`.
  have h0 : 0 ≤ t % ((2 ^ (k + 1) : ℕ) : ℤ) := Int.emod_nonneg _ (by positivity)
  set m := (t % ((2 ^ (k + 1) : ℕ) : ℤ)).toNat with hm_def
  have hm : u ^ t = u ^ m := by
    rw [zpow_eq_zpow_emod' t hu1, ← Int.toNat_of_nonneg h0, zpow_natCast]
  have hmlt : m < 2 ^ (k + 1) := by
    have := Int.emod_lt_of_pos t (show (0 : ℤ) < ((2 ^ (k + 1) : ℕ) : ℤ) by positivity)
    omega
  -- `F_k - 1 = 2 ^ 2 ^ k * 1`, so the odd part is `d = 1`.
  refine ⟨by have := Nat.three_le_fermatNumber k; omega, hk, Nat.odd_fermatNumber k, 2 ^ k, 1,
    by simp [Nat.fermatNumber], odd_one, ?_⟩
  rw [hm, Units.val_pow_eq_pow_val, hu, pow_one]
  rcases Nat.eq_zero_or_pos m with h | h
  · exact Or.inl (by rw [h, pow_zero])
  · -- Write `m = 2 ^ j * s` with `s` odd; then `j ≤ k` and `(2 ^ m) ^ 2 ^ (k - j) = -1`.
    right
    obtain ⟨j, s, hs, hms⟩ := Nat.exists_eq_two_pow_mul_odd h.ne'
    have hj : j ≤ k := by
      have : 2 ^ j < 2 ^ (k + 1) := lt_of_le_of_lt (hms ▸ Nat.le_mul_of_pos_right _ hs.pos) hmlt
      exact Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by norm_num)).mp this)
    refine ⟨k - j, lt_of_le_of_lt (Nat.sub_le k j) Nat.lt_two_pow_self, ?_⟩
    rw [mul_one, ← pow_mul, hms, show 2 ^ j * s * 2 ^ (k - j) = 2 ^ k * s by
      rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' hj], pow_mul, h2, hs.neg_one_pow]

end MetaMathlibExt
