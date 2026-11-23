/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.StrongPseudoprime

/-!
# Strong pseudoprime bases are closed under powers and negation

Let `n` be a strong pseudoprime to a unit base `b` of `ZMod n`, with `n - 1 = 2 ^ k * d` and `d`
odd, so that `b ^ d = 1` or `b ^ (2 ^ i * d) = -1` for some `i < k`. The same `k` and `d` serve
for the bases `b ^ t` (`t : ℤ`) and `-b`.

* Powers. Put `y = b ^ d`, so that `(b ^ t) ^ (e * d) = (y ^ t) ^ e`. If `y = 1`, then
  `y ^ t = 1`. If `y ^ 2 ^ i = -1`, then `y ^ 2 ^ (i + 1) = 1`, so `y ^ t = y ^ m` for the residue
  `m` of `t` modulo `2 ^ (i + 1)`. Either `m = 0`, or `m = 2 ^ j * s` with `s` odd and `j ≤ i`,
  and then `(y ^ m) ^ 2 ^ (i - j) = (y ^ 2 ^ i) ^ s = -1`.
* Negation. As `d` is odd, `(-b) ^ d = -b ^ d`. If `b ^ d = 1`, then `(-b) ^ (2 ^ 0 * d) = -1`,
  where `0 < k` because `n - 1` is even. If `b ^ d = -1`, then `(-b) ^ d = 1`. If
  `b ^ (2 ^ i * d) = -1` with `0 < i`, the exponent is even and `(-b) ^ (2 ^ i * d) = -1`.
-/

namespace MetaMathlibExt

/-- **Strong pseudoprime bases are closed under powers and negation.** Let $n$ be a natural
number and $b$ a unit of $\mathbb{Z}/n\mathbb{Z}$ such that $n$ is a strong pseudoprime to the
base $b$. Then for every integer $t$, $n$ is a strong pseudoprime to the base $b^t$, and $n$ is a
strong pseudoprime to the base $-b$.

Requiring $b$ to be a unit loses nothing, since every strong pseudoprime base $b$ satisfies
$b^{n-1} = 1$; it also gives meaning to negative exponents.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 6 (`integers-2024-A23-thm-6`). -/
public theorem isStrongPseudoprime_zpow_and_neg {n : ℕ} {b : (ZMod n)ˣ}
    (h : IsStrongPseudoprime n (b : ZMod n)) (t : ℤ) :
    IsStrongPseudoprime n ((b ^ t : (ZMod n)ˣ) : ZMod n) ∧
      IsStrongPseudoprime n (-(b : ZMod n)) := by
  obtain ⟨hn, hcomp, hodd, k, d, hkd, hd, hb⟩ := h
  refine ⟨⟨hn, hcomp, hodd, k, d, hkd, hd, ?_⟩, ⟨hn, hcomp, hodd, k, d, hkd, hd, ?_⟩⟩
  · -- In the unit group, `(b ^ t) ^ (e * d) = (y ^ t) ^ e` with `y = b ^ d`.
    set y := b ^ d with hy
    have key : ∀ e : ℕ,
        ((b ^ t : (ZMod n)ˣ) : ZMod n) ^ (e * d) = (((y ^ t) ^ e : (ZMod n)ˣ) : ZMod n) := by
      intro e
      rw [← Units.val_pow_eq_pow_val, hy, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
        ← zpow_mul, ← zpow_mul, ← zpow_mul, Nat.cast_mul, mul_comm (d : ℤ), mul_assoc]
    rcases hb with hb | ⟨i, hi, hb⟩
    · left
      have hy1 : y = 1 := Units.ext (by rw [hy, Units.val_pow_eq_pow_val, hb, Units.val_one])
      rw [← one_mul d, key, hy1, one_zpow, one_pow, Units.val_one]
    · -- `y ^ 2 ^ i = -1`, so `y ^ 2 ^ (i + 1) = 1`.
      have hyi : y ^ 2 ^ i = -1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, hy, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, hb,
          Units.val_neg, Units.val_one])
      have hy1 : y ^ 2 ^ (i + 1) = 1 := by rw [pow_succ, pow_mul, hyi, neg_one_sq]
      -- Replace the integer exponent `t` by its residue `m` modulo `2 ^ (i + 1)`.
      have hpos : (0 : ℤ) < ((2 ^ (i + 1) : ℕ) : ℤ) := Int.natCast_pos.mpr (Nat.two_pow_pos _)
      have h0 : 0 ≤ t % ((2 ^ (i + 1) : ℕ) : ℤ) := Int.emod_nonneg _ hpos.ne'
      set m := (t % ((2 ^ (i + 1) : ℕ) : ℤ)).toNat with hm_def
      have hm : y ^ t = y ^ m := by
        rw [zpow_eq_zpow_emod' t hy1, ← Int.toNat_of_nonneg h0, zpow_natCast]
      have hmlt : m < 2 ^ (i + 1) := by
        have := Int.emod_lt_of_pos t hpos
        omega
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · left
        rw [← one_mul d, key, hm, hm0, pow_zero, one_pow, Units.val_one]
      · -- Write `m = 2 ^ j * s` with `s` odd; then `j ≤ i` and `(y ^ m) ^ 2 ^ (i - j) = -1`.
        right
        obtain ⟨j, s, hs, hms⟩ := Nat.exists_eq_two_pow_mul_odd hm0.ne'
        have hj : j ≤ i := by
          have : 2 ^ j < 2 ^ (i + 1) :=
            lt_of_le_of_lt (hms ▸ Nat.le_mul_of_pos_right _ hs.pos) hmlt
          exact Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp this)
        refine ⟨i - j, lt_of_le_of_lt (Nat.sub_le i j) hi, ?_⟩
        rw [key, hm, ← pow_mul, hms, show 2 ^ j * s * 2 ^ (i - j) = 2 ^ i * s by
          rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' hj], pow_mul, hyi,
          hs.neg_one_pow, Units.val_neg, Units.val_one]
  · -- `(-b) ^ d = -b ^ d` since `d` is odd.
    have hneg : (-(b : ZMod n)) ^ d = -(b : ZMod n) ^ d := hd.neg_pow _
    rcases hb with hb | ⟨i, hi, hb⟩
    · -- `0 < k`, since `n - 1` is even and `d` is odd.
      right
      have hk : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [pow_zero, one_mul] at hkd
          have heven := Nat.Odd.sub_odd hodd odd_one
          rw [hkd] at heven
          exact absurd heven (Nat.not_even_iff_odd.mpr hd)
        · exact hk
      exact ⟨0, hk, by rw [pow_zero, one_mul, hneg, hb]⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · left
        rw [pow_zero, one_mul] at hb
        rw [hneg, hb, neg_neg]
      · right
        refine ⟨i, hi, ?_⟩
        rw [Even.neg_pow ((Nat.even_pow.mpr ⟨even_two, hi0.ne'⟩).mul_right d), hb]

end MetaMathlibExt
