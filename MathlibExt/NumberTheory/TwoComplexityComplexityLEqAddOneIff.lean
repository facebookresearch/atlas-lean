/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TwoComplexity
import MathlibExt.NumberTheory.TwoComplexityComplexityLPowAddPow

/-!
# Even integers of 2-complexity one above the lower exponent

For natural numbers $m \ge 1$ and even $n$ with $2^m < n \le 2^{m+1}$, the 2-complexity of $n$
is $m+1$ exactly when $n = 2^m + 2^t$ for some $1 \le t \le m$. The endpoint $n = 2^{m+1}$
is included by taking $t = m$.

The independently proved lower bound for numbers not expressible as a sum of two powers forces
the forward representation. The interval fixes the larger exponent, and evenness excludes
exponent zero. The reverse direction uses the complexity formula for a sum of two powers.

## References

* Pengcheng Zhang, *The 2-Complexity of Even Positive Integers*, INTEGERS 24 (2024),
  Article A109, pp. 1–11, Proposition 3 and Theorem 1(1); the proof uses Corollaries 1 and 2.
  <https://math.colgate.edu/~integers/vol24.html>
* ATLAS: `MathlibExt.NumberTheory.TwoComplexity` (`logb_two_add_one_le`) and
  `MathlibExt.NumberTheory.TwoComplexityComplexityLPowAddPow` (`complexityL_pow_add_pow`).
-/

set_option autoImplicit false

public section

namespace MathlibExt.NumberTheory.TwoComplexityWanted

/-- **Even $n$ with $2^m < n \le 2^{m+1}$ and 2-complexity $m + 1$.** Write $\|n\|_2$ for the
2-complexity of $n$. Let $m \ge 1$ and let $n$ be an even natural number with
$2^m < n \le 2^{m+1}$. Then $\|n\|_2 = m + 1$ if and only if $n = 2^m + 2^t$ for some natural
number $t$ with $1 \le t \le m$.

The case $t = m$ gives $n = 2^{m+1}$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 3 and Theorem 1. -/
theorem complexityL_eq_add_one_iff (m n : ℕ)
    (hm : 1 ≤ m) (h2n : 2 ∣ n) (hn1 : 2 ^ m < n)
    (hn2 : n ≤ 2 ^ (m + 1)) :
    complexityL 2 n = m + 1 ↔
      ∃ t : ℕ, 1 ≤ t ∧ t ≤ m ∧ n = 2 ^ m + 2 ^ t := by
  constructor
  · intro hc
    have hsum : ∃ a b : ℕ, a ≤ b ∧ n = 2 ^ a + 2 ^ b := by
      by_contra hnone
      have hbound := logb_two_add_one_le n h2n (by omega) hnone
      have hlog : (m : ℝ) < Real.logb 2 (n : ℝ) := by
        calc
          (m : ℝ) = Real.logb 2 ((2 : ℝ) ^ m) := by
            rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
          _ < Real.logb 2 (n : ℝ) :=
            Real.logb_lt_logb (by norm_num) (by positivity) (by exact_mod_cast hn1)
      rw [hc, Nat.cast_add, Nat.cast_one] at hbound
      linarith only [hlog, hbound]
    obtain ⟨a, b, hab, hn⟩ := hsum
    -- The sum lies in the interval with lower exponent b as well as the one with exponent m.
    have hlow : 2 ^ b < n := by
      rw [hn]
      exact Nat.lt_add_of_pos_left (Nat.two_pow_pos a)
    have hupp : n ≤ 2 ^ (b + 1) := by
      rw [hn, pow_succ, mul_two]
      exact Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hab) _
    have htwo : 1 < (2 : ℕ) := by decide
    have hmb := (Nat.pow_lt_pow_iff_right htwo).mp (hn1.trans_le hupp)
    have hbm := (Nat.pow_lt_pow_iff_right htwo).mp (hlow.trans_le hn2)
    have hb : b = m := by omega
    subst b
    have ha : 1 ≤ a := by
      by_contra h
      have ha : a = 0 := by omega
      have hd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
      rw [hn, ha, pow_zero] at h2n
      omega
    exact ⟨a, ha, hab, hn.trans (add_comm _ _)⟩
  · rintro ⟨t, ht, htm, rfl⟩
    exact complexityL_pow_add_pow 2 m t (by decide) htm ht

end MathlibExt.NumberTheory.TwoComplexityWanted
