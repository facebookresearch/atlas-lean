/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp

/-!
# Even and odd binomial sums weighted by powers of two

Multiplying by `n + 1` shifts the binomial coefficients to row `n + 1`. Subtracting
the expansions of `(2 + 1)^(n + 1)` and `(2 - 1)^(n + 1)` isolates its odd terms.
-/

namespace MetaMathlibExt

open Finset

namespace sum_choose_even_two_pow_sub_div

private lemma sum_split (f : ℕ → ℚ) (n : ℕ) :
    ∑ j ∈ range (n + 2), f j = f 0 + (∑ k ∈ range (n / 2 + 1), f (2 * k + 1)) +
      ∑ k ∈ Icc 1 ((n + 1) / 2), f (2 * k) := by
  induction n with
  | zero => simp [sum_range_succ]
  | succ n ih =>
    rw [sum_range_succ _ (n + 2), ih]
    by_cases h : n % 2 = 0
    · rw [show (n + 1 + 1) / 2 = (n + 1) / 2 + 1 by omega,
        sum_Icc_succ_top (by omega), show n.succ / 2 = n / 2 by omega,
        show 2 * (n / 2 + 1) = n + 2 by omega]
      ac_rfl
    · rw [show (n + 1 + 1) / 2 = (n + 1) / 2 by omega,
        show n.succ / 2 = n / 2 + 1 by omega, sum_range_succ _ (n / 2 + 1),
        show 2 * (n / 2 + 1) + 1 = n + 2 by omega]
      ac_rfl

private lemma split_add_pow (x y : ℚ) (n : ℕ) :
    (x + y) ^ (n + 1) = y ^ (n + 1) +
      (∑ k ∈ range (n / 2 + 1),
        x ^ (2 * k + 1) * y ^ (n - 2 * k) * (n + 1).choose (2 * k + 1)) +
      ∑ k ∈ Icc 1 ((n + 1) / 2),
        x ^ (2 * k) * y ^ (n + 1 - 2 * k) * (n + 1).choose (2 * k) := by
  rw [add_pow, sum_split]
  simp

end sum_choose_even_two_pow_sub_div

open sum_choose_even_two_pow_sub_div

/-- **Even-index and odd-index binomial sums weighted by powers of $2$.** For every natural
number $n$,
$$\sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} \frac{2^{n-2k+1} - 2^{2k+1}}{2k+1} =
\sum_{k=1}^{\lceil n/2 \rceil} \binom{n}{2k-1} \frac{2^{2k-1}}{k}.$$

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 5 (`integers-2026-A19-prop-5`). -/
public theorem sum_choose_even_two_pow_sub_div (n : ℕ) :
    ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℚ) * (2 ^ (n + 1) / 2 ^ (2 * k) - 2 ^ (2 * k + 1)) / (2 * k + 1) =
      ∑ k ∈ Icc 1 ((n + 1) / 2), (n.choose (2 * k - 1) : ℚ) * 2 ^ (2 * k - 1) / k := by
  have plus := split_add_pow 1 2 n
  have minus := split_add_pow (-1) 2 n
  have swap := split_add_pow 2 1 n
  have sign (k : ℕ) : (-1 : ℚ) ^ (2 * k) = 1 := (even_two.mul_right k).neg_one_pow
  norm_num [pow_succ (-1 : ℚ), sign, sum_neg_distrib] at plus minus swap
  have shift (j : ℕ) : ((n : ℚ) + 1) * n.choose j =
      ((n + 1).choose (j + 1) : ℚ) * (j + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n j
  apply (mul_right_inj' (show (n : ℚ) + 1 ≠ 0 by positivity)).mp
  rw [mul_sum, mul_sum]
  have evenTerm (k : ℕ) (hk : k ∈ range (n / 2 + 1)) :
      ((n : ℚ) + 1) * ((n.choose (2 * k) : ℚ) *
        (2 ^ (n + 1) / 2 ^ (2 * k) - 2 ^ (2 * k + 1)) / (2 * k + 1)) =
      2 * (2 ^ (n - 2 * k) * ((n + 1).choose (2 * k + 1) : ℚ)) -
        2 ^ (2 * k + 1) * (n + 1).choose (2 * k + 1) := by
    have hle : 2 * k ≤ n := by
      have := mem_range.mp hk
      omega
    rw [mul_div_assoc', ← mul_assoc, shift, Nat.cast_mul, Nat.cast_ofNat]
    rw [pow_succ (2 : ℚ) n, pow_sub₀ _ two_ne_zero hle]
    field_simp
  have oddTerm (k : ℕ) (hk : k ∈ Icc 1 ((n + 1) / 2)) :
      ((n : ℚ) + 1) * ((n.choose (2 * k - 1) : ℚ) * 2 ^ (2 * k - 1) / k) =
        2 ^ (2 * k) * (n + 1).choose (2 * k) := by
    have hk' := (mem_Icc.mp hk).1
    have he : 2 * k - 1 + 1 = 2 * k := by omega
    have hp : (2 : ℚ) ^ (2 * k) = 2 ^ (2 * k - 1) * 2 := he ▸ pow_succ _ _
    rw [mul_div_assoc', ← mul_assoc, shift, he, ← Nat.cast_add_one, he, Nat.cast_mul,
      Nat.cast_ofNat, hp]
    field_simp
  rw [sum_congr rfl evenTerm, sum_congr rfl oddTerm, sum_sub_distrib, ← mul_sum]
  linarith only [plus, minus, swap]

end MetaMathlibExt
