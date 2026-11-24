/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

/-!
# An alternating binomial polynomial identity

After multiplication by `2 * (n + 1)`, both sums compute the difference
`(x + 1)^(n + 1) - (x - 1)^(n + 1)` by the binomial theorem.
-/

namespace MetaMathlibExt

open Finset

/-- **Alternating polynomial identity in $1 - x$ with weights $2^k/(k+1)$.** For every natural
number $n$ and every complex number $x$,
$$
\sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} \frac{2^k}{k+1} (1-x)^{n-k}
= \sum_{k=0}^{\lfloor n/2 \rfloor} \frac{1}{2k+1} \binom{n}{2k} x^{n-2k}.
$$

This is equation (45) of the source.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 4 (`integers-2026-A19-cor-4`). -/
public theorem sum_choose_two_pow_div_succ_one_sub_pow (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1), (-1) ^ (n - k) * (n.choose k : ℂ) * 2 ^ k / (k + 1) * (1 - x) ^ (n - k) =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℂ) / (2 * k + 1) * x ^ (n - 2 * k) := by
  have succ_ne (j : ℕ) : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have shift (j : ℕ) : ((n : ℂ) + 1) * ((n.choose j : ℂ) / (j + 1)) =
      ((n + 1).choose (j + 1) : ℂ) := by
    have h : ((n : ℂ) + 1) * (n.choose j : ℂ) =
        ((n + 1).choose (j + 1) : ℂ) * (j + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n j
    rw [mul_div_assoc', h, mul_div_cancel_right₀ _ (succ_ne j)]
  have two_ne : (2 : ℂ) ≠ 0 := by norm_num
  apply (mul_right_inj' (mul_ne_zero two_ne (succ_ne n))).mp
  calc
    _ = (x + 1) ^ (n + 1) - (x - 1) ^ (n + 1) := by
      -- Expand around `x - 1`; the constant term cancels.
      rw [show x + 1 = 2 + (x - 1) by ring, add_pow (2 : ℂ) (x - 1),
        sum_range_succ' _ (n + 1)]
      simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one,
        one_mul, mul_one, add_sub_cancel_right, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      calc
        _ = 2 ^ (k + 1) * ((-1 : ℂ) * (1 - x)) ^ (n - k) *
            (((n : ℂ) + 1) * ((n.choose k : ℂ) / (k + 1))) := by
          rw [pow_succ (2 : ℂ), mul_pow]
          ring
        _ = _ := by
          rw [shift, show (-1 : ℂ) * (1 - x) = x - 1 by ring, Nat.add_sub_add_right]
    _ = _ := by
      -- Subtract the expansions with increments `1` and `-1` to keep only the odd terms.
      have oddPart : (x + 1) ^ (n + 1) - (x - 1) ^ (n + 1) =
          ∑ j ∈ (range (n + 2)).filter Odd,
            2 * (x ^ (n + 1 - j) * ((n + 1).choose j : ℂ)) := by
        rw [add_comm x 1, show x - 1 = -1 + x by ring, add_pow, add_pow, ← sum_sub_distrib,
          sum_filter]
        refine sum_congr rfl fun j _ => ?_
        by_cases hj : Odd j
        · rw [ite_eq_left hj, hj.neg_one_pow, one_pow]
          ring
        · rw [ite_eq_right hj, (Nat.not_odd_iff_even.mp hj).neg_one_pow, one_pow, sub_self]
      rw [oddPart, mul_sum]
      symm
      refine sum_bij (fun k _ => 2 * k + 1) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [mem_filter, mem_range, Nat.odd_iff] at hk ⊢
        omega
      · intro k _ l _ h
        omega
      · intro j hj
        simp only [mem_filter, mem_range, Nat.odd_iff] at hj
        exact ⟨j / 2, mem_range.mpr (by omega), by omega⟩
      · intro k _
        have h := shift (2 * k)
        push_cast at h
        rw [mul_assoc, ← mul_assoc ((n : ℂ) + 1), h, Nat.add_sub_add_right]
        ac_rfl

end MetaMathlibExt
