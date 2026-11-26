/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Basic
import MathlibExt.Combinatorics.Enumerative.AlzerRichardsBernoulliSum

/-!
# Vanishing alternating Stirling sums

The Alzer–Richards vanishing identity follows by comparing two consecutive
binomial-weighted sums for the same Bernoulli number.
-/

namespace MetaMathlibExt

open Finset

/-- **Vanishing alternating Stirling sums with $\binom{r+m}{k}$.** Write $S(n, k)$ for the
Stirling numbers of the second kind. For every natural number $m \ge 1$ and every natural number
$r$,
$$
\sum_{k=0}^{r+m} (-1)^k \frac{\binom{r+m}{k}}{\binom{r+k}{k}} S(r+k, k) = 0.
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 3, Equation (5). -/
public theorem sum_choose_div_choose_mul_stirlingSecond_eq_zero {m : ℕ} (hm : 1 ≤ m)
    (r : ℕ) :
    ∑ k ∈ range (r + m + 1), (-1 : ℚ) ^ k *
        (((r + m).choose k : ℚ) / ((r + k).choose k : ℚ)) *
          (Nat.stirlingSecond (r + k) k : ℚ) = 0 := by
  let n := r + (m - 1)
  have hnm : r + m = n + 1 := by dsimp [n]; omega
  have hr : r ≤ n := Nat.le_add_right _ _
  let term (a k : ℕ) : ℚ :=
    (-1 : ℚ) ^ k * ((a : ℚ) / ((r + k).choose k : ℚ)) * (Nat.stirlingSecond (r + k) k : ℚ)
  have hLower : ∑ k ∈ range (n + 1), term ((n + 1).choose (k + 1)) k = bernoulli r :=
    (sum_choose_div_choose_mul_stirlingSecond_eq_bernoulli n).1 r hr
  have hUpper : ∑ k ∈ range (n + 1 + 1), term ((n + 1 + 1).choose (k + 1)) k = bernoulli r :=
    (sum_choose_div_choose_mul_stirlingSecond_eq_bernoulli (n + 1)).1 r (Nat.le_succ_of_le hr)
  have hPascal (k : ℕ) : term ((n + 1 + 1).choose (k + 1)) k =
      term ((n + 1).choose k) k + term ((n + 1).choose (k + 1)) k := by
    rw [Nat.choose_succ_succ' (n + 1) k]
    simp only [term, Nat.cast_add, add_div, mul_add, add_mul]
  have hsum :
      (∑ k ∈ range (n + 1 + 1), term ((n + 1 + 1).choose (k + 1)) k) =
        (∑ k ∈ range (n + 1 + 1), term ((n + 1).choose k) k) +
          ∑ k ∈ range (n + 1), term ((n + 1).choose (k + 1)) k := by
    -- The endpoint has coefficient one in both long sums; Pascal splits the other terms.
    rw [sum_range_succ _ (n + 1), sum_range_succ _ (n + 1)]
    simp only [Nat.choose_self, hPascal, sum_add_distrib]
    ac_rfl
  rw [hUpper, hLower] at hsum
  rw [hnm]
  change (∑ k ∈ range (n + 1 + 1), term ((n + 1).choose k) k) = 0
  exact add_right_cancel (hsum.symm.trans (zero_add _).symm)

end MetaMathlibExt
