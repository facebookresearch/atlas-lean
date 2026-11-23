/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-! # Kollár's incomplete binomial sums -/

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.IncompleteBinomialHarmonicSumsWanted

/-- **Kollár's auxiliary sum $C_n$.** For a natural number $n$, $C_n$ is the rational number
$C_n = \sum_{k=1}^{n} \frac{1}{k \, 2^k}$. -/
def invPowTwoSum (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k * 2 ^ k)

/-- **Kollár's auxiliary sum $D_n$.** For a natural number $n$, $D_n$ is the rational number
$D_n = \sum_{k=1}^{n} \frac{\binom{2k}{k}}{2k \cdot 2^{2k}}$. -/
def centralBinomWeightedSum (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n,
    ((2 * k).choose k : ℚ) / ((2 * k : ℚ) * 2 ^ (2 * k))

/-- **Kollár's recursion for incomplete binomial sums with top index $2n-1$.** Let
$(a_k)_{k \ge 0}$ be a sequence of real numbers, let $n$ be a positive integer and let $m$ be a
natural number with $m \le n$. Then
$$\sum_{k=0}^{m} \binom{2n-1}{k} a_k =
\sum_{k=0}^{m} \binom{2n-2}{k} (a_k + a_{k+1}) - \binom{2n-2}{m} a_{m+1}.$$

Source: Richard Kollár, "Incomplete Finite Binomial Sums of
Harmonic Numbers", Corollary 2, equation `Lemma7`. -/
theorem sum_range_choose_two_mul_sub_one_mul_eq
    (a : ℕ → ℝ) (m n : ℕ) (hn : 0 < n) (hmn : m ≤ n) :
    (∑ k ∈ Finset.range (m + 1), ((2 * n - 1).choose k : ℝ) * a k) =
      (∑ k ∈ Finset.range (m + 1),
        ((2 * n - 2).choose k : ℝ) * (a k + a (k + 1))) -
        ((2 * n - 2).choose m : ℝ) * a (m + 1) := by
  rw [show 2 * n - 1 = (2 * n - 2) + 1 by omega]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ _ (m + 1), ih (Nat.le_of_succ_le hmn),
      Finset.sum_range_succ _ (m + 1), Nat.choose_succ_succ', Nat.cast_add]
    ring

end MathlibExt.Combinatorics.Enumerative.IncompleteBinomialHarmonicSumsWanted
