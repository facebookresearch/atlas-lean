/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Incomplete finite binomial sums of harmonic numbers

Statements from Richard Kollár, "Incomplete Finite Binomial Sums
of Harmonic Numbers", *Journal of Integer Sequences* 27 (2024),
Article 24.2.1
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Kollar/kollar6.html>).

Here `harmonic` is Mathlib's rational harmonic number.  The paper's
auxiliary sums are
`Cₙ = ∑ k ∈ [1,n], 1 / (k * 2 ^ k)` and
`Dₙ = ∑ k ∈ [1,n], (2k).choose k / ((2 * k) * 2 ^ (2 * k))`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

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

/-- **Kollár's recursion for incomplete binomial sums.** Let $(a_k)_{k \ge 0}$ be a sequence of
real numbers and let $m$ and $N$ be positive integers with $m \le N$. Then
$$\sum_{k=0}^{m} \binom{N}{k} a_k =
\sum_{k=0}^{m-1} \binom{N-1}{k} (a_k + a_{k+1}) + \binom{N-1}{m} a_m.$$

Source: Richard Kollár, "Incomplete Finite Binomial Sums of
Harmonic Numbers", Lemma 1. -/
theorem_wanted sum_range_choose_mul_eq_sum_range_choose_add
    (a : ℕ → ℝ) (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hmN : m ≤ N) :
    (∑ k ∈ Finset.range (m + 1), (N.choose k : ℝ) * a k) =
      (∑ k ∈ Finset.range m, ((N - 1).choose k : ℝ) * (a k + a (k + 1))) +
        ((N - 1).choose m : ℝ) * a m

/-- **Kollár's recursion for incomplete binomial sums with top index $2n-1$.** Let
$(a_k)_{k \ge 0}$ be a sequence of real numbers, let $n$ be a positive integer and let $m$ be a
natural number with $m \le n$. Then
$$\sum_{k=0}^{m} \binom{2n-1}{k} a_k =
\sum_{k=0}^{m} \binom{2n-2}{k} (a_k + a_{k+1}) - \binom{2n-2}{m} a_{m+1}.$$

Source: Richard Kollár, "Incomplete Finite Binomial Sums of
Harmonic Numbers", Corollary 2, equation `Lemma7`. -/
theorem_wanted sum_range_choose_two_mul_sub_one_mul_eq
    (a : ℕ → ℝ) (m n : ℕ) (hn : 0 < n) (hmn : m ≤ n) :
    (∑ k ∈ Finset.range (m + 1), ((2 * n - 1).choose k : ℝ) * a k) =
      (∑ k ∈ Finset.range (m + 1),
        ((2 * n - 2).choose k : ℝ) * (a k + a (k + 1))) -
        ((2 * n - 2).choose m : ℝ) * a (m + 1)

/-- **Kollár's recursion for incomplete binomial sums with top index $2n$.** Let
$(a_k)_{k \ge 0}$ be a sequence of real numbers and let $m$ and $n$ be positive integers with
$m \le n$. Then
$$\sum_{k=0}^{m} \binom{2n}{k} a_k =
\sum_{k=0}^{m-1} \binom{2n-1}{k} (a_k + a_{k+1}) + \binom{2n-1}{m} a_m.$$

Source: Richard Kollár, "Incomplete Finite Binomial Sums of
Harmonic Numbers", Corollary 2, equation `Lemma8`. -/
theorem_wanted sum_range_choose_two_mul_mul_eq
    (a : ℕ → ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n) :
    (∑ k ∈ Finset.range (m + 1), ((2 * n).choose k : ℝ) * a k) =
      (∑ k ∈ Finset.range m,
        ((2 * n - 1).choose k : ℝ) * (a k + a (k + 1))) +
        ((2 * n - 1).choose m : ℝ) * a m

/-- **Half-range binomial sum of harmonic numbers with top index $2n-1$.** Let $H_i$ denote
the $i$-th harmonic number (with $H_0 = 0$), and let Kollár's auxiliary sums be
$C_n = \sum_{k=1}^{n} \frac{1}{k \, 2^k}$ and
$D_n = \sum_{k=1}^{n} \frac{\binom{2k}{k}}{2k \cdot 2^{2k}}$.
For every positive integer $n$,
$$\sum_{i=0}^{n-1} \binom{2n-1}{i} H_i =
2^{2n-2} \left( H_{2n-1} - 2 C_{2n-1} + D_{n-1} \right).$$

Source: Richard Kollár, "Incomplete Finite Binomial Sums of
Harmonic Numbers", Theorem 3, equation `oddH`. -/
theorem_wanted sum_range_choose_two_mul_sub_one_mul_harmonic
    (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, ((2 * n - 1).choose i : ℚ) * harmonic i) =
      (2 : ℚ) ^ (2 * n - 2) *
        (harmonic (2 * n - 1) - 2 * invPowTwoSum (2 * n - 1) +
          centralBinomWeightedSum (n - 1))

/-- **Half-range binomial sum of harmonic numbers with top index $2n$.** Let $H_i$ denote
the $i$-th harmonic number (with $H_0 = 0$), and let Kollár's auxiliary sums be
$C_n = \sum_{k=1}^{n} \frac{1}{k \, 2^k}$ and
$D_n = \sum_{k=1}^{n} \frac{\binom{2k}{k}}{2k \cdot 2^{2k}}$.
For every positive integer $n$,
$$\sum_{i=0}^{n} \binom{2n}{i} H_i =
2^{2n-1} \left( H_{2n} - 2 C_{2n} + D_n \right) + \frac{1}{2} \binom{2n}{n} H_n.$$

Source: Richard Kollár, "Incomplete Finite Binomial Sums of
Harmonic Numbers", Theorem 3, equation `evenH`. -/
theorem_wanted sum_range_choose_two_mul_mul_harmonic
    (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range (n + 1), ((2 * n).choose i : ℚ) * harmonic i) =
      (2 : ℚ) ^ (2 * n - 1) *
          (harmonic (2 * n) - 2 * invPowTwoSum (2 * n) +
            centralBinomWeightedSum n) +
        (1 / 2 : ℚ) * ((2 * n).choose n : ℚ) * harmonic n

end MathlibExt.Combinatorics.Enumerative.IncompleteBinomialHarmonicSumsWanted
