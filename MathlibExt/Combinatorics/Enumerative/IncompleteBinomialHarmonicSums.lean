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
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Kollár's incomplete binomial sums

Pascal's rule gives recursions for partial binomial sums and closed forms for the
harmonic-weighted first half of both odd and even rows.
-/

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

-- `hm` and `hmN` are part of the source statement but are not needed: the identity holds for
-- every cutoff `m` as soon as `N` is positive.
set_option linter.unusedVariables false in
/-- **Kollár's recursion for incomplete binomial sums.** Let $(a_k)_{k \ge 0}$ be a sequence of
real numbers and let $m$ and $N$ be positive integers with $m \le N$. Then
$$\sum_{k=0}^{m} \binom{N}{k} a_k =
\sum_{k=0}^{m-1} \binom{N-1}{k} (a_k + a_{k+1}) + \binom{N-1}{m} a_m.$$

Source: Richard Kollár, "Incomplete Finite Binomial Sums of
Harmonic Numbers", Lemma 1. -/
theorem sum_range_choose_mul_eq_sum_range_choose_add
    (a : ℕ → ℝ) (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hmN : m ≤ N) :
    (∑ k ∈ Finset.range (m + 1), (N.choose k : ℝ) * a k) =
      (∑ k ∈ Finset.range m, ((N - 1).choose k : ℝ) * (a k + a (k + 1))) +
        ((N - 1).choose m : ℝ) * a m := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_one.mpr hN
  rw [Nat.add_sub_cancel]
  -- Drop the unused bounds on `m` so that the induction hypothesis is unconditional.
  clear hm hmN
  induction m with
  | zero => simp
  | succ m ih =>
    -- Split off the last term on both sides and apply Pascal's rule to `(M + 1).choose (m + 1)`.
    rw [Finset.sum_range_succ _ (m + 1), ih, Finset.sum_range_succ _ m, Nat.choose_succ_succ',
      Nat.cast_add]
    ring

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

/-- **Kollár's recursion for incomplete binomial sums with top index $2n$.** Let
$(a_k)_{k \ge 0}$ be a sequence of real numbers and let $m$ and $n$ be positive integers with
$m \le n$. Then
$$\sum_{k=0}^{m} \binom{2n}{k} a_k =
\sum_{k=0}^{m-1} \binom{2n-1}{k} (a_k + a_{k+1}) + \binom{2n-1}{m} a_m.$$

Source: Richard Kollár, "Incomplete Finite Binomial Sums of
Harmonic Numbers", Corollary 2, equation `Lemma8`. -/
theorem sum_range_choose_two_mul_mul_eq
    (a : ℕ → ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n) :
    (∑ k ∈ Finset.range (m + 1), ((2 * n).choose k : ℝ) * a k) =
      (∑ k ∈ Finset.range m,
        ((2 * n - 1).choose k : ℝ) * (a k + a (k + 1))) +
        ((2 * n - 1).choose m : ℝ) * a m := by
  exact sum_range_choose_mul_eq_sum_range_choose_add a m (2 * n) hm
    (Nat.mul_pos (by decide) hn) (by omega)

open Finset

private def binomSum (N m : ℕ) : ℚ := ∑ i ∈ range m, (N.choose i : ℚ)

private def harmonicSum (N m : ℕ) : ℚ := ∑ i ∈ range m, (N.choose i : ℚ) * harmonic i

private theorem binomSum_succ (N m : ℕ) :
    binomSum N (m + 1) = binomSum N m + N.choose m :=
  sum_range_succ ..

private theorem harmonicSum_succ (N m : ℕ) :
    harmonicSum N (m + 1) = harmonicSum N m + N.choose m * harmonic m :=
  sum_range_succ ..

private theorem binomSum_pascal (N m : ℕ) :
    binomSum (N + 1) (m + 1) = binomSum N (m + 1) + binomSum N m := by
  induction m with
  | zero => simp [binomSum]
  | succ m ih =>
    rw [binomSum_succ (N + 1), ih, binomSum_succ N (m + 1), binomSum_succ N m,
      Nat.choose_succ_succ', Nat.cast_add]
    ring

-- Pascal's rule leaves the increment H_{i+1} - H_i. Binomial absorption
-- converts its coefficient into the next row divided by N + 1.
private theorem harmonicSum_pascal (N m : ℕ) :
    harmonicSum (N + 1) (m + 1) = harmonicSum N (m + 1) + harmonicSum N m +
      (binomSum (N + 1) (m + 1) - 1) / (N + 1) := by
  induction m with
  | zero => simp [harmonicSum, binomSum]
  | succ m ih =>
    rw [harmonicSum_succ (N + 1), ih, harmonicSum_succ N (m + 1), harmonicSum_succ N m,
      binomSum_succ (N + 1) (m + 1)]
    have habs : (N.choose m : ℚ) * (↑(m + 1 : ℕ) : ℚ)⁻¹ =
        ((N + 1).choose (m + 1) : ℚ) / (N + 1) := by
      rw [← div_eq_mul_inv, div_eq_div_iff (by positivity) (by positivity), mul_comm]
      exact_mod_cast Nat.add_one_mul_choose_eq N m
    simp only [Nat.choose_succ_succ', harmonic_succ, Nat.cast_add, Nat.cast_one] at habs ⊢
    linear_combination habs

private theorem odd_row_step (n : ℕ) :
    harmonicSum (2 * n + 3) (n + 2) = 4 * harmonicSum (2 * n + 1) (n + 1) +
      ((2 : ℚ) ^ (2 * (n + 1)) + (2 * (n + 1)).choose (n + 1) - 2) / (2 * (n + 1)) +
      (2 ^ (2 * (n + 1)) - 1) / (2 * (n + 1) + 1) := by
  have hodd : binomSum (2 * n + 3) (n + 2) = (2 : ℚ) ^ (2 * (n + 1)) := by
    rw [pow_mul]
    change binomSum (2 * (n + 1) + 1) ((n + 1) + 1) = 4 ^ (n + 1)
    unfold binomSum
    exact_mod_cast Nat.sum_range_choose_halfway (n + 1)
  -- The even half-row includes its central term. Doubling counts that term twice.
  have heven : 2 * binomSum (2 * n + 2) (n + 2) =
      2 ^ (2 * (n + 1)) + (2 * (n + 1)).choose (n + 1) := by
    have hrow := binomSum_pascal (2 * n + 2) (n + 1)
    rw [hodd] at hrow
    linear_combination binomSum_succ (2 * n + 2) (n + 1) - hrow
  -- Combining two Pascal steps cancels the central coefficient of the harmonic number.
  have hcenter : ((2 * n + 2).choose (n + 1) : ℚ) = 2 * (2 * n + 1).choose (n + 1) := by
    rw [Nat.choose_succ_succ', Nat.cast_add, Nat.choose_symm_half]
    ring
  have h₁ := harmonicSum_pascal (2 * n + 1) (n + 1)
  have h₂ := harmonicSum_pascal (2 * n + 2) (n + 1)
  rw [hodd] at h₂
  rw [harmonicSum_succ (2 * n + 1) (n + 1)] at h₁
  have hend := harmonicSum_succ (2 * n + 2) (n + 1)
  push_cast at h₁ h₂
  rw [show 2 * (n : ℚ) + 1 + 1 = 2 * (n + 1) by ring] at h₁
  rw [hcenter] at hend
  linear_combination 2 * h₁ + h₂ - hend + heven / (2 * ((n : ℚ) + 1))

private theorem invPowTwoSum_succ (n : ℕ) :
    invPowTwoSum (n + 1) = invPowTwoSum n + 1 / ((n + 1 : ℚ) * 2 ^ (n + 1)) := by
  simp only [invPowTwoSum, sum_Icc_succ_top (by omega : 1 ≤ n + 1), Nat.cast_add, Nat.cast_one]

private theorem centralBinomWeightedSum_succ (n : ℕ) :
    centralBinomWeightedSum (n + 1) = centralBinomWeightedSum n +
      ((2 * (n + 1)).choose (n + 1) : ℚ) / (2 * (n + 1) * 2 ^ (2 * (n + 1))) := by
  simp only [centralBinomWeightedSum, sum_Icc_succ_top (by omega : 1 ≤ n + 1),
    Nat.cast_add, Nat.cast_one]

/-- **Half-range binomial sum of harmonic numbers with top index $2n-1$.** Let $H_i$ denote
the $i$-th harmonic number (with $H_0 = 0$), and let Kollár's auxiliary sums be
$C_n = \sum_{k=1}^{n} \frac{1}{k \, 2^k}$ and
$D_n = \sum_{k=1}^{n} \frac{\binom{2k}{k}}{2k \cdot 2^{2k}}$.
For every positive integer $n$,
$$\sum_{i=0}^{n-1} \binom{2n-1}{i} H_i =
2^{2n-2} \left( H_{2n-1} - 2 C_{2n-1} + D_{n-1} \right).$$

Source: Richard Kollár, "Incomplete Finite Binomial Sums of
Harmonic Numbers", Theorem 3, equation `oddH`. -/
theorem sum_range_choose_two_mul_sub_one_mul_harmonic
    (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, ((2 * n - 1).choose i : ℚ) * harmonic i) =
      (2 : ℚ) ^ (2 * n - 2) *
        (harmonic (2 * n - 1) - 2 * invPowTwoSum (2 * n - 1) +
          centralBinomWeightedSum (n - 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one.mpr hn
  clear hn
  change harmonicSum (2 * n + 1) (n + 1) =
    2 ^ (2 * n) *
      (harmonic (2 * n + 1) - 2 * invPowTwoSum (2 * n + 1) + centralBinomWeightedSum n)
  induction n with
  | zero => norm_num [harmonicSum, invPowTwoSum, centralBinomWeightedSum]
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega, odd_row_step n, ih,
      harmonic_succ (2 * n + 2), harmonic_succ (2 * n + 1), invPowTwoSum_succ (2 * n + 2),
      invPowTwoSum_succ (2 * n + 1), centralBinomWeightedSum_succ]
    push_cast
    simp only [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add, pow_two]
    field_simp
    ring

/-- **Half-range binomial sum of harmonic numbers with top index $2n$.** Let $H_i$ denote
the $i$-th harmonic number (with $H_0 = 0$), and let Kollár's auxiliary sums be
$C_n = \sum_{k=1}^{n} \frac{1}{k \, 2^k}$ and
$D_n = \sum_{k=1}^{n} \frac{\binom{2k}{k}}{2k \cdot 2^{2k}}$.
For every positive integer $n$,
$$\sum_{i=0}^{n} \binom{2n}{i} H_i =
2^{2n-1} \left( H_{2n} - 2 C_{2n} + D_n \right) + \frac{1}{2} \binom{2n}{n} H_n.$$

Source: Richard Kollár, "Incomplete Finite Binomial Sums of
Harmonic Numbers", Theorem 3, equation `evenH`. -/
theorem sum_range_choose_two_mul_mul_harmonic
    (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range (n + 1), ((2 * n).choose i : ℚ) * harmonic i) =
      (2 : ℚ) ^ (2 * n - 1) *
          (harmonic (2 * n) - 2 * invPowTwoSum (2 * n) +
            centralBinomWeightedSum n) +
        (1 / 2 : ℚ) * ((2 * n).choose n : ℚ) * harmonic n := by
  have hodd := sum_range_choose_two_mul_sub_one_mul_harmonic (n + 1) (by omega)
  change harmonicSum (2 * n + 1) (n + 1) = 2 ^ (2 * n) *
    (harmonic (2 * n + 1) - 2 * invPowTwoSum (2 * n + 1) + centralBinomWeightedSum n) at hodd
  have hhalf : binomSum (2 * n + 1) (n + 1) = (2 : ℚ) ^ (2 * n) := by
    rw [pow_mul]
    unfold binomSum
    exact_mod_cast Nat.sum_range_choose_halfway n
  -- The two even-row sums in Pascal's rule differ only at the central term.
  have hpascal := harmonicSum_pascal (2 * n) n
  rw [hhalf] at hpascal
  calc
    harmonicSum (2 * n) (n + 1) =
        (harmonicSum (2 * n + 1) (n + 1) + (2 * n).choose n * harmonic n -
          (2 ^ (2 * n) - 1) / (↑(2 * n : ℕ) + 1)) / 2 := by
      linear_combination (harmonicSum_succ (2 * n) n - hpascal) / 2
    _ = _ := by
      rw [hodd, harmonic_succ, invPowTwoSum_succ, pow_succ]
      have hp : (2 : ℚ) ^ (2 * n) = 2 ^ (2 * n - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [hp]
      push_cast
      field_simp
      ring

end MathlibExt.Combinatorics.Enumerative.IncompleteBinomialHarmonicSumsWanted
