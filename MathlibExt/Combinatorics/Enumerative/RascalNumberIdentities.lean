/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.RascalNumbers
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Identities for Rascal numbers from their closed form

Statements from Amelia Gibbs and Brian K. Miceli, "Two Combinatorial Interpretations of Rascal
Numbers", *Journal of Integer Sequences* 27 (2024), Article 24.8.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Miceli/miceli9.html>; arXiv:2405.11045).

Each identity follows from the closed form `rascalZ n k = k * (n - k) + 1` for `0 ≤ k ≤ n`:
symmetry, Fleron's recurrence, the generalized diamond recurrence, the row-shift and diagonal
recurrences, row and column sums, binomial-weighted and alternating row sums, the double sum of
the interior numbers, and the products of the shifted numbers `R_{n,k} - 1`.

The docstrings below record three corrections to the printed statements: Fleron's recurrence
(Theorem 4) needs `0 < k < n`, Theorem 6 needs `k ≤ n`, and Theorem 10 has the exponent `n - 1`
where the paper prints `n - 2`.
-/

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

open Finset

/-- In range, a Rascal number at natural indices is given by its closed form. -/
private theorem rascalZ_natCast {n k : ℕ} (h : k ≤ n) :
    rascalZ (n : ℤ) (k : ℤ) = (k : ℤ) * ((n : ℤ) - k) + 1 :=
  ite_eq_left ⟨by omega, by omega⟩

/-- The sum of `0, 1, …, n` as a binomial coefficient, in `ℤ`. -/
private theorem sum_range_natCast (n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℤ) = ((n + 1).choose 2 : ℕ) := by
  rw [Nat.choose_two_right, ← sum_range_id, Nat.cast_sum]

/-- The row sums of the closed form `k (n - k) + 1`. -/
private theorem sum_range_closedForm (n : ℕ) :
    ∑ k ∈ range (n + 1), ((k : ℤ) * ((n : ℤ) - k) + 1) =
      ((n + 1).choose 3 : ℕ) + (n : ℤ) + 1 := by
  induction n with
  | zero => simp [Nat.choose_eq_zero_of_lt]
  | succ n ih =>
    have hshift : ∑ k ∈ range (n + 1), ((k : ℤ) * (((n + 1 : ℕ) : ℤ) - k) + 1) =
        ∑ k ∈ range (n + 1), ((k : ℤ) * ((n : ℤ) - k) + 1) +
          ∑ k ∈ range (n + 1), (k : ℤ) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [sum_range_succ, hshift, ih, sum_range_natCast, Nat.choose_succ_succ' (n + 1) 2]
    push_cast
    ring

/-- Alternating sums of a quadratic polynomial over `0, 1, …, 2m`. -/
private theorem sum_range_neg_one_pow_quadratic (a b c : ℤ) (m : ℕ) :
    ∑ k ∈ range (2 * m + 1), (-1 : ℤ) ^ k * (a + b * k + c * k ^ 2) =
      a + b * m + c * (2 * m ^ 2 + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      (show Odd (2 * m + 1) from ⟨m, rfl⟩).neg_one_pow,
      (show Even (2 * m + 1 + 1) from ⟨m + 1, by ring⟩).neg_one_pow]
    push_cast
    ring

/-- **Symmetry of Rascal numbers.** For integers $n$ and $k$ with $0 \le k \le n$, the Rascal
numbers satisfy $R_{n,k} = R_{n,n-k}$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 2. -/
public theorem rascalZ_symm (n k : ℤ) (h0 : 0 ≤ k) (h1 : k ≤ n) :
    rascalZ n k = rascalZ n (n - k) := by
  simp (disch := omega) only [rascalZ, ite_eq_left]
  ring

-- Keep the source's hypothesis `2 ≤ n`, which follows from `0 < k < n`.
set_option linter.unusedVariables false in
/-- **Fleron's recurrence for Rascal numbers.** For integers $n$ and $k$ with $n \ge 2$ and
$0 < k < n$, the Rascal numbers $R_{n,k}$ satisfy
$R_{n,k} = R_{n-1,k} + R_{n-1,k-1} - R_{n-2,k-1} + 1$.

The hypothesis $0 < k < n$ is needed: at $k = 0$ or $k = n$ the right side equals $2$ while
$R_{n,k} = 1$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 4. -/
public theorem rascalZ_fleron (n k : ℤ) (hn : 2 ≤ n)
    (hk0 : 0 < k) (hkn : k < n) :
    rascalZ n k = rascalZ (n - 1) k + rascalZ (n - 1) (k - 1) -
      rascalZ (n - 2) (k - 1) + 1 := by
  simp (disch := omega) only [rascalZ, ite_eq_left]
  ring

/-- **Generalized diamond recurrence for Rascal numbers.** For integers $n$, $k$, $\ell$, $u$
with $\ell \ge 0$, $u \ge 0$ and $\ell \le k \le n - u$, the Rascal numbers satisfy
$R_{n,k} R_{n-u-\ell,k-\ell} = R_{n-u,k} R_{n-\ell,k-\ell} + u\ell$.

Since $R_{n-u-\ell,k-\ell} \ge 1$ under these hypotheses, this is the paper's formula
$R_{n,k} = (R_{n-u,k} R_{n-\ell,k-\ell} + u\ell) / R_{n-u-\ell,k-\ell}$ cleared of denominators.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 5. -/
public theorem rascalZ_mul_eq (n k ℓ u : ℤ) (hℓ : 0 ≤ ℓ)
    (hu : 0 ≤ u) (h : ℓ ≤ k) (h2 : k ≤ n - u) :
    rascalZ n k * rascalZ (n - u - ℓ) (k - ℓ) =
      rascalZ (n - u) k * rascalZ (n - ℓ) (k - ℓ) + u * ℓ := by
  simp (disch := omega) only [rascalZ, ite_eq_left]
  ring

/-- **Row-shift identity for the Rascal numbers.** For integers $n$, $m$ and $k$ with $m \ge 0$
and $0 \le k \le n$,
$$R_{n+m,k} = R_{n,k} + R_{m+k,k} - 1,$$
where $R_{a,b}$ denotes the Rascal numbers, which vanish unless $0 \le b \le a$.

The hypothesis $k \le n$, absent from the printed statement, is needed: for $n = 0$, $m = 1$ and
$k = 2$ the left side is $R_{1,2} = 0$ while the right side is $0 + 3 - 1 = 2$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 6. -/
public theorem rascalZ_add_eq (n m k : ℤ) (hm : 0 ≤ m)
    (hk0 : 0 ≤ k) (hkn : k ≤ n) :
    rascalZ (n + m) k = rascalZ n k + rascalZ (m + k) k - 1 := by
  simp (disch := omega) only [rascalZ, ite_eq_left]
  ring

/-- **Diagonal recurrence for Rascal numbers.** For integers $n$ and $k$ with $0 < k < n$,
$$k R_{n-1,k-1} - 1 = (k-1) R_{n,k},$$
where $R_{a,b}$ is the Rascal number, equal to $b(a-b) + 1$ for $0 \le b \le a$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 7. -/
public theorem mul_rascalZ_sub_one (n k : ℤ) (hk0 : 0 < k)
    (hkn : k < n) :
    k * rascalZ (n - 1) (k - 1) - 1 = (k - 1) * rascalZ n k := by
  simp (disch := omega) only [rascalZ, ite_eq_left]
  ring

/-- **Row sums of the Rascal triangle.** For every natural number
$n$, the Rascal numbers $R_{n,k} = k(n-k) + 1$ ($0 \le k \le n$)
satisfy $\sum_{k=0}^{n} R_{n,k} = \binom{n+1}{3} + n + 1$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 8. -/
public theorem sum_rascalZ_row (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), rascalZ (n : ℤ) (k : ℤ) =
      (Nat.choose (n + 1) 3 : ℤ) + (n : ℤ) + 1 := by
  rw [← sum_range_closedForm]
  exact sum_congr rfl fun k hk => rascalZ_natCast (Nat.lt_succ_iff.mp (mem_range.mp hk))

/-- **Column sums of the Rascal triangle.** For all natural numbers
$k$ and $r$, the Rascal numbers $R_{n,k} = k(n-k) + 1$
($0 \le k \le n$) satisfy
$\sum_{i=0}^{r} R_{k+i,k} = k \binom{r+1}{2} + r + 1$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 9. -/
public theorem sum_rascalZ_column (k r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), rascalZ ((k + i : ℕ) : ℤ) (k : ℤ) =
      (k : ℤ) * (Nat.choose (r + 1) 2 : ℤ) + (r : ℤ) + 1 := by
  have hterm (i : ℕ) : rascalZ ((k + i : ℕ) : ℤ) (k : ℤ) = (k : ℤ) * i + 1 := by
    rw [rascalZ_natCast (Nat.le_add_right k i)]
    push_cast
    ring
  simp only [hterm, sum_add_distrib, ← mul_sum, sum_range_natCast, sum_const, card_range,
    nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- **Binomial-weighted row sums of the Rascal triangle.** For
every natural number $n$, the Rascal numbers
$R_{n,k} = k(n-k) + 1$ ($0 \le k \le n$) satisfy
$2 \sum_{k=0}^{n} \binom{n}{k} R_{n,k} = 2^n \binom{n}{2} + 2^{n+1}$.

The paper prints the exponent $n - 2$ where the correct exponent
is $n - 1$ in $\sum_{k} \binom{n}{k} R_{n,k} = 2^{n-1} \binom{n}{2} + 2^n$
(at $n = 2$ the sum is $6$, not $5$); the identity is stated
doubled so that no exponent is negative at $n = 0$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 10. -/
public theorem two_mul_sum_choose_mul_rascalZ (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℤ) * rascalZ (n : ℤ) (k : ℤ) =
      2 ^ n * (Nat.choose n 2 : ℤ) + 2 ^ (n + 1) := by
  have hsplit : ∑ k ∈ range (n + 1), (Nat.choose n k : ℤ) * rascalZ (n : ℤ) (k : ℤ) =
      ∑ k ∈ range (n + 1), (Nat.choose n k : ℤ) * ((k : ℤ) * ((n : ℤ) - k)) +
        ∑ k ∈ range (n + 1), (Nat.choose n k : ℤ) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [rascalZ_natCast (Nat.lt_succ_iff.mp (mem_range.mp hk))]
    ring
  have hpow : ∑ k ∈ range (n + 1), (Nat.choose n k : ℤ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  -- Twice the weighted part `∑ C(n, k) k (n - k)` is `2 ^ n * C(n, 2)`.
  have hweight :
      2 * ∑ k ∈ range (n + 1), (Nat.choose n k : ℤ) * ((k : ℤ) * ((n : ℤ) - k)) =
        2 ^ n * (Nat.choose n 2 : ℤ) := by
    rcases n with _ | _ | m
    · simp
    · simp [sum_range_succ]
    -- Drop the zero terms `k = 0` and `k = m + 2`, and write the others with `k = j + 1`.
    rw [sum_range_succ', sum_range_succ]
    have hterm (j : ℕ) (hj : j ∈ range (m + 1)) :
        ((m + 1 + 1).choose (j + 1) : ℤ) *
            (((j + 1 : ℕ) : ℤ) * (((m + 1 + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ))) =
          ((m : ℤ) + 2) * ((m : ℤ) + 1) * (m.choose j : ℤ) := by
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have h1 : (((m + 1 + 1) * (m + 1).choose j : ℕ) : ℤ) =
          (((m + 1 + 1).choose (j + 1) * (j + 1) : ℕ) : ℤ) :=
        congrArg _ (Nat.add_one_mul_choose_eq (m + 1) j)
      have h2 : ((m.choose j * (m + 1) : ℕ) : ℤ) =
          (((m + 1).choose j * (m + 1 - j) : ℕ) : ℤ) :=
        congrArg _ (Nat.choose_mul_succ_eq m j)
      push_cast [Nat.cast_sub (show j ≤ m + 1 by omega)] at h1 h2 ⊢
      linear_combination (-((m : ℤ) + 1 - j)) * h1 - ((m : ℤ) + 2) * h2
    have hchoose : ((m + 1 + 1).choose 2 : ℤ) * 2 = ((m : ℤ) + 2) * ((m : ℤ) + 1) := by
      have h := Nat.add_one_mul_choose_eq (m + 1) 1
      rw [Nat.choose_one_right] at h
      exact_mod_cast h.symm
    have hsum : ∑ j ∈ range (m + 1), (m.choose j : ℤ) = 2 ^ m := by
      exact_mod_cast Nat.sum_range_choose m
    rw [sum_congr rfl hterm, ← mul_sum, hsum]
    simp only [sub_self, mul_zero, Nat.cast_zero, zero_mul, add_zero]
    linear_combination (-(2 : ℤ) ^ m * 2) * hchoose
  rw [hsplit, hpow, mul_add, hweight, pow_succ]
  ring

-- Keep the source's hypothesis `2 ≤ n`; the identity also holds for `n = 0` and `n = 1`.
set_option linter.unusedVariables false in
/-- **Sum of the interior Rascal numbers.** For every natural
number $n \ge 2$, the Rascal numbers $R_{i,j} = j(i-j) + 1$
($0 \le j \le i$) satisfy
$\sum_{i=1}^{n} \sum_{j=1}^{i-1} R_{i,j} = \binom{n+2}{4} + \binom{n}{2}$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 11. -/
public theorem sum_sum_rascalZ (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 (i - 1),
        rascalZ (i : ℤ) (j : ℤ) =
      (Nat.choose (n + 2) 4 : ℤ) + (Nat.choose n 2 : ℤ) := by
  -- The interior of row `i + 1` sums to `C(i + 2, 3) + i`.
  have hrow (i : ℕ) : ∑ j ∈ Icc 1 i, rascalZ ((i + 1 : ℕ) : ℤ) (j : ℤ) =
      ((i + 2).choose 3 : ℕ) + (i : ℤ) := by
    have := sum_rascalZ_row (i + 1)
    rw [sum_range_succ, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), zero_add,
      Ico_add_one_right_eq_Icc, rascalZ_natCast le_rfl, rascalZ_natCast (Nat.zero_le _)] at this
    push_cast at this ⊢
    linarith
  clear hn
  induction n with
  | zero => simp [Nat.choose_eq_zero_of_lt]
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel, hrow,
      show n + 1 + 2 = (n + 2) + 1 by ring, Nat.choose_succ_succ' (n + 2) 3,
      Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    push_cast
    ring

/-- **Alternating row sums of the Rascal triangle, odd rows.**
For every natural number $m$, the Rascal numbers
$R_{n,k} = k(n-k) + 1$ ($0 \le k \le n$) satisfy
$\sum_{k=0}^{2m+1} (-1)^k R_{2m+1,k} = 0$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 13. -/
public theorem sum_rascalZ_alternating_odd (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 2),
        (-1 : ℤ) ^ k * rascalZ ((2 * m + 1 : ℕ) : ℤ) (k : ℤ) = 0 := by
  have hterm (k : ℕ) (hk : k ∈ range (2 * m + 2)) :
      (-1 : ℤ) ^ k * rascalZ ((2 * m + 1 : ℕ) : ℤ) (k : ℤ) =
        (-1 : ℤ) ^ k * (1 + (2 * (m : ℤ) + 1) * k + (-1) * k ^ 2) := by
    rw [rascalZ_natCast (Nat.lt_succ_iff.mp (mem_range.mp hk))]
    push_cast
    ring
  rw [sum_congr rfl hterm, sum_range_succ, sum_range_neg_one_pow_quadratic,
    (show Odd (2 * m + 1) from ⟨m, rfl⟩).neg_one_pow]
  push_cast
  ring

/-- **Alternating row sums of Rascal numbers on even rows.** For every natural number $m$, the
Rascal numbers satisfy $\sum_{k=0}^{2m} (-1)^k R_{2m,k} = 1 - m$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 13. -/
public theorem sum_rascalZ_alternating_even (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 1),
        (-1 : ℤ) ^ k * rascalZ ((2 * m : ℕ) : ℤ) (k : ℤ) =
      1 - (m : ℤ) := by
  have hterm (k : ℕ) (hk : k ∈ range (2 * m + 1)) :
      (-1 : ℤ) ^ k * rascalZ ((2 * m : ℕ) : ℤ) (k : ℤ) =
        (-1 : ℤ) ^ k * (1 + 2 * (m : ℤ) * k + (-1) * k ^ 2) := by
    rw [rascalZ_natCast (Nat.lt_succ_iff.mp (mem_range.mp hk))]
    push_cast
    ring
  rw [sum_congr rfl hterm, sum_range_neg_one_pow_quadratic]
  ring

-- Keep the source's hypotheses `1 ≤ m ≤ n`; the expansion holds for all `m` and `n`.
set_option linter.unusedVariables false in
/-- **Subset-sum expansion of the product of the shifted Rascal numbers.** For natural numbers
$m$ and $n$ with $1 \le m \le n$, writing $[m] = \{1, \dots, m\}$,
$$\prod_{k=1}^{m} (R_{n,k} - 1) = \sum_{S \subseteq [m]} (-1)^{m-|S|} \prod_{i \in S} R_{n,i},$$
where $R_{n,k}$ denotes the Rascal numbers.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 14. -/
public theorem prod_rascalZ_sub_one_eq_sum (n m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∏ k ∈ Finset.Icc 1 m, (rascalZ (n : ℤ) (k : ℤ) - 1) =
      ∑ S ∈ (Finset.Icc 1 m).powerset,
        (-1 : ℤ) ^ (m - S.card) *
          ∏ i ∈ S, rascalZ (n : ℤ) (i : ℤ) := by
  simp only [sub_eq_add_neg, prod_add, prod_const]
  refine sum_congr rfl fun S hS => ?_
  rw [card_sdiff_of_subset (mem_powerset.mp hS), Nat.card_Icc, Nat.add_sub_cancel, mul_comm]

-- Keep the source's hypothesis `1 ≤ m`; the identity also holds for `m = 0`.
set_option linter.unusedVariables false in
/-- **Closed form for the product of the shifted Rascal numbers.** For natural numbers $m$ and
$n$ with $1 \le m \le n$,
$$\prod_{k=1}^{m} (R_{n,k} - 1) = m! \, (n-1)^{\underline{m}},$$
where $R_{n,k}$ denotes the Rascal numbers and $x^{\underline{m}} = x(x-1)\cdots(x-m+1)$ is the
falling factorial.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 14. -/
public theorem prod_rascalZ_sub_one_eq_factorial_mul (n m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∏ k ∈ Finset.Icc 1 m, (rascalZ (n : ℤ) (k : ℤ) - 1) =
      (m.factorial : ℤ) * (Nat.descFactorial (n - 1) m : ℤ) := by
  clear hm
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_Icc_succ_top (by omega), ih (by omega), rascalZ_natCast hmn, Nat.factorial_succ,
      Nat.descFactorial_succ]
    push_cast [Nat.cast_sub (show m ≤ n - 1 by omega), Nat.cast_sub (show 1 ≤ n by omega)]
    ring

/-- **Binomial coefficients from products of Rascal numbers.** For natural numbers $n$ and $m$
with $1 \le m \le n$,
$$(m!)^2 \binom{n-1}{m} = \prod_{k=1}^{m} (R_{n,k} - 1),$$
where $R_{n,k} = k(n-k) + 1$ is the Rascal number for $0 \le k \le n$.

Equivalently, $\frac{1}{(m!)^2} \prod_{k=1}^{m} (R_{n,k} - 1) = \binom{n-1}{m}$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Corollary 15. -/
public theorem factorial_sq_mul_choose_eq_prod (n m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    (m.factorial : ℤ) ^ 2 * (Nat.choose (n - 1) m : ℤ) =
      ∏ k ∈ Finset.Icc 1 m, (rascalZ (n : ℤ) (k : ℤ) - 1) := by
  rw [prod_rascalZ_sub_one_eq_factorial_mul n m hm hmn, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
