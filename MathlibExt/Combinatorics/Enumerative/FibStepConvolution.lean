/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.List.GetD
import Mathlib.Tactic.LinearCombination

/-!
# Convolutions of Fibonacci step sequences

The recurrence for the Fibonacci `m`-step numbers gives the denominator of their generating
function. Subtracting the identities for consecutive orders expresses both sides of the
convolution as coefficients of the same product of three generating functions. The six-step
convolution with the Fibonacci numbers follows by combining the two denominator identities.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

/-- **Initial segments of the Fibonacci $m$-step sequence.** For natural numbers $m$ and $n$,
this is the list of integers $[F_0, F_1, \dots, F_n]$, built recursively: the list for $n = 0$
is $[0]$, the list for $n = 1$ is $[0, 1]$, and for $n \ge 2$ the list for $n$ is the list for
$n - 1$ followed by $F_n = \sum_{j=1}^{m} F_{n-j}$, where $F_i = 0$ for $i < 0$. -/
def fibStepSeq (m : ℕ) : ℕ → List ℤ
  | 0 => [0]
  | 1 => [0, 1]
  | n + 2 =>
      let prev := fibStepSeq m (n + 1)
      prev ++ [∑ j ∈ Finset.Icc 1 m, prev.getD (n + 2 - j) 0]

/-- **Fibonacci $m$-step numbers.** For natural numbers $m$ and $n$, the integer $F^{(m)}_n$ is
defined by $F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$ and $F^{(m)}_n = \sum_{j=1}^{m} F^{(m)}_{n-j}$ for
$n \ge 2$, where $F^{(m)}_i = 0$ for $i < 0$. -/
def fibStep (m n : ℕ) : ℤ := (fibStepSeq m n).getD n 0

/-- **Generating function of the Fibonacci $m$-step numbers.** For a natural number $m$,
$F^{(m)}(X)$ is the formal power series $\sum_{n \ge 0} F^{(m)}_n X^n$ with rational
coefficients, where $F^{(m)}_n$ is the $n$-th Fibonacci $m$-step number. -/
noncomputable def fibStepGF (m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (fibStep m n : ℚ)

private lemma length_fibStepSeq (m n : ℕ) : (fibStepSeq m n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp [fibStepSeq, ih]

private lemma getD_fibStepSeq (m n k : ℕ) (hk : k ≤ n) :
    (fibStepSeq m n).getD k 0 = fibStep m k := by
  induction n with
  | zero =>
    obtain rfl : k = 0 := by omega
    rfl
  | succ n ih =>
    obtain h | rfl := lt_or_eq_of_le hk
    · cases n with
      | zero =>
        obtain rfl : k = 0 := by omega
        rfl
      | succ n =>
        rw [fibStepSeq, List.getD_append _ _ _ _ (by simpa [length_fibStepSeq] using h)]
        exact ih (by omega)
    · rfl

private lemma fibStep_add_two (m n : ℕ) :
    fibStep m (n + 2) = ∑ j ∈ Finset.Icc 1 m, fibStep m (n + 2 - j) := by
  rw [fibStep, fibStepSeq, List.getD_append_right _ _ _ _ (by simp [length_fibStepSeq])]
  simp only [length_fibStepSeq, Nat.sub_self, List.getD_cons_zero]
  exact Finset.sum_congr rfl fun j hj =>
    getD_fibStepSeq m (n + 1) _ (by have := (Finset.mem_Icc.mp hj).1; omega)

/-- **Alternating sum of the tribonacci numbers.** Write $T_n$ for the tribonacci numbers (the
Fibonacci $3$-step numbers $F^{(3)}_n$). For every integer $n \ge 0$,
$2 \sum_{j=0}^{n} (-1)^j T_j = (-1)^n (T_{n+1} - T_{n-1}) - 1$, where $T_{n-1}$ is read as
$T_0 = 0$ when $n = 0$.

The source prints this identity with a factor $1/2$; it is stated here multiplied by $2$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 18. -/
theorem two_mul_sum_neg_one_pow_trib (n : ℕ) :
    2 * ∑ j ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ j * fibStep 3 j =
      (-1 : ℤ) ^ n * (fibStep 3 (n + 1) - fibStep 3 (n - 1)) - 1 := by
  induction n with
  | zero =>
    simp [show fibStep 3 0 = 0 from rfl, show fibStep 3 1 = 1 from rfl]
  | succ n ih =>
    -- At n = 0, the last index saturates to 0 and the extra term is zero.
    have hrec : fibStep 3 (n + 2) = fibStep 3 (n + 1) + fibStep 3 n + fibStep 3 (n - 1) := by
      rw [fibStep_add_two 3 n, Finset.sum_Icc_succ_top (by decide : 1 ≤ 3),
        Finset.sum_Icc_succ_top (by decide : 1 ≤ 2), Finset.Icc_self, Finset.sum_singleton]
      congr 1
    -- The change in the signed boundary term is twice the new summand.
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ, Nat.add_sub_cancel, hrec]
    ring

open PowerSeries

private lemma coeff_shift (m j n : ℕ) :
    coeff n (X ^ j * fibStepGF m) = (fibStep m (n - j) : ℚ) := by
  rw [coeff_X_pow_mul']
  split_ifs with hj
  · exact coeff_mk ..
  · rw [Nat.sub_eq_zero_of_le (by omega)]
    rfl

private lemma fibStepGF_denom (m : ℕ) :
    (1 - ∑ j ∈ Finset.Icc 1 m, X ^ j) * fibStepGF m = X := by
  ext n
  simp only [sub_mul, one_mul, Finset.sum_mul, map_sub, map_sum, coeff_shift, coeff_X]
  rw [fibStepGF, coeff_mk]
  have h0 : fibStep m 0 = 0 := rfl
  match n with
  | 0 => simp [h0]
  | 1 =>
    have hz (j : ℕ) (hj : j ∈ Finset.Icc 1 m) : (fibStep m (1 - j) : ℚ) = 0 := by
      simp [Nat.sub_eq_zero_of_le (Finset.mem_Icc.mp hj).1, h0]
    simp [Finset.sum_eq_zero hz, show fibStep m 1 = 1 from rfl]
  | n + 2 => simp [fibStep_add_two m n]

private lemma fibStepGF_sub_succ (m : ℕ) :
    fibStepGF m - fibStepGF (m + 1) =
      -(X ^ m) * fibStepGF m * fibStepGF (m + 1) := by
  have hm := fibStepGF_denom m
  have hs := fibStepGF_denom (m + 1)
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), pow_succ] at hs
  apply X_mul_cancel
  linear_combination fibStepGF (m + 1) * hm - fibStepGF m * hs

/-- **A product identity for three consecutive Fibonacci step generating functions.** Let
$m \ge 1$ be a natural number. For each $k$, let $F^{(k)} = \sum_{n \ge 0} F^{(k)}_n X^n$ in
$\mathbb{Q}[[X]]$ be the ordinary generating function of the Fibonacci $k$-step numbers
$F^{(k)}_n$. Then
$$X^{2m+1} F^{(m)} F^{(m+1)} F^{(m+2)} = X^m F^{(m)} F^{(m+2)} - F^{(m+1)} + F^{(m)}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 24. -/
theorem fibStepGF_triple_consecutive (m : ℕ)
    (hm : 1 ≤ m) :
    PowerSeries.X ^ (2 * m + 1) * fibStepGF m * fibStepGF (m + 1) *
        fibStepGF (m + 2) =
      PowerSeries.X ^ m * fibStepGF m * fibStepGF (m + 2) -
        fibStepGF (m + 1) + fibStepGF m := by
  by_cases h : m = 0
  · subst m
    exact (Nat.not_succ_le_zero 0 hm).elim
  symm
  calc
    _ = X ^ m * fibStepGF m * fibStepGF (m + 2) +
        (fibStepGF m - fibStepGF (m + 1)) := by ring
    _ = X ^ m * fibStepGF m * (fibStepGF (m + 2) - fibStepGF (m + 1)) := by
      rw [fibStepGF_sub_succ m]
      ring
    _ = _ := by
      rw [← neg_sub (fibStepGF (m + 1)) (fibStepGF (m + 2)), fibStepGF_sub_succ (m + 1),
        show 2 * m + 1 = m + (m + 1) by omega, pow_add]
      ring

/-- **A product identity for four consecutive Fibonacci step generating functions.** Let
$m \ge 1$ be a natural number. For each $k$, let $F^{(k)} = \sum_{n \ge 0} F^{(k)}_n X^n$ in
$\mathbb{Q}[[X]]$ be the ordinary generating function of the Fibonacci $k$-step numbers
$F^{(k)}_n$. Then
$$X^{2m+1} F^{(m)} F^{(m+1)} F^{(m+2)} F^{(m+3)} =
X^m F^{(m)} F^{(m+2)} F^{(m+3)} - F^{(m+1)} F^{(m+3)} + F^{(m)} F^{(m+3)}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 31. -/
theorem fibStepGF_quadruple_consecutive (m : ℕ)
    (hm : 1 ≤ m) :
    PowerSeries.X ^ (2 * m + 1) * fibStepGF m * fibStepGF (m + 1) *
        fibStepGF (m + 2) * fibStepGF (m + 3) =
      PowerSeries.X ^ m * fibStepGF m * fibStepGF (m + 2) *
          fibStepGF (m + 3) -
        fibStepGF (m + 1) * fibStepGF (m + 3) +
        fibStepGF m * fibStepGF (m + 3) := by
  by_cases h : m = 0
  · subst m
    exact (Nat.not_succ_le_zero 0 hm).elim
  rw [show 2 * m + 1 = m + (m + 1) by omega, pow_add]
  -- Multiply the two consecutive differences by the remaining factors and cancel.
  linear_combination
    -(fibStepGF (m + 3)) * fibStepGF_sub_succ m +
      X ^ m * fibStepGF m * fibStepGF (m + 3) * fibStepGF_sub_succ (m + 1)

/-- **Convolution of the Fibonacci and tribonacci numbers.** Write $F_n$ and $T_n$ for the
Fibonacci and tribonacci numbers, that is, the Fibonacci $m$-step numbers $F^{(m)}_n$ for
$m = 2, 3$ ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each later term is the sum of the $m$ terms
before it, terms at negative indices being $0$). For every natural number $n$,
$$\sum_{j=0}^{n} F_j T_{n-j} = T_{n+2} - F_{n+2}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 2. -/
theorem sum_fib_mul_trib (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), fibStep 2 j * fibStep 3 (n - j) =
      fibStep 3 (n + 2) - fibStep 2 (n + 2) := by
  have hg : X ^ 2 * (fibStepGF 2 * fibStepGF 3) = fibStepGF 3 - fibStepGF 2 := by
    linear_combination fibStepGF_sub_succ 2
  have hc := congrArg (coeff (n + 2) (R := ℚ)) hg
  rw [coeff_X_pow_mul] at hc
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sub,
    fibStepGF, coeff_mk] at hc
  exact_mod_cast hc

/-- **Difference of the Fibonacci 3-step and 2-step numbers as a convolution.** Let $F_j$ and
$T_j$ be the Fibonacci $2$-step and $3$-step numbers, where the Fibonacci $k$-step numbers start
$0, 1$ and each later term is the sum of the $k$ terms before it (terms of negative index being
$0$). For every natural number $n \ge 1$,

$$T_{n+1} - F_{n+1} = \sum_{j=0}^{n-1} T_j \, F_{n-1-j}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 11. -/
theorem trib_sub_fib_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    fibStep 3 (n + 1) - fibStep 2 (n + 1) =
      ∑ j ∈ Finset.range n, fibStep 3 j * fibStep 2 (n - 1 - j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [← sum_fib_mul_trib k, ← Finset.sum_flip (fun j => fibStep 2 j * fibStep 3 (k - j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.sub_sub_self (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  exact mul_comm _ _

private lemma sum_consecutive_mul_sub_eq (m n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range (n + 1), fibStep m j *
        (fibStep (m + 1) (n - j) - fibStep (m + 2) (n - j)) =
      ∑ j ∈ Finset.range n,
        (fibStep m j - fibStep (m + 1) j) * fibStep (m + 2) (n - 1 - j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h : fibStepGF m * (fibStepGF (m + 1) - fibStepGF (m + 2)) =
      X * ((fibStepGF m - fibStepGF (m + 1)) * fibStepGF (m + 2)) := by
    rw [fibStepGF_sub_succ (m + 1), fibStepGF_sub_succ m, pow_succ X m]
    ring
  have hc := congrArg (coeff (k + 1) (R := ℚ)) h
  rw [coeff_succ_X_mul] at hc
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sub,
    fibStepGF, coeff_mk] at hc
  exact_mod_cast hc

/-- **Convolution of the Fibonacci numbers with tribonacci minus tetranacci.** Write $F_n$, $T_n$
and $Q_n$ for the Fibonacci, tribonacci and tetranacci numbers, that is, the Fibonacci $m$-step
numbers $F^{(m)}_n$ for $m = 2, 3, 4$ ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each later term is the
sum of the $m$ terms before it, terms at negative indices being $0$). For every natural number
$n \ge 1$,
$$\sum_{j=0}^{n} F_j (T_{n-j} - Q_{n-j}) = \sum_{j=0}^{n-1} (F_j - T_j) Q_{n-1-j}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 11. -/
theorem sum_fib_mul_sub_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range (n + 1), fibStep 2 j *
        (fibStep 3 (n - j) - fibStep 4 (n - j)) =
      ∑ j ∈ Finset.range n,
        (fibStep 2 j - fibStep 3 j) * fibStep 4 (n - 1 - j) :=
  sum_consecutive_mul_sub_eq 2 n hn

/-- **Convolution of the Fibonacci 3-step numbers with differences of 4- and 5-step numbers.**
Let $T_j$, $Q_j$ and $P_j$ be the Fibonacci $3$-, $4$- and $5$-step numbers, where the Fibonacci
$k$-step numbers start $0, 1$ and each later term is the sum of the $k$ terms before it (terms of
negative index being $0$). For every natural number $n \ge 1$,

$$\sum_{j=0}^{n} T_j \bigl(Q_{n-j} - P_{n-j}\bigr) =
\sum_{j=0}^{n-1} \bigl(T_j - Q_j\bigr) P_{n-1-j}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 11. -/
theorem sum_trib_mul_sub_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range (n + 1), fibStep 3 j *
        (fibStep 4 (n - j) - fibStep 5 (n - j)) =
      ∑ j ∈ Finset.range n,
        (fibStep 3 j - fibStep 4 j) * fibStep 5 (n - 1 - j) :=
  sum_consecutive_mul_sub_eq 3 n hn

private lemma fibStepGF_six_mul_two :
    5 * (X ^ 3 * (fibStepGF 6 * fibStepGF 2)) =
      fibStepGF 6 + X ^ 2 * fibStepGF 6 - X ^ 3 * fibStepGF 6 +
        3 * (X ^ 4 * fibStepGF 6) + X ^ 6 * fibStepGF 6 -
        fibStepGF 2 - X ^ 2 * fibStepGF 2 := by
  have h₂ := fibStepGF_denom 2
  have h₆ := fibStepGF_denom 6
  norm_num [Finset.sum_Icc_succ_top] at h₂ h₆
  apply X_mul_cancel
  linear_combination
    (1 + X ^ 2 - X ^ 3 + 3 * X ^ 4 + X ^ 6) * fibStepGF 6 * h₂ -
    (1 + X ^ 2) * fibStepGF 2 * h₆

/-- **Convolution of the Fibonacci $6$-step numbers with the Fibonacci numbers.** Write
$s_n = F^{(6)}_n$ for the Fibonacci $6$-step numbers and $F_n = F^{(2)}_n$ for the Fibonacci
numbers. For every natural number $n \ge 3$,
$$5 \sum_{j=0}^{n} s_j F_{n-j} =
s_{n+3} + s_{n+1} - s_n + 3 s_{n-1} + s_{n-3} - F_{n+3} - F_{n+1}.$$

The source prints this identity divided by $5$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 41. -/
theorem five_mul_sum_fibStep6_mul_fib (n : ℕ)
    (hn : 3 ≤ n) :
    5 * ∑ j ∈ Finset.range (n + 1),
        fibStep 6 j * fibStep 2 (n - j) =
      fibStep 6 (n + 3) + fibStep 6 (n + 1) - fibStep 6 n +
        3 * fibStep 6 (n - 1) + fibStep 6 (n - 3) -
        fibStep 2 (n + 3) - fibStep 2 (n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h := congrArg (coeff (k + 3 + 3) (R := ℚ)) fibStepGF_six_mul_two
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_X_pow_mul, coeff_shift] at h
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, fibStepGF, coeff_mk] at h
  apply Int.cast_injective (α := ℚ)
  push_cast
  exact h

end MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted
