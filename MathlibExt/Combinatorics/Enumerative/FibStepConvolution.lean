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
# A convolution of the Fibonacci, tribonacci and tetranacci numbers

The recurrence for the Fibonacci `m`-step numbers gives the denominator of their generating
function. Subtracting the identities for consecutive orders expresses both sides of the
convolution as coefficients of the same product of three generating functions.
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
        (fibStep 2 j - fibStep 3 j) * fibStep 4 (n - 1 - j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h : fibStepGF 2 * (fibStepGF 3 - fibStepGF 4) =
      X * ((fibStepGF 2 - fibStepGF 3) * fibStepGF 4) := by
    rw [fibStepGF_sub_succ 3, fibStepGF_sub_succ 2]
    ring
  have hc := congrArg (coeff (k + 1) (R := ℚ)) h
  rw [coeff_succ_X_mul] at hc
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sub,
    fibStepGF, coeff_mk] at hc
  exact_mod_cast hc

end MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted
