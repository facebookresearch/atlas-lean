/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibility
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Set.Finite.Basic

/-!
# The minimum Pisano period-to-modulus ratio

Even-indexed Fibonacci numbers give arbitrarily small period-to-modulus ratios: the
period is bounded by twice the index, whereas the modulus grows exponentially.

## References

* Oisín Flynn-Connolly, *On the Divisibility of Sums of Fibonacci Numbers*,
  INTEGERS 25 (2025), [Article A87](https://math.colgate.edu/~integers/z87/z87.pdf), pp. 1–8.
  The argument uses Proposition 2 (pp. 5–6) as in the proof of Corollary 1 (p. 6).
-/

namespace MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

private theorem two_pow_le_fib_two_mul (j : ℕ) (hj : 3 ≤ j) : 2 ^ j ≤ Nat.fib (2 * j) := by
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j _ ih =>
    rw [pow_succ, show 2 * (j + 1) = 2 * j + 2 by omega, Nat.fib_add_two]
    have h := Nat.fib_le_fib_succ (n := 2 * j)
    omega

private theorem exists_pisanoPeriod_div_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ (pisanoPeriod m : ℝ) / m < ε := by
  have hlim : Filter.Tendsto (fun j : ℕ => 4 * ((j : ℝ) / (2 : ℝ) ^ j))
      Filter.atTop (nhds 0) := by
    simpa only [pow_one, mul_zero] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)).const_mul 4
  obtain ⟨j, hj, hjε⟩ := ((Filter.eventually_ge_atTop 3).and (hlim.eventually_lt_const hε)).exists
  have hm : 0 < Nat.fib (2 * j) := Nat.fib_pos.mpr (by omega)
  have hperiod : pisanoPeriod (Nat.fib (2 * j)) ≤ 4 * j := by
    rw [show 4 * j = 2 * (2 * j) by omega]
    exact Nat.le_of_dvd (by omega) (pisanoPeriod_fib_dvd_two_mul _ (by omega) (dvd_mul_right 2 j))
  have hpow : (2 : ℝ) ^ j ≤ (Nat.fib (2 * j) : ℝ) := by
    exact_mod_cast two_pow_le_fib_two_mul j hj
  refine ⟨Nat.fib (2 * j), hm, ?_⟩
  calc
    _ ≤ (4 : ℝ) * j / (Nat.fib (2 * j) : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hperiod) (by positivity)
    _ ≤ (4 : ℝ) * j / (2 : ℝ) ^ j := div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ < ε := by simpa only [mul_div_assoc] using hjε

/-- **The minimum of $\pi(n)/n$ over $1 \le n < N$ tends to zero.** Let $\pi(n)$ denote the Pisano
period of $n$. As $N \to \infty$, the minimum of the real numbers $\pi(n)/n$ over the integers
$1 \le n \le N - 1$ (defined for $N \ge 2$) tends to $0$.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Corollary 1. -/
public theorem tendsto_iInf_pisanoPeriod_div_atTop :
    Filter.Tendsto
      (fun N : ℕ =>
        ⨅ n : {n : ℕ // n ∈ Finset.Icc 1 (N - 1)},
          (pisanoPeriod n.1 : ℝ) / n.1)
      Filter.atTop (nhds 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨m, hm, hratio⟩ := exists_pisanoPeriod_div_lt hε
  refine ⟨m + 1, fun N hN => ?_⟩
  let i : {n : ℕ // n ∈ Finset.Icc 1 (N - 1)} := ⟨m, Finset.mem_Icc.mpr ⟨hm, by omega⟩⟩
  have : Nonempty {n : ℕ // n ∈ Finset.Icc 1 (N - 1)} := ⟨i⟩
  have hnonneg : 0 ≤ ⨅ n : {n : ℕ // n ∈ Finset.Icc 1 (N - 1)}, (pisanoPeriod n.1 : ℝ) / n.1 :=
    le_ciInf fun _ => by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact (ciInf_le (Set.finite_range _).bddBelow i).trans_lt hratio

end MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted
