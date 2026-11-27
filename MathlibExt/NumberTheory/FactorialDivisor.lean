/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.Chebyshev

/-!
# An exponential bound for divisors of a factorial

`MetaMathlibExt.le_exp_of_dvd_factorial` bounds a divisor of `n!` in terms of `n` and the
largest exponent in its prime factorization.
-/

open Nat

namespace MetaMathlibExt

/-- **Divisors of a factorial bounded by their largest prime exponent.** Let $n \ge 1$ and let
$x$ be a positive integer dividing $n!$. Write $K(x)$ for the largest exponent in the prime
factorization of $x$, with $K(1) = 0$. Then $x \le \exp(3 n K(x) / 2)$.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Lemma 1 (`integers-2025-A71-lem-1`). -/
public theorem le_exp_of_dvd_factorial {n x : ℕ} (hn : 0 < n) (hx : 0 < x)
    (hdvd : x ∣ n !) :
    (x : ℝ) ≤ Real.exp (3 * n * (x.primeFactors.sup x.factorization : ℕ) / 2) := by
  let K := x.primeFactors.sup x.factorization
  have hprimes : x.primeFactors ⊆ primesLE n := by
    intro p hp
    have hprime := prime_of_mem_primeFactors hp
    exact mem_primesLE.mpr ⟨hprime.dvd_factorial.mp ((dvd_of_mem_primeFactors hp).trans hdvd),
      hprime⟩
  have hsum : ∑ p ∈ x.primeFactors, Real.log p ≤ Chebyshev.theta n := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    exact Finset.sum_le_sum_of_subset_of_nonneg hprimes fun p _ _ ↦ Real.log_natCast_nonneg p
  have hlog : Real.log 4 ≤ 3 / 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    linarith [Real.log_two_lt_d9]
  apply (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hx)).mp
  calc
    Real.log x = ∑ p ∈ x.primeFactors, (x.factorization p : ℝ) * Real.log p :=
      Real.log_nat_eq_sum_factorization x
    _ ≤ ∑ p ∈ x.primeFactors, (K : ℝ) * Real.log p := by
      refine Finset.sum_le_sum fun p hp ↦ mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
      exact_mod_cast Finset.le_sup (f := x.factorization) hp
    _ = K * ∑ p ∈ x.primeFactors, Real.log p := (Finset.mul_sum ..).symm
    _ ≤ K * (Real.log 4 * n) := by
      gcongr
      exact hsum.trans (Chebyshev.theta_le_log4_mul_x (Nat.cast_pos.mpr hn).le)
    _ ≤ K * (3 / 2 * (n : ℝ)) := by gcongr
    _ = 3 * n * (K : ℝ) / 2 := by ring

end MetaMathlibExt
