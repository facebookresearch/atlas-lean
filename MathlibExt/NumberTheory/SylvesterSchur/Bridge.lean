/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Basic

import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Sylvester-Schur: binomial and consecutive forms

This file records the elementary bridge between the binomial-coefficient form

`∃ p, p.Prime ∧ i < p ∧ p ∣ Nat.choose N i`, for `1 ≤ i` and `2 * i ≤ N`,

and the consecutive-integer form

among `n` consecutive integers starting at `k` with `n < k`, one has a prime divisor
greater than `n`.

The bridge contains no use of the main Sylvester-Schur theorem itself.
-/

@[expose] public section

namespace Nat.SylvesterSchur

open scoped BigOperators

open Finset Nat

/-- **Large prime divisors of a block term divide the binomial coefficient.** Let $n$, $k$ and
$j$ be natural numbers with $j < n$, and let $p$ be a prime with $p > n$. If $p$ divides
$k + j$, one of the $n$ consecutive integers $k, \dots, k+n-1$, then $p$ divides
$\binom{k+n-1}{n}$. -/
theorem prime_dvd_choose_of_dvd_consecutive {n k p j : ℕ} (hp : p.Prime) (hp_gt : n < p)
    (hj : j < n) (hdvd : p ∣ k + j) :
    p ∣ Nat.choose (k + n - 1) n := by
  have hprod_eq : k.ascFactorial n = n ! * Nat.choose (k + n - 1) n :=
    Nat.ascFactorial_eq_factorial_mul_choose' k n
  have hprod_eq_range : k.ascFactorial n = ∏ i ∈ Finset.range n, (k + i) :=
    Nat.ascFactorial_eq_prod_range k n
  have hp_dvd_prod : p ∣ ∏ i ∈ Finset.range n, (k + i) :=
    hdvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj))
  rw [← hprod_eq_range, hprod_eq] at hp_dvd_prod
  exact (hp.coprime_factorial_of_lt hp_gt).dvd_of_dvd_mul_left hp_dvd_prod

/-- **Prime divisors of the block binomial coefficient divide a block term.** Let $n$ and $k$ be
natural numbers and let $p$ be a prime. If $p$ divides $\binom{k+n-1}{n}$, then $p$ divides
$k + i$ for some $i$ with $0 \le i < n$. -/
theorem exists_dvd_consecutive_of_prime_dvd_choose (n k p : ℕ) (hp : p.Prime)
    (hp_dvd : p ∣ Nat.choose (k + n - 1) n) :
    ∃ i < n, p ∣ k + i := by
  have hprod_eq : k.ascFactorial n = n ! * Nat.choose (k + n - 1) n :=
    Nat.ascFactorial_eq_factorial_mul_choose' k n
  have hprod_eq_range : k.ascFactorial n = ∏ i ∈ Finset.range n, (k + i) :=
    Nat.ascFactorial_eq_prod_range k n
  have hp_dvd_prod : p ∣ ∏ i ∈ Finset.range n, (k + i) := by
    rw [← hprod_eq_range, hprod_eq]
    exact dvd_mul_of_dvd_right hp_dvd (n !)
  rw [hp.prime.dvd_finsetProd_iff] at hp_dvd_prod
  simpa [Finset.mem_range] using hp_dvd_prod

/-- **From a large prime divisor of the binomial coefficient to one in the block.** Let $n$ and
$k$ be natural numbers. If some prime $p > n$ divides $\binom{k+n-1}{n}$, then some prime
$p > n$ divides one of the integers $k + i$ with $0 \le i < n$. -/
theorem consecutive_of_exists_prime_dvd_choose {n k : ℕ}
    (hbin : ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  obtain ⟨p, hp, hp_gt, hp_dvd⟩ := hbin
  obtain ⟨i, hi, hi_dvd⟩ :=
    exists_dvd_consecutive_of_prime_dvd_choose n k p hp hp_dvd
  exact ⟨i, hi, p, hp, hp_gt, hi_dvd⟩

end Nat.SylvesterSchur
