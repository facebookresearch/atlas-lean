/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.IntervalCases

/-!
# Primorials below powers of sixteen

The product of the first `w` primes is less than `16 ^ w` exactly when `0 < w < 16`.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 10 (`integers-2026-A95-prop-10`).
-/

namespace MetaMathlibExt

private def firstPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]

private theorem nth_prime_eq_firstPrimes {i : ℕ} (hi : i < 16) :
    Nat.nth Nat.Prime i = firstPrimes.getD i 0 := by
  have hp : Nat.Prime (firstPrimes.getD i 0) := by
    interval_cases i <;> decide
  have hc : Nat.count Nat.Prime (firstPrimes.getD i 0) = i := by
    interval_cases i <;> decide
  simpa only [hc] using Nat.nth_count hp

private theorem prod_eq_firstPrimes {w : ℕ} (hw : w ≤ 16) :
    ∏ i ∈ Finset.range w, Nat.nth Nat.Prime i =
      ∏ i ∈ Finset.range w, firstPrimes.getD i 0 := by
  apply Finset.prod_congr rfl
  intro i hi
  exact nth_prime_eq_firstPrimes ((Finset.mem_range.mp hi).trans_le hw)

private theorem pow_le_prod_first_primes {w : ℕ} (hw : 16 ≤ w) :
    16 ^ w ≤ ∏ i ∈ Finset.range w, Nat.nth Nat.Prime i := by
  induction w, hw using Nat.le_induction with
  | base =>
    rw [prod_eq_firstPrimes (by decide)]
    decide
  | succ w hw ih =>
    rw [pow_succ, Finset.prod_range_succ]
    exact Nat.mul_le_mul ih (by have := Nat.add_two_le_nth_prime w; omega)

/-- **Primorials below powers of sixteen.** For every positive integer $w$, we have $w < 16$ if and
only if the product $p_1 p_2 \cdots p_w$ of the first $w$ primes is less than $16^w$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 10 (`integers-2026-A95-prop-10`). -/
public theorem lt_sixteen_iff_prod_first_primes_lt {w : ℕ} (hw : 0 < w) :
    w < 16 ↔ ∏ i ∈ Finset.range w, Nat.nth Nat.Prime i < 16 ^ w
    := by
  constructor
  · intro h
    rw [prod_eq_firstPrimes h.le]
    interval_cases w <;> decide
  · intro h
    by_contra hn
    exact (not_lt_of_ge (pow_le_prod_first_primes (Nat.le_of_not_gt hn))) h

end MetaMathlibExt
