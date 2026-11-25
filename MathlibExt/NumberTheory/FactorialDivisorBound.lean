/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Choose.Factorization

/-!
# Bounding a divisor of a factorial by its number of prime factors

For every positive divisor of `n!`, `MetaMathlibExt.le_rpow_mul_pow_of_dvd_factorial`
gives an upper bound in terms of `n` and the number of distinct prime divisors.
-/

open Nat

namespace MetaMathlibExt

/-- **Divisors of a factorial bounded by their number of prime factors.** Let $n \ge 1$ and let
$x$ be a positive integer dividing $n!$, and write $\omega(x)$ for the number of distinct prime
divisors of $x$. Then for every positive integer $a$,
$x \le n^{n/a} (a \, \omega(x) + 1)^{n \, \omega(x)}$, where $n^{n/a}$ is a real power.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Lemma 2 (`integers-2025-A71-lem-2`). -/
public theorem le_rpow_mul_pow_of_dvd_factorial {n x : ℕ} (hn : 0 < n) (hx : 0 < x)
    (hdvd : x ∣ n !) {a : ℕ} (ha : 0 < a) :
    (x : ℝ) ≤ (n : ℝ) ^ ((n : ℝ) / a) *
      ((a * x.primeFactors.card + 1 : ℕ) : ℝ) ^ (n * x.primeFactors.card) := by
  have hfactor (p : ℕ) (hp : p ∈ x.primeFactors) :
      p ^ x.factorization p ≤ (a * x.primeFactors.card + 1) ^ n := by
    have hprime := prime_of_mem_primeFactors hp
    have hbase : p ≤ 2 ^ (p - 1) := by
      have := Nat.lt_two_pow_self (n := p - 1)
      omega
    have hexp : (p - 1) * x.factorization p ≤ n := calc
      _ ≤ (p - 1) * (n !).factorization p :=
        Nat.mul_le_mul_left _ ((factorization_le_iff_dvd hx.ne' n.factorial_ne_zero).2 hdvd p)
      _ ≤ n := (sub_one_mul_factorization_factorial hprime).trans_le (Nat.sub_le _ _)
    have htwo : 2 ≤ a * x.primeFactors.card + 1 :=
      Nat.succ_le_succ (Nat.mul_pos ha (Finset.card_pos.mpr ⟨p, hp⟩))
    calc
      p ^ x.factorization p ≤ (2 ^ (p - 1)) ^ x.factorization p := Nat.pow_le_pow_left hbase _
      _ = 2 ^ ((p - 1) * x.factorization p) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hexp
      _ ≤ (a * x.primeFactors.card + 1) ^ n := Nat.pow_le_pow_left htwo _
  have hprod : x ≤ (a * x.primeFactors.card + 1) ^ (n * x.primeFactors.card) := calc
    x = ∏ p ∈ x.primeFactors, p ^ x.factorization p := prod_primeFactors_pow_factorization hx.ne'
    _ ≤ ∏ _p ∈ x.primeFactors, (a * x.primeFactors.card + 1) ^ n := Finset.prod_le_prod hfactor
    _ = _ := by rw [Finset.prod_const, ← pow_mul]
  calc
    (x : ℝ) ≤ ((a * x.primeFactors.card + 1 : ℕ) : ℝ) ^ (n * x.primeFactors.card) := by
      exact_mod_cast hprod
    _ ≤ _ := le_mul_of_one_le_left (by positivity)
      (Real.one_le_rpow (by exact_mod_cast hn) (by positivity))

end MetaMathlibExt
