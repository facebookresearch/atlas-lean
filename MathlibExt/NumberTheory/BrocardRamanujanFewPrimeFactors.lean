/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Order.Filter.AtTopBot.Finite

/-!
# Brocard–Ramanujan solutions with `x - 1` or `x + 1` having few prime factors

`MetaMathlibExt.brocardRamanujan_fewPrimeFactors_finite` proves that for every `l ≥ 2` there are
only finitely many pairs of natural numbers `(n, x)` with `n! + 1 = x ^ 2` such that `x - 1` or
`x + 1` has fewer than `l` distinct prime divisors.

The statement is from Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with
7-Free Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 1(ii).

The condition "`x ± 1` has fewer than `l` prime divisors" is read as "`x - 1` or `x + 1` has".
The paper's own specialisation forces this reading: `(4, 5)` is listed as a solution with
`x ± 1` a prime power, while `x - 1 = 4 = 2 ^ 2` is a prime power and `x + 1 = 6` is not. Prime
divisors are counted without multiplicity, matching the specialisation `l = 2` to prime powers.
Solutions are taken with `x` a natural number. Negative `x` mirror positive ones: `x ↦ -x` swaps
`|x - 1|` and `|x + 1|`, so the disjunctive condition is unchanged.

## Proof

Write `n! = (x - 1) (x + 1)` and let `d` be the factor with fewer than `l` prime divisors. For
each prime `p`, Legendre's formula gives `(p - 1) v_p(n!) ≤ n`, so
`p ^ v_p(d) ≤ (2 ^ (p - 1)) ^ v_p(n!) ≤ 2 ^ n`, and hence `d ≤ 2 ^ (n l)`. Therefore
`n! < x ^ 2 ≤ (d + 1) ^ 2 ≤ 4 (4 ^ l) ^ n`, which fails for large `n` because `n!` eventually
exceeds `a c ^ n` for all natural numbers `a` and `c`. Since `n` determines `x`, there are only
finitely many solutions. The argument does not use the hypothesis `l ≥ 2`, which is kept from the
source.
-/

open Nat

namespace MetaMathlibExt

/-- A positive divisor `d` of `n!` satisfies `d ≤ 2 ^ (n ω(d))`, where `ω(d)` is the number of
distinct prime divisors of `d`: by Legendre's formula `(p - 1) v_p(n!) ≤ n`, so every prime
power `p ^ v_p(d)` dividing `d` exactly is at most `(2 ^ (p - 1)) ^ v_p(n!) ≤ 2 ^ n`. -/
private theorem le_two_pow_of_dvd_factorial {n d : ℕ} (hd : d ≠ 0) (hdvd : d ∣ n !) :
    d ≤ 2 ^ (n * d.primeFactors.card) := by
  have hfactor (p : ℕ) (hp : p ∈ d.primeFactors) : p ^ d.factorization p ≤ 2 ^ n := by
    have hbase : p ≤ 2 ^ (p - 1) := by
      have := Nat.lt_two_pow_self (n := p - 1)
      omega
    have hexp : (p - 1) * d.factorization p ≤ n := calc
      _ ≤ (p - 1) * (n !).factorization p :=
        Nat.mul_le_mul_left _ ((factorization_le_iff_dvd hd n.factorial_ne_zero).2 hdvd p)
      _ ≤ n := (sub_one_mul_factorization_factorial (prime_of_mem_primeFactors hp)).trans_le
        (Nat.sub_le _ _)
    calc
      p ^ d.factorization p ≤ (2 ^ (p - 1)) ^ d.factorization p := Nat.pow_le_pow_left hbase _
      _ = 2 ^ ((p - 1) * d.factorization p) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hexp
  calc
    d = ∏ p ∈ d.primeFactors, p ^ d.factorization p := prod_primeFactors_pow_factorization hd
    _ ≤ ∏ _p ∈ d.primeFactors, 2 ^ n := Finset.prod_le_prod hfactor
    _ = 2 ^ (n * d.primeFactors.card) := by rw [Finset.prod_const, ← pow_mul]

-- The source assumes `l ≥ 2`, although the finiteness also holds for `l < 2`.
set_option linter.unusedVariables false in
/-- **Brocard–Ramanujan solutions with $x - 1$ or $x + 1$ having few prime factors are finite.**
For every natural number $l \ge 2$, there are only finitely many pairs of natural numbers
$(n, x)$ with $n! + 1 = x^2$ such that $x - 1$ or $x + 1$ has fewer than $l$ distinct prime
divisors.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 1(ii), first
sentence (`integers-2025-A71-thm-1`). -/
public theorem brocardRamanujan_fewPrimeFactors_finite (l : ℕ) (hl : 2 ≤ l) :
    {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
      ((p.2 - 1).primeFactors.card < l ∨ (p.2 + 1).primeFactors.card < l)}.Finite := by
  -- Past `N`, the factorial exceeds the bound `4 (4 ^ l) ^ n` that every solution satisfies.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (Nat.eventually_mul_pow_lt_factorial_sub 4 (4 ^ l) 0)
  refine ((Set.finite_Iio N).image fun n => (n, Nat.sqrt (n ! + 1))).subset ?_
  rintro ⟨n, x⟩ ⟨hsol, hfew⟩
  dsimp only at hsol hfew
  refine ⟨n, Set.mem_Iio.2 ?_, by simp [hsol, Nat.sqrt_eq']⟩
  by_contra! hn
  have hlt : 4 * (4 ^ l) ^ n < n ! := by simpa using hN n hn
  have hx : 2 ≤ x := by nlinarith [n.factorial_pos]
  have hprod : (x - 1) * (x + 1) = n ! := by
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    nlinarith
  -- The factor of `n!` with fewer than `l` prime divisors is at most `2 ^ (n l)`.
  have hbound : x ≤ 2 ^ (n * l) + 1 := by
    rcases hfew with h | h
    · have hd := le_two_pow_of_dvd_factorial (by omega) (Dvd.intro _ hprod)
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.mul_le_mul_left n h.le)
      omega
    · have hd := le_two_pow_of_dvd_factorial (by omega) (Dvd.intro_left _ hprod)
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.mul_le_mul_left n h.le)
      omega
  have hpow : (4 ^ l) ^ n = (2 ^ (n * l)) ^ 2 := by
    rw [← pow_mul, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring
  have hone : 1 ≤ 2 ^ (n * l) := Nat.one_le_two_pow
  rw [hpow] at hlt
  nlinarith

end MetaMathlibExt
