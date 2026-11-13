/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.PrimeFin
public import MathlibExt.NumberTheory.PowerFree
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorization.Defs

/-!
# The Brocard-Ramanujan equation with `k`-free integers and prime powers

Statements from Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with
7-Free Integers and Prime Powers*, INTEGERS 25 (2025), Article A71.

The condition "`x ± 1` is `k`-free" (respectively "has fewer than `l` prime
divisors", "is a prime power") is read as "`x - 1` or `x + 1` is". The paper's own
specialisation forces this reading: `(4, 5)` is listed as a solution with
`x ± 1` a prime power, while `x - 1 = 4 = 2 ^ 2` is a prime power and
`x + 1 = 6` is not. Prime divisors are counted without multiplicity, matching the
specialisation `l = 2` to prime powers.

In the Theorem 1 statements solutions are taken with `x` a natural number. Negative `x`
mirror positive ones: `x ↦ -x` swaps `|x - 1|` and `|x + 1|`, so the disjunctive conditions
are unchanged. Theorem 2 keeps `x` an integer, as the paper states it ("finitely many integer
solutions"): for a fixed polynomial `P`, negating `x` does not preserve
`x = x_1 ⋯ x_m P(x_1, …, x_m) ± 1`.
-/

open Nat

namespace MetaMathlibExt

@[expose] public section

/-- **Brocard–Ramanujan solutions with $x - 1$ or $x + 1$ power-free are finite.** For every
natural number $k \ge 2$, there are only finitely many pairs of natural numbers $(n, x)$ with
$n! + 1 = x^2$ such that $x - 1$ or $x + 1$ is $k$-free.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 1(i), first
sentence (`integers-2025-A71-thm-1`). -/
public theorem_wanted brocardRamanujan_powerFree_finite (k : ℕ) (hk : 2 ≤ k) :
    {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
      ((p.2 - 1).IsPowerFree k ∨ (p.2 + 1).IsPowerFree k)}.Finite

/-- **Brocard–Ramanujan solutions with $x - 1$ or $x + 1$ seven-free.** If natural numbers $n$
and $x$ satisfy $n! + 1 = x^2$ and $x - 1$ or $x + 1$ is $7$-free, then $(n, x)$ is one of
$(4, 5)$, $(5, 11)$ and $(7, 71)$.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 1(i),
second sentence (`integers-2025-A71-thm-1`). -/
public theorem_wanted brocardRamanujan_sevenFree_subset :
    {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
      ((p.2 - 1).IsPowerFree 7 ∨ (p.2 + 1).IsPowerFree 7)} ⊆
      {(4, 5), (5, 11), (7, 71)}

/-- **Brocard–Ramanujan solutions with $x - 1$ or $x + 1$ having few prime factors are finite.**
For every natural number $l \ge 2$, there are only finitely many pairs of natural numbers
$(n, x)$ with $n! + 1 = x^2$ such that $x - 1$ or $x + 1$ has fewer than $l$ distinct prime
divisors.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 1(ii), first
sentence (`integers-2025-A71-thm-1`). -/
public theorem_wanted brocardRamanujan_fewPrimeFactors_finite (l : ℕ) (hl : 2 ≤ l) :
    {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
      ((p.2 - 1).primeFactors.card < l ∨ (p.2 + 1).primeFactors.card < l)}.Finite

/-- **Brocard–Ramanujan solutions with $x - 1$ or $x + 1$ a prime power.** If natural numbers
$n$ and $x$ satisfy $n! + 1 = x^2$ and $x - 1$ or $x + 1$ is a prime power, then
$(n, x) = (4, 5)$.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 1(ii),
second sentence (`integers-2025-A71-thm-1`). -/
public theorem_wanted brocardRamanujan_primePow_subset :
    {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧ (IsPrimePow (p.2 - 1) ∨ IsPrimePow (p.2 + 1))} ⊆
      {(4, 5)}

/-- **Divisors of a factorial bounded by their largest prime exponent.** Let $n \ge 1$ and let
$x$ be a positive integer dividing $n!$. Write $K(x)$ for the largest exponent in the prime
factorization of $x$, with $K(1) = 0$. Then $x \le \exp(3 n K(x) / 2)$.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Lemma 1 (`integers-2025-A71-lem-1`). -/
public theorem_wanted le_exp_of_dvd_factorial {n x : ℕ} (hn : 0 < n) (hx : 0 < x)
    (hdvd : x ∣ n !) :
    (x : ℝ) ≤ Real.exp (3 * n * (x.primeFactors.sup x.factorization : ℕ) / 2)

/-- **Divisors of a factorial bounded by their number of prime factors.** Let $n \ge 1$ and let
$x$ be a positive integer dividing $n!$, and write $\omega(x)$ for the number of distinct prime
divisors of $x$. Then for every positive integer $a$,
$x \le n^{n/a} (a \, \omega(x) + 1)^{n \, \omega(x)}$, where $n^{n/a}$ is a real power.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Lemma 2 (`integers-2025-A71-lem-2`). -/
public theorem_wanted le_rpow_mul_pow_of_dvd_factorial {n x : ℕ} (hn : 0 < n) (hx : 0 < x)
    (hdvd : x ∣ n !) {a : ℕ} (ha : 0 < a) :
    (x : ℝ) ≤ (n : ℝ) ^ ((n : ℝ) / a) *
      ((a * x.primeFactors.card + 1 : ℕ) : ℝ) ^ (n * x.primeFactors.card)

/-- **Finitely many Brocard–Ramanujan solutions of polynomial shape.** Let $k \ge 2$, $l \ge 2$
and $m \ge 1$ be natural numbers and let $P \in \mathbb{Z}[X_1, \ldots, X_m]$. Write
$F_k P_l$ for the set of products $y z$ of a $k$-free number $y$ and a positive integer $z$
with fewer than $l$ distinct prime divisors. Then there are only finitely many pairs $(n, x)$
of a natural number $n$ and an integer $x$ such that $n! + 1 = x^2$ and
$x = x_1 \cdots x_m P(x_1, \ldots, x_m) + 1$ or $x = x_1 \cdots x_m P(x_1, \ldots, x_m) - 1$
for some $x_1, \ldots, x_m \in F_k P_l$.

Here $x$ ranges over the integers, since negating $x$ does not preserve the shape
$x_1 \cdots x_m P(x_1, \ldots, x_m) \pm 1$.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 2 (`integers-2025-A71-thm-2`). -/
public theorem_wanted brocardRamanujan_polynomial_powerFree_mul_fewPrimeFactors_finite
    {k l m : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l) (hm : 1 ≤ m) (P : MvPolynomial (Fin m) ℤ) :
    {p : ℕ × ℤ | ((p.1 ! : ℕ) : ℤ) + 1 = p.2 ^ 2 ∧
      ∃ xs : Fin m → ℕ, (∀ i, ∃ y z : ℕ, xs i = y * z ∧ y.IsPowerFree k ∧ 0 < z ∧
          z.primeFactors.card < l) ∧
        (p.2 = (∏ i, (xs i : ℤ)) * MvPolynomial.eval (fun i => (xs i : ℤ)) P + 1 ∨
          p.2 = (∏ i, (xs i : ℤ)) * MvPolynomial.eval (fun i => (xs i : ℤ)) P - 1)}.Finite

end

end MetaMathlibExt
