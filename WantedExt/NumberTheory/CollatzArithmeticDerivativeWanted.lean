/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The arithmetic derivative commuting with the Collatz map

Statements from Zachary P. Bradshaw, "On a Family of Solutions to Arithmetic Differential
Equations Involving the Collatz Map", *Journal of Integer Sequences* 28 (2025), Article 25.1.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.html>).

The arithmetic derivative `D` is `arithmeticDerivative`
(`MathlibExt/NumberTheory/ArithmeticDerivative.lean`), given by the paper's explicit formula
`D(n) = ∑_{p ∣ n} ν_p(n) · n / p` (so `D(0) = D(1) = 0`, `D(p) = 1` for primes `p`, and the
Leibniz rule holds). The paper's Collatz map is the accelerated map
`C(n) = (3n + 1)/2` for odd `n`, `C(n) = n/2` for even `n` (`collatzAccelerated`). The paper's
sequence `(aₙ)` lists the positive integers `n` with `D(C(n)) = C(D(n))`; statements about
`aₙ` are stated for every positive `n` with this property. Semiprimes `pq` and `rs` are
*compatible* (`IsCompatibleSemiprimePair p q r s`) when `p, q, r, s` are primes and `r, s` are
the roots of `2x² - (p + q)x + 3pq + 1 = 0`, that is, `2(r + s) = p + q` and
`2rs = 3pq + 1`.

The statements already proved, such as the oddness of every positive `n` with
`D(C(n)) = C(D(n))` and the prime gap bound for semiprime solutions, live in
`MathlibExt/NumberTheory/CollatzArithmeticDerivative.lean`, which this module imports publicly.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.ArithmeticDerivative
public import MathlibExt.NumberTheory.CollatzArithmeticDerivative

namespace MetaMathlibExt

@[expose] public section

/-- **Bounds for the arithmetic derivative.** Let $n \ge 2$ be a natural number, let $p$ be the
least prime factor of $n$, and let $\Omega(n)$ be the number of prime factors of $n$ counted with
multiplicity. Then the arithmetic derivative $D(n)$ satisfies
$$\Omega(n) \, n^{(\Omega(n) - 1)/\Omega(n)} \le D(n) \le \frac{n \log_p n}{p},$$
and each of the two inequalities is an equality if and only if $n$ is a prime power.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Lemma 1
(`jis-2025-25.1.8-lem-1`). -/
public theorem_wanted arithmeticDerivative_bounds (n : ℕ) (hn : 2 ≤ n) :
    let om : ℝ := n.primeFactorsList.length
    let p : ℝ := n.minFac
    let lower : ℝ := om * (n : ℝ) ^ ((om - 1) / om)
    let upper : ℝ := n * Real.logb p n / p
    lower ≤ arithmeticDerivative n ∧ (arithmeticDerivative n : ℝ) ≤ upper ∧
      (lower = arithmeticDerivative n ↔ IsPrimePow n) ∧
      ((arithmeticDerivative n : ℝ) = upper ↔ IsPrimePow n)

/-- **Positive solutions of the Collatz arithmetic differential equation are composite.** Let
$D$ be the arithmetic derivative and $C$ the accelerated Collatz map. Every positive integer $n$
with $D(C(n)) = C(D(n))$ is composite, that is, $n > 1$ and $n$ is not prime.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 3 (`jis-2025-25.1.8-prop-3`). -/
public theorem_wanted composite_of_arithmeticDerivative_collatz_comm (n : ℕ) (hn : 0 < n)
    (h : arithmeticDerivative (collatzAccelerated n) =
      collatzAccelerated (arithmeticDerivative n)) :
    1 < n ∧ ¬ n.Prime

/-- **Prime tetrations where the arithmetic derivative and the Collatz map commute.** Let $D$ be
the arithmetic derivative and $C$ the accelerated Collatz map. For a prime $p$,
$D(C(p^p)) = C(D(p^p))$ if and only if $C(p^p) = q^q$ for some prime $q$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 4 (`jis-2025-25.1.8-prop-4`). -/
public theorem_wanted arithmeticDerivative_collatz_comm_prime_tetration_iff (p : ℕ)
    (hp : p.Prime) :
    arithmeticDerivative (collatzAccelerated (p ^ p)) =
        collatzAccelerated (arithmeticDerivative (p ^ p)) ↔
      ∃ q : ℕ, q.Prime ∧ collatzAccelerated (p ^ p) = q ^ q

/-- **No special semiprime solves the derivative–Collatz equation.** Let $D$ be the arithmetic
derivative and let $C$ be the accelerated Collatz map, $C(n) = n/2$ for even $n$ and
$C(n) = (3n + 1)/2$ for odd $n$. Let $n$ be a positive integer with $D(C(n)) = C(D(n))$ and let
$p$ be a prime. Then $n \ne p^2$; if $p + 2$ is prime then $n \ne p(p + 2)$; if $p + 4$ is prime
then $n \ne p(p + 4)$; and if $2p + 1$ is prime then $n \ne p(2p + 1)$. Thus no such $n$ is the
square of a prime, a product of twin primes, a product of cousin primes, or the product of a
Sophie Germain prime and its safe prime.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Corollary 6 (`jis-2025-25.1.8-cor-6`). -/
public theorem_wanted not_special_semiprime_of_arithmeticDerivative_collatz_comm (n : ℕ)
    (hn : 0 < n)
    (h : arithmeticDerivative (collatzAccelerated n) =
      collatzAccelerated (arithmeticDerivative n))
    (p : ℕ) (hp : p.Prime) :
    n ≠ p ^ 2 ∧ ((p + 2).Prime → n ≠ p * (p + 2)) ∧ ((p + 4).Prime → n ≠ p * (p + 4)) ∧
      ((2 * p + 1).Prime → n ≠ p * (2 * p + 1))

/-- **Prime roots give semiprime solutions.** Let $D$ be the arithmetic derivative and $C$ the
accelerated Collatz map. Let $p$ and $q$ be primes and let $t \ge 0$ be an integer with
$t^2 = p^2 - 22pq + q^2 - 8$. If $r = (p + q + t)/4$ and $s = (p + q - t)/4$ are both primes,
then $C(pq) = rs$ and $D(C(pq)) = C(D(pq))$.

The numbers $r$ and $s$ are the roots $(p + q \pm \sqrt{p^2 - 22pq + q^2 - 8})/4$ of
$2x^2 - (p + q)x + 3pq + 1 = 0$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 7 (`jis-2025-25.1.8-prop-7`). -/
public theorem_wanted collatzAccelerated_mul_eq_and_comm_of_roots_prime (p q r s t : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (ht : (t : ℤ) ^ 2 = (p : ℤ) ^ 2 - 22 * p * q + (q : ℤ) ^ 2 - 8)
    (hr' : 4 * (r : ℤ) = p + q + t) (hs' : 4 * (s : ℤ) = p + q - t) :
    collatzAccelerated (p * q) = r * s ∧
      arithmeticDerivative (collatzAccelerated (p * q)) =
        collatzAccelerated (arithmeticDerivative (p * q))

/-- **Compatible semiprimes have odd prime factors.** Let $p, q, r, s$ be primes with
$2(r + s) = p + q$ and $2rs = 3pq + 1$, so that the semiprimes $pq$ and $rs$ are compatible.
Then $p$, $q$, $r$ and $s$ are all odd.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Lemma 9
(`jis-2025-25.1.8-lem-9`). -/
public theorem_wanted IsCompatibleSemiprimePair.odd {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    Odd p ∧ Odd q ∧ Odd r ∧ Odd s

/-- **Bounds on the factors of compatible semiprimes.** Suppose the semiprimes $pq$ and $rs$ are
compatible, where $q < p$. Then $r \ge 241$, $s \ge 241$, $3q < r < 3p$ and $3q < s < 3p$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Lemma 11
(`jis-2025-25.1.8-lem-11`). -/
public theorem_wanted IsCompatibleSemiprimePair.bounds {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) (hqp : q < p) :
    241 ≤ r ∧ 241 ≤ s ∧ 3 * q < r ∧ 3 * q < s ∧ r < 3 * p ∧ s < 3 * p

/-- **Compatible semiprimes modulo 5.** Let $p, q, r, s$ be primes with $2(r + s) = p + q$ and
$2rs = 3pq + 1$, so that the semiprimes $pq$ and $rs$ are compatible. Then one of $p, q$ is
congruent to $1$ and the other to $4$ modulo $5$, and likewise one of $r, s$ is congruent to $1$
and the other to $4$ modulo $5$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 12 (`jis-2025-25.1.8-prop-12`). -/
public theorem_wanted IsCompatibleSemiprimePair.mod_five {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    ((p % 5 = 1 ∧ q % 5 = 4) ∨ (q % 5 = 1 ∧ p % 5 = 4)) ∧
      ((r % 5 = 1 ∧ s % 5 = 4) ∨ (s % 5 = 1 ∧ r % 5 = 4))

/-- **Compatible semiprimes modulo 10.** Let $p, q, r, s$ be primes with $2(r + s) = p + q$ and
$2rs = 3pq + 1$, so that the semiprimes $pq$ and $rs$ are compatible. Then one of $p, q$ is
congruent to $1$ and the other to $9$ modulo $10$, and likewise one of $r, s$ is congruent to $1$
and the other to $9$ modulo $10$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 13 (`jis-2025-25.1.8-prop-13`). -/
public theorem_wanted IsCompatibleSemiprimePair.mod_ten {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    ((p % 10 = 1 ∧ q % 10 = 9) ∨ (p % 10 = 9 ∧ q % 10 = 1)) ∧
      ((r % 10 = 1 ∧ s % 10 = 9) ∨ (r % 10 = 9 ∧ s % 10 = 1))

/-- **Reciprocals of compatible semiprimes have a finite sum.** Call a natural number $n$ a
compatible semiprime if $n = pq$ for primes $p, q$ for which there are primes $r, s$ with
$2(r + s) = p + q$ and $2rs = 3pq + 1$. The sum of $1/n$ over all compatible semiprimes $n$
converges.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Theorem 14 (`jis-2025-25.1.8-thm-14`). -/
public theorem_wanted summable_inv_compatibleSemiprimes :
    Summable (Set.indicator {n : ℕ | ∃ p q r s, IsCompatibleSemiprimePair p q r s ∧ n = p * q}
      fun n => (1 : ℝ) / n)

end

end MetaMathlibExt
