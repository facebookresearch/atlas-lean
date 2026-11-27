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
`MathlibExt/NumberTheory/CollatzArithmeticDerivative.lean`, except
`IsCompatibleSemiprimePair.mod_five`, which lives in
`MathlibExt/NumberTheory/CollatzArithmeticDerivativeModFive.lean`,
`IsCompatibleSemiprimePair.bounds`, which lives in
`MathlibExt/NumberTheory/CollatzArithmeticDerivativeBounds.lean`, and
`arithmeticDerivative_bounds`, which lives in
`MathlibExt/NumberTheory/CollatzArithmeticDerivativeArithmeticDerivativeBounds.lean`; this
module imports all four publicly.
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
public import MathlibExt.NumberTheory.CollatzArithmeticDerivativeModFive
public import MathlibExt.NumberTheory.CollatzArithmeticDerivativeBounds
public import MathlibExt.NumberTheory.CollatzArithmeticDerivativeArithmeticDerivativeBounds
public import MathlibExt.NumberTheory.CollatzArithmeticDerivativePrimeTetration

namespace MetaMathlibExt

@[expose] public section

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
