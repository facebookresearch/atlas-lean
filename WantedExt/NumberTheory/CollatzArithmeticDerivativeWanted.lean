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
`IsCompatibleSemiprimePair.mod_ten`, which lives in
`MathlibExt/NumberTheory/CollatzArithmeticDerivativeModTen.lean`,
`IsCompatibleSemiprimePair.bounds`, which lives in
`MathlibExt/NumberTheory/CollatzArithmeticDerivativeBounds.lean`,
`arithmeticDerivative_bounds`, which lives in
`MathlibExt/NumberTheory/CollatzArithmeticDerivativeArithmeticDerivativeBounds.lean`, and
`arithmeticDerivative_collatz_comm_prime_tetration_iff`, which lives in
`MathlibExt/NumberTheory/CollatzArithmeticDerivativePrimeTetration.lean`; this module publicly
imports each of these modules. It also publicly imports the prime-roots criterion from
`MathlibExt/NumberTheory/CollatzArithmeticDerivativePrimeRoots.lean`.
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
public import MathlibExt.NumberTheory.CollatzArithmeticDerivativeModTen
public import MathlibExt.NumberTheory.CollatzArithmeticDerivativeBounds
public import MathlibExt.NumberTheory.CompatibleSemiprimeReciprocals
public import MathlibExt.NumberTheory.CollatzArithmeticDerivativeArithmeticDerivativeBounds
public import MathlibExt.NumberTheory.CollatzArithmeticDerivativePrimeTetration
public import MathlibExt.NumberTheory.CollatzArithmeticDerivativePrimeRoots

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

/-- **Compatible semiprimes have odd prime factors.** Let $p, q, r, s$ be primes with
$2(r + s) = p + q$ and $2rs = 3pq + 1$, so that the semiprimes $pq$ and $rs$ are compatible.
Then $p$, $q$, $r$ and $s$ are all odd.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Lemma 9
(`jis-2025-25.1.8-lem-9`). -/
public theorem_wanted IsCompatibleSemiprimePair.odd {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    Odd p ∧ Odd q ∧ Odd r ∧ Odd s

-- The reciprocal series is proved in
-- `MathlibExt.NumberTheory.CompatibleSemiprimeReciprocals`, which this module publicly imports.

end

end MetaMathlibExt
