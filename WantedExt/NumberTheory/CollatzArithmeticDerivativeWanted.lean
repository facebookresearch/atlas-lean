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
