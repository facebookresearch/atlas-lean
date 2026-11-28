/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.FibonacciGeneratingFunctions
public import MathlibExt.NumberTheory.FibonacciGeneratingFunctionsClassification
public import MathlibExt.NumberTheory.FibonacciGeneratingFunctionsKnappMRelations
public import MathlibExt.NumberTheory.GibonacciNumber
public import MathlibExt.NumberTheory.GibonacciPowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- Lemma 12: if `a² + ab - b² < 0` and `p / q` (lowest terms) is good for
`(a, b)`, some consecutive pair `(H_n, H_{n+1})` of its family has
`M(a, b, H_n, H_{n+1})² ≤ |a² + ab - b²|`. The pairs include one with
`H_{n+1} = 0` when the family is the Fibonacci one, as in the paper's
remark on the example `(a, b) = (1, 11)` (`M(1, 11, 1, 0) = -10`); without it the bound fails for
`(a, b) = (1, 11)`, `x = 0` (least `|M|` over pairs with `H_{n+1} ≠ 0`
is `11 > √109`).

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 12 (`jis-2024-24.3.1-lem-12`). -/
public theorem_wanted knappM_small_of_neg (a b p q : ℤ) (hD : a ^ 2 + a * b - b ^ 2 < 0)
    (hcop : Int.gcd p q = 1) (hq : q ≠ 0) (hgood : IsGibonacciGood a b ((p : ℚ) / q)) :
    ∃ v ∈ fibonacciPairOrbit (p, q),
      knappM a b v.1 v.2 ^ 2 ≤ |((a ^ 2 + a * b - b ^ 2 : ℤ) : ℚ)|

/-- Lemma 13: if `a² + ab - b² > 0` and `p / q` (lowest terms) is good for
`(a, b)`, some consecutive pair of its family has
`5 M(a, b, H_n, H_{n+1})² ≤ a² + ab - b²`, with pairs as in Lemma 12.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 13 (`jis-2024-24.3.1-lem-13`). -/
public theorem_wanted knappM_small_of_pos (a b p q : ℤ) (hD : 0 < a ^ 2 + a * b - b ^ 2)
    (hcop : Int.gcd p q = 1) (hq : q ≠ 0) (hgood : IsGibonacciGood a b ((p : ℚ) / q)) :
    ∃ v ∈ fibonacciPairOrbit (p, q),
      5 * knappM a b v.1 v.2 ^ 2 ≤ ((a ^ 2 + a * b - b ^ 2 : ℤ) : ℚ)

end

end MetaMathlibExt
