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
public import MathlibExt.NumberTheory.GibonacciNumber
public import MathlibExt.NumberTheory.GibonacciPowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- Lemma 9: the values `H_n / H_{n+1}` (`n ∈ ℤ`, `H_{n+1} ≠ 0`) of the
sequence with `H_0 = -b`, `H_1 = a` are exactly the values
`-G_{n+1} / G_n` (`n ∈ ℤ`, `G_n ≠ 0`) of the Gibonacci sequence with
`G_0 = a`, `G_1 = b`; both index sets run over the two-sided orbits.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 9 (`jis-2024-24.3.1-lem-9`). -/
public theorem_wanted gibonacci_shifted_ratios_eq_negated_ratios (a b : ℤ) :
    {x : ℚ | ∃ v ∈ fibonacciPairOrbit (-b, a), v.2 ≠ 0 ∧ x = (v.1 : ℚ) / v.2} =
      {x : ℚ | ∃ w ∈ fibonacciPairOrbit (a, b), w.1 ≠ 0 ∧ x = -(w.2 : ℚ) / w.1}

/-- Lemma 11: `M(a, b, p+q, p+2q) = -3M(a, b, q, p+q) - M(a, b, p, q)` and
`M(a,b,p,q)² + 3M(a,b,p,q)M(a,b,q,p+q) + M(a,b,q,p+q)² = a² + ab - b²`.
Stated for every `(p, q) ≠ (0, 0)`; the paper assumes `q ≠ 0`,
`p + q ≠ 0`, `p + 2q ≠ 0`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 11 (`jis-2024-24.3.1-lem-11`). -/
public theorem_wanted knappM_recurrence_and_quadratic (a b p q : ℤ) (hpq : (p, q) ≠ (0, 0)) :
    knappM a b (p + q) (p + 2 * q) = -3 * knappM a b q (p + q) - knappM a b p q ∧
      knappM a b p q ^ 2 + 3 * knappM a b p q * knappM a b q (p + q) +
          knappM a b q (p + q) ^ 2 = ((a ^ 2 + a * b - b ^ 2 : ℤ) : ℚ)

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

/-- Theorem 4: for `(a, b) ≠ (0, 0)`, (i) every integer solution `(M, k)`,
`k ≠ 0`, of `M² = 5k² + (2b - 6a)k + (a - b)²` gives a good value
`x = (a - b - k + M) / 2k` (whose family is good by Theorem 1); (ii) every
family of good values other than the Fibonacci family (the one containing
`0`) and the family containing a zero of `G^{(a,b)}` has a member
`x = (a - b - k + M) / 2k` with `k ≠ 0`, `M² = 5k² + (2b - 6a)k + (a - b)²`,
`|M| ≤ C` (written `M² ≤ |a² + ab - b²|` if `a² + ab - b² < 0` and
`5M² ≤ a² + ab - b²` if it is positive) and an integer `N` with
`M² + 3MN + N² = a² + ab - b²`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Theorem 4 (`jis-2024-24.3.1-thm-4`). -/
public theorem_wanted gibonacci_good_families_classification (a b : ℤ) (hab : (a, b) ≠ (0, 0)) :
    (∀ M k : ℤ, k ≠ 0 → M ^ 2 = 5 * k ^ 2 + (2 * b - 6 * a) * k + (a - b) ^ 2 →
        IsGibonacciGood a b (((a - b - k + M : ℤ) : ℚ) / (2 * k))) ∧
      ∀ p q : ℤ, Int.gcd p q = 1 → q ≠ 0 → IsGibonacciGood a b ((p : ℚ) / q) →
        (∀ v ∈ fibonacciPairOrbit (p, q), v.2 ≠ 0 →
          (v.1 : ℚ) / v.2 ≠ 0 ∧ gibonacciGeneratingValue a b ((v.1 : ℚ) / v.2) ≠ 0) →
        ∃ v ∈ fibonacciPairOrbit (p, q), v.2 ≠ 0 ∧ ∃ M k N : ℤ, k ≠ 0 ∧
          (a ^ 2 + a * b - b ^ 2 < 0 → M ^ 2 ≤ -(a ^ 2 + a * b - b ^ 2)) ∧
          (0 < a ^ 2 + a * b - b ^ 2 → 5 * M ^ 2 ≤ a ^ 2 + a * b - b ^ 2) ∧
          M ^ 2 + 3 * M * N + N ^ 2 = a ^ 2 + a * b - b ^ 2 ∧
          M ^ 2 = 5 * k ^ 2 + (2 * b - 6 * a) * k + (a - b) ^ 2 ∧
          (v.1 : ℚ) / v.2 = ((a - b - k + M : ℤ) : ℚ) / (2 * k)

end

end MetaMathlibExt
