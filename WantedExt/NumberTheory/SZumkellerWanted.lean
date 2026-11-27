/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generalized Zumkeller numbers

Statements from Jayanta Kalita and Helen K. Saikia, "A Study on Generalized
Zumkeller Numbers", *INTEGERS* 24 (2024), Article A95.

`n` is *s-Zumkeller* when its proper divisors split into two parts with equal
sums of squares (`IsSZumkeller`), and *unitary s-Zumkeller* when its proper
unitary divisors (MathlibExt's `Nat.unitaryDivisors n` without `n`) do
(`IsUnitarySZumkeller`). Both parts are required to be nonempty, as in a
partition `{A, B}`; this only excludes `n = 1`, whose empty divisor set would
otherwise split trivially (and would contradict Proposition 13).

`σ₂(n)` is `ArithmeticFunction.sigma 2 n`, `τ(n)` is `n.divisors.card`, and the
harmonic mean of the squared divisors is `H₂(n) = τ(n) / ∑_{d ∣ n} 1/d²`,
written out in `ℚ`. The paper's factorizations `n = n₁ n₂ ⋯ n_m` into pairwise
coprime factors `n₁ < ⋯ < n_m` (Lemma 3(ii), Propositions 11 and 12) are read,
as in the paper's Remark 2, as the prime-power components of `n`; then `n₁` is
the least unitary divisor of `n` exceeding `1`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.SZumkeller
public import MathlibExt.NumberTheory.SumSquaredDivisorsProduct
public import MathlibExt.NumberTheory.UnitaryDivisorCount
public import MathlibExt.NumberTheory.SZumkellerHarmonicMeanSqLeOfIsSZumkeller
public import MathlibExt.NumberTheory.SZumkellerSixDvdOfIsSZumkeller
public import MathlibExt.NumberTheory.SZumkellerThreeLeCardPrimeFactorsOfIsSZumkellerEven
public import MathlibExt.NumberTheory.SZumkellerNotIsUnitarySZumkellerOfOdd
public import MathlibExt.NumberTheory.SZumkellerCardUnitaryDivisorsOfIsUnitarySZumkeller
public import MathlibExt.NumberTheory.SZumkellerIsUnitarySZumkellerBounds
public import MathlibExt.NumberTheory.SZumkellerEightLeCardPrimeFactorsOfIsSZumkellerOdd
public import MathlibExt.NumberTheory.SZumkellerTwelveLeCardDivisorsOfIsSZumkeller
public import MathlibExt.NumberTheory.SZumkellerIsSZumkellerEvenProps

namespace MetaMathlibExt

@[expose] public section

/-- **A prime-factor product bound for s-Zumkeller numbers.** Let $n$ be an s-Zumkeller number
and let $p_1$ be its least prime factor. Then
$$\frac{2}{p_1^2} + 1 < \prod_{p} \frac{p^2}{p^2 - 1},$$
where the product ranges over the distinct prime factors $p$ of $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 5. -/
public theorem_wanted two_div_minFac_sq_add_one_lt_prod (n : ℕ) (h : IsSZumkeller n) :
    2 / (n.minFac : ℚ) ^ 2 + 1 < ∏ p ∈ n.primeFactors, (p : ℚ) ^ 2 / (p ^ 2 - 1)

/-- **Odd s-Zumkeller numbers are perfect squares.** Every odd s-Zumkeller number is a perfect
square.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 7. -/
public theorem_wanted isSquare_of_isSZumkeller_odd (n : ℕ) (h : IsSZumkeller n) (ho : Odd n) :
    IsSquare n

/-- **Lower bound for odd s-Zumkeller numbers divisible by 3.** Every odd s-Zumkeller number $n$
divisible by $3$ satisfies
$n \ge 12442607161209225 = (3 \cdot 5 \cdot 7 \cdot 11 \cdot 13 \cdot 17 \cdot 19 \cdot 23)^2$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 8. -/
public theorem_wanted le_of_isSZumkeller_odd_three_dvd (n : ℕ) (h : IsSZumkeller n)
    (ho : Odd n) (h3 : 3 ∣ n) : 12442607161209225 ≤ n

end

end MetaMathlibExt
