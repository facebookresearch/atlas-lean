/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Van der Waerden-type vanishing for sum-plus-product families

Statements from Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden
Theorem to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25 (arXiv:2502.07921).
Labels follow the journal numbering (Lemmas 1-9); the arXiv version calls Lemmas 1-5 and
7-9 Propositions 1-5 and 7-9, and Lemma 6 Proposition 6.

A family `F = {f^(l)}_{l ≥ 2}` of functions `f^(l) : (ℤ/n)^l → M` is `m`-vanishing when
every sequence over `ℤ/n` contains `m` consecutive blocks of a common length `l > 1` on which
`f^(l)` vanishes, and vanishing when it is `m`-vanishing for every `m > 0`. Sequences are
indexed from `0` rather than `1`, which does not affect either property. Values of `f^(l)`
at `l < 2` never enter the definitions.
-/
module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Additive.VanDerWaerdenNonvanishingAlternating
public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductFourEight
public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductNine
public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductPrimeOneModFour
public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductPrimeThreeModFour
public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductThree
public import MathlibExt.Combinatorics.Additive.VanDerWaerdenTransformationSums
public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductEightMul
public import MathlibExt.Combinatorics.Additive.VanDerWaerdenZModTwoEquations

namespace MetaMathlibExt

@[expose] public section

-- `not_isMVanishingFamily_sumAddMulProd_six` is proved in
-- `MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductClassification`, re-exported here.

/-- **The sum-minus-product family is vanishing modulo prime powers.** Let $p$ be a prime,
$k > 0$ and $n = p^k$, and let $F_{-1}$ be the family over $\mathbb{Z}/n\mathbb{Z}$ sending a
block $(b_1, \dots, b_l)$ to $\sum_i b_i - \prod_i b_i$. Then $F_{-1}$ is vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 4
(`integers-2026-A25-thm-4`). -/
public theorem_wanted isVanishingFamily_sumAddMulProd_neg_one_prime_pow {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    IsVanishingFamily (sumAddMulProdFamily (-1 : ZMod (p ^ k)))

end

end MetaMathlibExt
