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
public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductThree
public import MathlibExt.Combinatorics.Additive.VanDerWaerdenTransformationSums

namespace MetaMathlibExt

@[expose] public section

-- `not_isMVanishingFamily_sumAddMulProd_six` is proved in
-- `MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductClassification`, re-exported here.

/-- **Nonzero solutions of a two-equation system modulo primes greater than 3 congruent to 3
mod 4.** Let $n > 3$ be a prime with $n \equiv 3 \pmod 4$. Then there are nonzero
$x, y \in \mathbb{Z}/n\mathbb{Z}$ and an integer $r \in \{2, 3\}$ such that $x + ry = 0$ and
$xy^r = 1$ in $\mathbb{Z}/n\mathbb{Z}$.

The source prints the second equation as $xy r = 1$; it is read as $xy^r = 1$, as in the proof,
whose first case computes $xy^2 = x^3/4 = 1$.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 6
(`integers-2026-A25-lem-6`). -/
public theorem_wanted exists_add_mul_eq_zero_mul_pow_eq_one {n : ℕ} (hp : n.Prime)
    (h3 : 3 < n) (h4 : n % 4 = 3) :
    ∃ x y : ZMod n, x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℕ, (r = 2 ∨ r = 3) ∧
      x + r * y = 0 ∧ x * y ^ r = 1

/-- **$F_1$ modulo a prime $n > 3$ with $n \equiv 3 \pmod 4$ is not $m$-vanishing for $m > 0$.**
Let $n > 3$ be a prime with $n \equiv 3 \pmod 4$. Then for every $m > 0$ the sum-plus-product
family $F_1$ over $\mathbb{Z}/n$, $F_1(b_1, \dots, b_l) = b_1 + \dots + b_l + b_1 \cdots b_l$, is
not $m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 7
(`integers-2026-A25-lem-7`). -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_one_prime_three_mod_four
    {n : ℕ} (hp : n.Prime) (h3 : 3 < n) (h4 : n % 4 = 3) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n))

/-- **$F_1$ modulo $8u$ with $u > 1$ is not $m$-vanishing for $m > 0$.** Let $u > 1$ be a natural
number and $n = 8u$. Then for every $m > 0$ the sum-plus-product family $F_1$ over $\mathbb{Z}/n$,
$F_1(b_1, \dots, b_l) = b_1 + \dots + b_l + b_1 \cdots b_l$, is not $m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 8
(`integers-2026-A25-lem-8`). -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_one_eight_mul {u : ℕ}
    (hu : 1 < u) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod (8 * u)))

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
