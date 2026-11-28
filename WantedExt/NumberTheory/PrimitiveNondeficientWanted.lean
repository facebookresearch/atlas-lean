/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Must a primitive non-deficient number always have a small component?

Statements from Joshua Zelinsky, "Must a Primitive Non-Deficient
Number Always Have a Small Component?", *Journal of Integer
Sequences* 29 (2026), Article 26.4.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Zelinsky/zel14.tex>).

Definitions follow the paper (TeX lines 88-92) and the encoding
already used by the MathlibExt proof of the paper's main theorem
(`MetaMathlibExt.primitive_nondeficient_prime_power_bound`):
`n` is *non-deficient* if `σ(n) ≥ 2n`, with `σ` spelled out as
`∑ d ∈ Nat.divisors n, d`, and *primitive* non-deficient if in
addition every proper divisor is deficient. The paper's
factorization `n = p₁^{a₁} ⋯ p_k^{a_k}` with
`p₁ < ⋯ < p_k` is encoded through `n.primeFactors` (so
`k = n.primeFactors.card`), `n.factorization p` for the
exponents, the radical `R = ∏ q ∈ n.primeFactors, q`, and explicit
extremal elements for `p₁` (least) and `p_k` (greatest). The
paper's abundancy `h(n) = σ(n)/n` is `abundancyIndex`, and its
supremum bound `H(n) = ∏_{p ∣ n} p/(p-1)` is `abundancySup`,
both in `ℚ`.

The paper's Theorem (label `maintheoremboundwithkR`: some
`p_i^{a_i+1} < 2kR`) is already proved in MathlibExt as
`MetaMathlibExt.primitive_nondeficient_prime_power_bound` and is
not restated. The statement
`max_primeFactor_lt_sqrt_radical_or_exists_pow_lt` is proved in
`MathlibExt.NumberTheory.PrimitiveNondeficient`. Grün's bound is
proved in `MathlibExt.NumberTheory.PrimitiveNondeficientGrun`. This module
states the remaining wanted lemmas.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndexDiv
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficientRadical
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficientTwoPowMulPrime
public import MathlibExt.NumberTheory.OddTwoPrimeFactorsDeficient
public import MathlibExt.NumberTheory.PrimitiveNondeficient
public import MathlibExt.NumberTheory.PrimitiveNondeficientGrun
public import MathlibExt.NumberTheory.PrimitiveNondeficientPuchta

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PrimitiveNondeficientWanted

/-- **Small component for odd primitive non-deficient numbers with three or four prime factors.**
Let $n$ be an odd primitive non-deficient number with exactly $3$ or exactly $4$ distinct prime
factors, and let $R$ be the product of the distinct prime factors of $n$. Then some prime factor
$p$ of $n$ satisfies $p^{a+1} < 2R$, where $a$ is the exponent of $p$ in $n$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma
(label `Checkforexactly3or4distinctprimefactors`). -/
theorem_wanted exists_pow_factorization_add_one_lt_two_mul_radical
    (n : ℕ) (hno : Odd n) (hn : IsPrimitiveNondeficient n)
    (hk : n.primeFactors.card = 3 ∨ n.primeFactors.card = 4) :
    ∃ p ∈ n.primeFactors,
      p ^ (n.factorization p + 1) < 2 * ∏ q ∈ n.primeFactors, q

end MathlibExt.NumberTheory.PrimitiveNondeficientWanted
