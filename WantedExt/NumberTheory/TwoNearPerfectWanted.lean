/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-near perfect numbers of the forms `2^k p` and `2^k p^2`

Statements from Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua
Zelinsky, *On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61 (arXiv:2310.01305).
Labels follow the journal numbering; the arXiv version numbers Lemmas 1-10 as Lemmas 3-7,
10, 11, 14, 15, 17 and Propositions 1-5 as Propositions 8, 9, 12, 13, 16.

A number `n` is `2`-near perfect with omitted divisors `d₁ ≠ d₂` when `d₁, d₂ ∣ n` and
`σ(n) = 2n + d₁ + d₂`. It is strongly `2`-near perfect when it has a divisor `d` with
`σ(n) = 2n + d + n / d` (the paper's equivalent form of the definition); for `n = 2^k p`
with `p` odd, `d ≠ n / d` holds automatically. Exponents flattened in the extracted
statements (`2k+1`, `pk`) are read as powers, as in the paper.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.NearPerfectPowerTwoDivisibility
public import MathlibExt.NumberTheory.StrongTwoNearPerfectExponentBound
public import MathlibExt.NumberTheory.TwoNearPerfectEquationDivisibility
public import MathlibExt.NumberTheory.TwoNearPerfectEquationSeven
public import MathlibExt.NumberTheory.TwoNearPerfectEquationSix
public import MathlibExt.NumberTheory.TwoNearPerfectOddDivisor
public import MathlibExt.NumberTheory.TwoNearPerfectOmittedDivisors
public import MathlibExt.NumberTheory.TwoNearPerfectPowerOfTwoDivisors
public import MathlibExt.NumberTheory.TwoNearPerfect
public import MathlibExt.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSq
public import MathlibExt.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSqCaseThree
public import MathlibExt.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSqCaseFive

namespace MetaMathlibExt

@[expose] public section

/-- **$2$-near perfect numbers of the form $2^k p$.** Let $k \ge 1$, let $p$ be a prime and let
$n = 2^k p$. Suppose $d_1 \ne d_2$ are divisors of $n$ with $\sigma(n) = 2n + d_1 + d_2$, where
$\sigma$ is the sum-of-divisors function (that is, $n$ is $2$-near perfect with omitted divisors
$d_1, d_2$). Then, after possibly swapping $d_1$ and $d_2$, one of the following holds, where
all equations are between integers: (1) $p = 2^k - 1$, $d_1 = 1$ and $d_2 = p$; (2) for some
natural numbers $a, b$, $p = 2^{k+1} - 2^a - 2^b - 1$, $d_1 = 2^a$ and $d_2 = 2^b$; (3) for some
natural numbers $a, b$, $p(1 + 2^b) = 2^{k+1} - 2^a - 1$, $d_1 = 2^a$ and $d_2 = 2^b p$; (4) for
some natural numbers $a, b$, $p(1 + 2^a + 2^b) = 2^{k+1} - 1$, $d_1 = 2^a p$ and $d_2 = 2^b p$.

The paper states only this necessary direction; the four situations are not sufficient as
printed ($k = 3$, $a = b = 1$ gives the prime $p = 11$ in situation 2, but $d_1 = d_2 = 2$).

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Theorem 1
(`integers-2024-A61-thm-1`). -/
public theorem_wanted two_near_perfect_two_pow_mul_prime_cases {k p d₁ d₂ : ℕ} (hk : 0 < k)
    (hp : p.Prime) (hd₁ : d₁ ∣ 2 ^ k * p) (hd₂ : d₂ ∣ 2 ^ k * p) (hne : d₁ ≠ d₂)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p) = 2 * (2 ^ k * p) + d₁ + d₂) :
    ∃ e₁ e₂ : ℕ, ((e₁ = d₁ ∧ e₂ = d₂) ∨ (e₁ = d₂ ∧ e₂ = d₁)) ∧
      (((p : ℤ) = 2 ^ k - 1 ∧ e₁ = 1 ∧ e₂ = p) ∨
        (∃ a b : ℕ, (p : ℤ) = 2 ^ (k + 1) - 2 ^ a - 2 ^ b - 1 ∧ e₁ = 2 ^ a ∧ e₂ = 2 ^ b) ∨
        (∃ a b : ℕ, (p : ℤ) * (1 + 2 ^ b) = 2 ^ (k + 1) - 2 ^ a - 1 ∧
          e₁ = 2 ^ a ∧ e₂ = 2 ^ b * p) ∨
        (∃ a b : ℕ, (p : ℤ) * (1 + 2 ^ a + 2 ^ b) = 2 ^ (k + 1) - 1 ∧
          e₁ = 2 ^ a * p ∧ e₂ = 2 ^ b * p))

/-- **Classification of prime solutions of $p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1$.** Let $a \le k$
be natural numbers and let $p$ be a prime with $p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1$, that is,
$p = (2^{k+1} - 2^a - 1)/(1 + 2^{k-a})$. Then $k = a + 2$, $2^k p / 2^a = 4p$,
$5p = 2^{a+3} - 2^a - 1$, and $a \equiv 3 \pmod 4$.

The source states this for $n = 2^k p$ strongly $2$-near perfect, that is, with
$\sigma(n) = 2n + d + n/d$ for some divisor $d$ of $n$, where $\sigma$ is the sum of divisors.
That hypothesis follows from the equation for $p$ by taking $d = 2^a$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 5
(`integers-2024-A61-prop-5`). -/
public theorem_wanted strong_two_near_perfect_two_pow_mul_prime_classification {a k p : ℕ}
    (hp : p.Prime) (hak : a ≤ k)
    (hform : (p : ℤ) * (1 + 2 ^ (k - a)) = 2 ^ (k + 1) - 2 ^ a - 1) :
    k = a + 2 ∧ 2 ^ k * p / 2 ^ a = 4 * p ∧ (5 * p : ℤ) = 2 ^ (a + 3) - 2 ^ a - 1 ∧
      a % 4 = 3

end

end MetaMathlibExt
