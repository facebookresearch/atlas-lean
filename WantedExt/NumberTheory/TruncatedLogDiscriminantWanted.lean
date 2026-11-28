/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.TruncatedLogDiscriminantPrimePower
public import MathlibExt.NumberTheory.TruncatedLogResultantPos
public import MathlibExt.NumberTheory.TruncatedLogResultantPrimePower
public import MathlibExt.NumberTheory.TruncatedLogDiscriminantFinitePrimesIsSquareDiscrTruncatedLog

/-!
# Discriminants of truncated logarithmic polynomials

Statements from Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39 (arXiv:2401.14138).
`F_n(x) = 1 + x + x²/2 + ⋯ + xⁿ/n`, `L_n = lcm(1, …, n)`, `F̃_n = L_n F_n ∈ ℤ[x]`,
and `𝒫_n = ∏ F̃_n(θ)` over the roots `θ` of `F_n' = 1 + x + ⋯ + x^{n-1}` (the
source's Equation (5)), here the resultant `Res(1 + x + ⋯ + x^{n-1}, F̃_n)`; by
`Polynomial.resultant_eq_prod_eval` this is that product, since
`1 + x + ⋯ + x^{n-1}` is monic. The discriminant is Mathlib's
`Polynomial.discr`. "Not in `ℚ^{×2}`" is stated as `¬ IsSquare`; the two agree
because these discriminants are nonzero.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Resultant product at $n = 1$.** The resultant product satisfies $\mathcal{P}_1 = 1$; it is an
empty product.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Equation (5). -/
public theorem truncatedLogResultantProduct_one : truncatedLogResultantProduct 1 = 1 := by
  simp [truncatedLogResultantProduct]

/-- **Nonsquare discriminants of $F_n$ for positive $n \equiv 0, 2, 3 \pmod 4$.** Let
$F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the truncated logarithmic polynomial and let
$n \ge 1$ be a natural number with $n \equiv 0$, $2$ or $3 \pmod 4$. Then the discriminant of
$F_n$ is not a square in $\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Proposition 1
(`integers-2025-A39-prop-1`). -/
public theorem_wanted not_isSquare_discr_truncatedLog_of_mod_four {n : ℕ} (hn : 1 ≤ n)
    (h : n % 4 = 0 ∨ n % 4 = 2 ∨ n % 4 = 3) :
    ¬ IsSquare (truncatedLogPolynomial n).discr

/-- **Nonsquare discriminants of truncated logarithmic polynomials.** Let
$F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the truncated logarithmic polynomial and let
$n \ge 1$. If $n \equiv 0$, $2$ or $3 \pmod 4$, or if $n \equiv 1 \pmod 4$ and $n = p^e$ for a
prime $p$ and an odd $e$, then the discriminant of $F_n$ is not a square in $\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 1
(`integers-2025-A39-thm-1`). -/
public theorem_wanted not_isSquare_discr_truncatedLog {n : ℕ} (hn : 1 ≤ n)
    (h : n % 4 = 0 ∨ n % 4 = 2 ∨ n % 4 = 3 ∨
      (n % 4 = 1 ∧ ∃ p e : ℕ, p.Prime ∧ Odd e ∧ n = p ^ e)) :
    ¬ IsSquare (truncatedLogPolynomial n).discr

end

end MetaMathlibExt
