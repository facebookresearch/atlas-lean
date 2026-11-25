/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Term counts in squares of polynomials
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace MathlibExt.Analysis.SparsePolynomialSquareTermBoundWanted

/-- **Erdős–Rényi conjecture on squares of sparse polynomials.** There is a function
$f : \mathbb{N} \to \mathbb{N}$ such that for every integer $k \ge 1$, every complex polynomial $p$
with at least $f(k)$ nonzero coefficients has a square $p^2$ with at least $k$ nonzero
coefficients. -/
def conjecture : Prop :=
  ∃ f : ℕ → ℕ,
    ∀ k : ℕ, 0 < k →
      ∀ p : Polynomial ℂ,
        f k ≤ p.support.card → k ≤ (p ^ 2).support.card

/-- **Schinzel's theorem on squares of sparse polynomials.** The Erdős–Rényi conjecture holds:
there is a function $f : \mathbb{N} \to \mathbb{N}$ such that for every integer $k \ge 1$, every
complex polynomial $p$ with at least $f(k)$ nonzero coefficients has a square $p^2$ with at least
$k$ nonzero coefficients.

Schinzel (Acta Arith. 49 (1987) 55-70) proved that the number of terms of $g \in \mathbb{C}[x]$
is bounded in terms of the number of terms of $g^2$; Fuchs, Mantova and Zannier
(arXiv:1412.4548, Thm 1.1) give a uniform version.

Source: C.
Fuchs, V. Mantova and U. Zannier, On fewnomials, integral points and a toric version of
Bertini's theorem (2017), arXiv:1412.4548, https://arxiv.org/abs/1412.4548. Moved from
`OpenConjectures/Analysis/SparsePolynomialSquareTermBound`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.SparsePolynomialSquareTermBoundWanted
