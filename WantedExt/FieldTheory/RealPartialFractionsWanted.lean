/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.FieldTheory.RatFunc.Basic

@[expose] public section

open scoped Polynomial RatFunc

namespace MathlibExt.FieldTheory.RealPartialFractionsWanted

/--
**Partial fraction decomposition over $\mathbb{R}$.** For every real rational function
$f \in \mathbb{R}(X)$ there exist a polynomial $q \in \mathbb{R}[X]$, a finite set $S$ of monic
polynomials in $\mathbb{R}[X]$, each of degree $1$ or irreducible of degree $2$, and, for each
$p \in S$, a natural number $m_p$ and polynomials $g_{p,k} \in \mathbb{R}[X]$ for $k < m_p$, each
of degree less than the degree of $p$, such that, in $\mathbb{R}(X)$,
$$f = q + \sum_{p \in S} \sum_{k=0}^{m_p - 1} \frac{g_{p,k}}{p^{k+1}}.$$

Only existence is stated: the standard uniqueness of the decomposition (support and
multiplicities fixed by the denominator's irreducible factors) is not, so a witness may include
polynomials $p \in S$ with $m_p = 0$ or zero numerators $g_{p,k}$.

Sources: Field theory / `ℝ(X)`-partial fraction decomposition in `docs/undergrad.yaml`;
S. Lang, Algebra, rev. 3rd ed., Springer, 2002, Ch. IV, §5 (Partial fractions), p. 187;
https://en.wikipedia.org/wiki/Partial_fraction_decomposition#General_result
-/
public theorem_wanted ratFunc_partial_fractions_real (f : ℝ⟮X⟯) :
    ∃ (q : ℝ[X]) (s : Finset ℝ[X]) (g : ℝ[X] → ℕ → ℝ[X]) (m : ℝ[X] → ℕ),
      (∀ p ∈ s, p.Monic ∧ (p.natDegree = 1 ∨ (p.natDegree = 2 ∧ Irreducible p)))
        ∧ (∀ p ∈ s, ∀ k < m p, (g p k).natDegree < p.natDegree)
        ∧ f = algebraMap ℝ[X] ℝ⟮X⟯ q
            + ∑ p ∈ s, ∑ k ∈ Finset.range (m p),
                algebraMap ℝ[X] ℝ⟮X⟯ (g p k) / algebraMap ℝ[X] ℝ⟮X⟯ p ^ (k + 1)

end MathlibExt.FieldTheory.RealPartialFractionsWanted
