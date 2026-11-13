/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.RatFunc.Basic

@[expose] public section

open scoped Polynomial RatFunc

namespace MathlibExt.FieldTheory.ComplexPartialFractionsWanted

/--
**Partial fraction decomposition over $\mathbb{C}$.** For every complex rational function
$f \in \mathbb{C}(X)$ there exist a polynomial $q \in \mathbb{C}[X]$, a finite set $S$ of monic
polynomials of degree $1$ in $\mathbb{C}[X]$, and, for each $p \in S$, a natural number $m_p$
and polynomials $g_{p,k} \in \mathbb{C}[X]$ for $k < m_p$, each of degree less than the degree
of $p$, such that, in $\mathbb{C}(X)$,
$$f = q + \sum_{p \in S} \sum_{k=0}^{m_p - 1} \frac{g_{p,k}}{p^{k+1}}.$$

Only existence is stated: the standard uniqueness of the decomposition (support and
multiplicities fixed by the denominator's irreducible factors) is not, so a witness may include
polynomials $p \in S$ with $m_p = 0$ or zero numerators $g_{p,k}$.

Sources: Field theory / `ℂ(X)`-partial fraction decomposition in `docs/undergrad.yaml`;
S. Lang, Algebra, rev. 3rd ed., Springer, 2002, Ch. IV, §5 (Partial fractions), p. 187;
https://en.wikipedia.org/wiki/Partial_fraction_decomposition#Statement
-/
public theorem_wanted ratFunc_partial_fractions_complex (f : ℂ⟮X⟯) :
    ∃ (q : ℂ[X]) (s : Finset ℂ[X]) (g : ℂ[X] → ℕ → ℂ[X]) (m : ℂ[X] → ℕ),
      (∀ p ∈ s, p.Monic ∧ p.natDegree = 1)
        ∧ (∀ p ∈ s, ∀ k < m p, (g p k).natDegree < p.natDegree)
        ∧ f = algebraMap ℂ[X] ℂ⟮X⟯ q
            + ∑ p ∈ s, ∑ k ∈ Finset.range (m p),
                algebraMap ℂ[X] ℂ⟮X⟯ (g p k) / algebraMap ℂ[X] ℂ⟮X⟯ p ^ (k + 1)

end MathlibExt.FieldTheory.ComplexPartialFractionsWanted
