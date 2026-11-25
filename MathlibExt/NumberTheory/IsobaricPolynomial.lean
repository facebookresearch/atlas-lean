/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Isobaric polynomials

Formalizes the required definition clause for isobaric polynomials:
a polynomial `P_{k,n}(t_1, …, t_k)` over `ℤ` whose monomials are indexed by
`α ⊢ n`, i.e. `∑ j, j * α_j = n`.
-/

@[expose] public section

noncomputable section

namespace MetaMathlibExt

open scoped BigOperators

/-- **Isobaric weight of an exponent vector.** For a natural number $k$ and an exponent vector
$\alpha = (\alpha_1, \dots, \alpha_k) \in \mathbb{N}^k$, the isobaric weight of $\alpha$ is
$\sum_{j=1}^k j \alpha_j$.

The source's condition on the monomials of an isobaric polynomial of degree $n$ is that this
weight equals $n$.

Source: statement `jis_975c9f8263707d64d52bd0a3`. -/
abbrev isobaricWeight {k : ℕ} (d : Fin k →₀ ℕ) : ℕ :=
  Finsupp.weight (fun j : Fin k ↦ j.val + 1) d

/-- **Isobaric polynomial.** Let $k$ and $n$ be natural numbers. A polynomial
$P \in \mathbb{Z}[t_1, \dots, t_k]$ is isobaric of degree $n$ if every monomial
$t_1^{\alpha_1} \cdots t_k^{\alpha_k}$ occurring in $P$ with nonzero coefficient satisfies
$\sum_{j=1}^k j \alpha_j = n$; that is, $P$ is weighted homogeneous of degree $n$ when the
variable $t_j$ has weight $j$. In particular, the zero polynomial is isobaric of every degree.

Source: statement `jis_975c9f8263707d64d52bd0a3`. -/
abbrev IsIsobaric {k : ℕ} (n : ℕ) (P : MvPolynomial (Fin k) ℤ) : Prop :=
  MvPolynomial.IsWeightedHomogeneous (fun j : Fin k ↦ j.val + 1) P n

end MetaMathlibExt

end
