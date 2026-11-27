/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.RingTheory.MultigradedHilbertSeries

/-!
# Multigraded Hilbert–Serre requests

Grade `k[x₀, …, xₙ₋₁]` positively by `ℕ^r`: every variable has a nonzero multidegree, so each
multidegree contains finitely many monomials and the quotient pieces are finite-dimensional
(`MathlibExt.RingTheory.MultigradedHilbertSeries.finite_quotientPiece`). By the
Hilbert–Serre theorem, for a homogeneous ideal `I` the Hilbert series of `k[x] ⧸ I` times
`∏ᵢ (1 - t ^ w i)` is a polynomial with integer coefficients. It is an identity of
multivariate formal power series over `ℤ`.

The one-variable weighted polynomial Hilbert-series proofs in TauCeti are covered source
results. This file asks for the vector-valued homogeneous quotient version.

References:
* Miller–Sturmfels, *Combinatorial Commutative Algebra*, Chapter 8,
  https://doi.org/10.1007/b138602.
* Covered source: TauCetiProject/TauCeti at
  62bbc0596dc3539d488232e4e924a338548ea0a9,
  `TauCeti/RingTheory/GradedAlgebra/HilbertSeries.lean`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MultigradedHilbertSerreWanted

open MvPolynomial MathlibExt.RingTheory.MultigradedHilbertSeries

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {k : Type*} [Field k] {n r : ℕ}

/-- **Multigraded Hilbert–Serre theorem.** Let $k$ be a field and grade $k[x_0, \dots, x_{n-1}]$ by
$\mathbb{N}^r$, giving $x_i$ the degree $w_i$, where every $w_i$ is nonzero. For every homogeneous
ideal $I$, the Hilbert series $\sum_a \dim_k (k[x]/I)_a\, t^a$ of $k[x]/I$ times
$\prod_i (1 - t^{w_i})$ is a polynomial in $t_1, \dots, t_r$ with integer coefficients. -/
theorem_wanted hilbertSerre (w : Fin n → (Fin r →₀ ℕ)) [Fact (∀ i, w i ≠ 0)]
    (I : HomogeneousIdeal (weightedHomogeneousSubmodule k w)) :
    ∃ p : MvPolynomial (Fin r) ℤ,
      hilbertSeries w I * denominator w = (p : MvPowerSeries (Fin r) ℤ)

end WantedExt.AlgebraicGeometry.MultigradedHilbertSerreWanted
