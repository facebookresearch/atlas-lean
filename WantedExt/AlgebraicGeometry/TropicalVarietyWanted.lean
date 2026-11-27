/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.TropicalVariety

/-!
# Tropical varieties: Kapranov's theorem and the Fundamental Theorem

Let `K` be an algebraically closed field with a nontrivial valuation `val : K → ℝ ∪ {∞}`. A
Laurent polynomial `f = ∑_u c_u x^u ∈ K[x₁^{±1}, …, x_n^{±1}]` tropicalizes to the
piecewise-linear function `trop(f)(w) = min_u (val(c_u) + u · w)` on `ℝⁿ`, and its tropical
hypersurface is the locus where this minimum is attained at least twice. Kapranov's theorem says
that this purely combinatorial set is the closure of the set of coordinatewise valuations of the
zeros of `f` in the torus `(K^*)ⁿ`. The Fundamental Theorem of tropical algebraic geometry
extends this from hypersurfaces to the variety of any ideal `I` of Laurent polynomials, whose
tropicalization is the intersection of the tropical hypersurfaces of the polynomials in `I`.

Laurent polynomials in `n` variables are the monoid algebra `K[ℤⁿ]`, here
`AddMonoidAlgebra K (Fin n → ℤ)`, with coefficient function `f.coeff`.

Source: D. Maclagan, B. Sturmfels, *Introduction to Tropical Geometry*, draft of 4 November
2009, Definition 3.1.1, Theorem 3.1.3 (Kapranov), Definition 3.2.1 and Theorem 3.2.4 (the
Fundamental Theorem), under the standing assumption of Chapter 3 that `K` is algebraically
closed with a nontrivial valuation; published as AMS Graduate Studies in Mathematics 161 (2015),
Sections 3.1 and 3.2.
-/

@[expose] public section

noncomputable section

namespace MathlibExt.AlgebraicGeometry.TropicalVarietyWanted

variable {K : Type*} [Field K] {n : ℕ}

/-- **Fundamental Theorem of Tropical Algebraic Geometry** (Maclagan–Sturmfels, *Introduction to
Tropical Geometry*, draft of 4 November 2009, Theorem 3.2.4, equality of sets 1 and 3). Let `K`
be an algebraically closed field with a nontrivial valuation `val : K → ℝ ∪ {∞}`, `I` an ideal of
Laurent polynomials and `X = V(I) ⊆ (K^*)ⁿ`. Then the tropical variety
`trop(X) = ⋂_{f ∈ I} trop(V(f))` equals the closure in `ℝⁿ` of the set of coordinatewise
valuations of the points of `X`. -/
theorem_wanted tropicalVariety_eq_closure_valuationsOfVariety [IsAlgClosed K]
    (v : AddValuation K (WithTop ℝ)) (_hv : ∃ x : K, x ≠ 0 ∧ v x ≠ 0)
    (I : Ideal (LaurentPoly K n)) :
    tropicalVariety v I = closure (valuationsOfVariety v I)

end MathlibExt.AlgebraicGeometry.TropicalVarietyWanted
