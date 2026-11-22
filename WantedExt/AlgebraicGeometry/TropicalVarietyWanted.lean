/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Algebra.MonoidAlgebra.Defs

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

/-- **Laurent polynomials.** The ring `K[x₁^{±1}, …, x_n^{±1}]`, as the monoid algebra of `ℤⁿ`. -/
abbrev LaurentPoly (K : Type*) [Field K] (n : ℕ) : Type _ :=
  AddMonoidAlgebra K (Fin n → ℤ)

/-- **Value of one term of a tropical polynomial.** For a Laurent polynomial `f = ∑ c_u x^u`, the
tropical term `val(c_u) + u · w ∈ ℝ ∪ {∞}` at the point `w ∈ ℝⁿ` (Maclagan–Sturmfels, draft
2009, Section 3.1). -/
def tropTerm (v : AddValuation K (WithTop ℝ)) (f : LaurentPoly K n) (w : Fin n → ℝ)
    (u : Fin n → ℤ) : WithTop ℝ :=
  v (f.coeff u) + ((∑ i, (u i : ℝ) * w i : ℝ) : WithTop ℝ)

/-- **Tropical hypersurface.** The set of `w ∈ ℝⁿ` at which the minimum
`trop(f)(w) = min_{u : c_u ≠ 0} (val(c_u) + u · w)` is attained at least twice
(Maclagan–Sturmfels, draft 2009, Definition 3.1.1). -/
def tropicalHypersurface (v : AddValuation K (WithTop ℝ)) (f : LaurentPoly K n) :
    Set (Fin n → ℝ) :=
  {w | ∃ u ∈ f.coeff.support, ∃ u' ∈ f.coeff.support, u ≠ u' ∧
    tropTerm v f w u = tropTerm v f w u' ∧
    ∀ u'' ∈ f.coeff.support, tropTerm v f w u ≤ tropTerm v f w u''}

/-- **Evaluation of a Laurent polynomial on the torus.** `f(y) = ∑_u c_u ∏_i y_i^{u_i}` for
`y ∈ (K^*)ⁿ`. -/
def evalTorus (f : LaurentPoly K n) (y : Fin n → Kˣ) : K :=
  f.coeff.sum fun u c ↦ c * ((∏ i, y i ^ u i : Kˣ) : K)

/-- **Coordinatewise valuations of a hypersurface.** The set
`{(val(y_1), …, val(y_n)) : y ∈ (K^*)ⁿ, f(y) = 0} ⊆ ℝⁿ` (Maclagan–Sturmfels, draft 2009,
Theorem 3.1.3, set 3, before taking the closure). -/
def valuationsOfZeros (v : AddValuation K (WithTop ℝ)) (f : LaurentPoly K n) :
    Set (Fin n → ℝ) :=
  {w | ∃ y : Fin n → Kˣ, evalTorus f y = 0 ∧ ∀ i, v (y i : K) = (w i : WithTop ℝ)}

/-- **Kapranov's theorem** (Maclagan–Sturmfels, *Introduction to Tropical Geometry*, draft of
4 November 2009, Theorem 3.1.3, equality of sets 1 and 3). Let `K` be an algebraically closed
field with a nontrivial valuation `val : K → ℝ ∪ {∞}` and `f` a nonzero Laurent polynomial in
`n` variables. Then the tropical hypersurface of `f` equals the closure in `ℝⁿ` of the set of
coordinatewise valuations of the zeros of `f` in the torus `(K^*)ⁿ`. (The hypothesis `f ≠ 0`
is implicit in the source: for `f = 0` the left side is empty and the right side is `ℝⁿ`.) -/
theorem_wanted tropicalHypersurface_eq_closure_valuationsOfZeros [IsAlgClosed K]
    (v : AddValuation K (WithTop ℝ)) (_hv : ∃ x : K, x ≠ 0 ∧ v x ≠ 0)
    (f : LaurentPoly K n) (_hf : f ≠ 0) :
    tropicalHypersurface v f = closure (valuationsOfZeros v f)

/-- **Tropicalization of a subvariety of the torus.** For an ideal `I` of Laurent polynomials
with variety `X = V(I) ⊆ (K^*)ⁿ`, the intersection `trop(X) = ⋂_{f ∈ I} trop(V(f))` of the
tropical hypersurfaces of the polynomials in `I` (Maclagan–Sturmfels, draft 2009,
Definition 3.2.1, equation (3.1)). The zero polynomial is left out of the intersection: its
tropical hypersurface is empty under Definition 3.1.1, and excluding it makes the zero ideal
tropicalize to `ℝⁿ`, as Theorem 3.2.4 requires; the source says nothing about `f = 0`. -/
def tropicalVariety (v : AddValuation K (WithTop ℝ)) (I : Ideal (LaurentPoly K n)) :
    Set (Fin n → ℝ) :=
  ⋂ f ∈ I, ⋂ (_ : f ≠ 0), tropicalHypersurface v f

/-- **Coordinatewise valuations of a variety.** The set
`val(X) = {(val(y_1), …, val(y_n)) : y ∈ X}` for `X = V(I) ⊆ (K^*)ⁿ` (Maclagan–Sturmfels, draft
2009, Theorem 3.2.4, set 3, before taking the closure). -/
def valuationsOfVariety (v : AddValuation K (WithTop ℝ)) (I : Ideal (LaurentPoly K n)) :
    Set (Fin n → ℝ) :=
  {w | ∃ y : Fin n → Kˣ, (∀ f ∈ I, evalTorus f y = 0) ∧ ∀ i, v (y i : K) = (w i : WithTop ℝ)}

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
