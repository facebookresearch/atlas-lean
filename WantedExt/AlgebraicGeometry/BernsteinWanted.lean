/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Bernstein's theorem for two sparse equations in two unknowns

The Newton polygon of a bivariate Laurent polynomial is the convex hull of its exponent
vectors. Bernstein's theorem replaces the Bézout number `deg g · deg h` by a sharper polyhedral
count: two generic Laurent polynomials `g, h` have exactly `M(New(g), New(h))` common zeros in
the torus `(ℂ^*)²`, where `M(P, Q) = area(P + Q) - area(P) - area(Q)` is the mixed area of the
Newton polygons. Bézout's count for dense polynomials of degrees `d, e` is the special case of
triangles, `M = de`.

Source: B. Sturmfels, *Solving Systems of Polynomial Equations*, CBMS Regional Conference
Series in Mathematics 97, AMS, 2002, Section 3.1, Theorem 3.2 (Bernstein's Theorem) and the
remark after it extending it to Laurent polynomials; D. N. Bernstein, *The number of roots of a
system of equations*, Funct. Anal. Appl. 9 (1975).
-/

@[expose] public section

noncomputable section

namespace MathlibExt.AlgebraicGeometry.BernsteinWanted

open scoped Pointwise

/-- **Newton polygon of a support.** The convex hull in `ℝ²` of a finite set `A ⊆ ℤ²` of
exponent vectors (Sturmfels, CBMS 97, Section 3.1, `New(f)`). This is the Laurent analogue of
`NewtonPolygon.newtonPolygon`, which takes a bivariate polynomial with exponents in `ℕ²`. -/
def newtonPolygon (A : Finset (Fin 2 → ℤ)) : Set (Fin 2 → ℝ) :=
  convexHull ℝ ((fun u : Fin 2 → ℤ ↦ fun i ↦ (u i : ℝ)) '' (A : Set (Fin 2 → ℤ)))

/-- **Mixed area.** `M(P, Q) = area(P + Q) - area(P) - area(Q)` for plane polygons, with `P + Q`
the Minkowski sum and area the Lebesgue measure of `ℝ²` (Sturmfels, CBMS 97, Section 3.1). -/
def mixedArea (P Q : Set (Fin 2 → ℝ)) : ℝ :=
  (MeasureTheory.volume (P + Q)).toReal - (MeasureTheory.volume P).toReal -
    (MeasureTheory.volume Q).toReal

/-- **Sparse bivariate Laurent polynomial.** The function `(x, y) ↦ ∑_{u ∈ A} a_u x^{u_0} y^{u_1}`
on the torus `(ℂ^*)²`, with support `A` and coefficients `a`. -/
def sparseEval (A : Finset (Fin 2 → ℤ)) (a : A → ℂ) (z : ℂˣ × ℂˣ) : ℂ :=
  ∑ u : A, a u * ((z.1 ^ (u : Fin 2 → ℤ) 0 * z.2 ^ (u : Fin 2 → ℤ) 1 : ℂˣ) : ℂ)

/-- **Bernstein's theorem in the plane** (Sturmfels, *Solving Systems of Polynomial Equations*,
CBMS 97, Theorem 3.2, for Laurent polynomials as remarked there). Fix nonempty finite supports
`A, B ⊆ ℤ²`. For generic coefficients — all coefficient vectors `(a, b)` off the zero set of
some nonzero polynomial `D` in the coefficients — the system `g = h = 0` with
`g = ∑_{u ∈ A} a_u x^u` and `h = ∑_{u ∈ B} b_u x^u` has finitely many solutions in `(ℂ^*)²`, and
their number is the mixed area `M(New(g), New(h))` of the two Newton polygons. -/
theorem_wanted card_zeros_eq_mixedArea (A B : Finset (Fin 2 → ℤ)) (_hA : A.Nonempty)
    (_hB : B.Nonempty) :
    ∃ D : MvPolynomial (A ⊕ B) ℂ, D ≠ 0 ∧ ∀ (a : A → ℂ) (b : B → ℂ),
      MvPolynomial.eval (Sum.elim a b) D ≠ 0 →
        {z : ℂˣ × ℂˣ | sparseEval A a z = 0 ∧ sparseEval B b z = 0}.Finite ∧
        ({z : ℂˣ × ℂˣ | sparseEval A a z = 0 ∧ sparseEval B b z = 0}.ncard : ℝ) =
          mixedArea (newtonPolygon A) (newtonPolygon B)

end MathlibExt.AlgebraicGeometry.BernsteinWanted
