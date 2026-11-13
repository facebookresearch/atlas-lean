/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nodal hypersurfaces in ℙ⁴ with fewer than (d-1)² nodes are factorial (AIM, Cheltsov)

AIM workshop Numerical invariants of singularities and higher-dimensional algebraic varieties,
problem list, Problem 18 (Cheltsov): let `Xₙ ⊂ ℙ⁴` be a hypersurface of degree `n` with a finite
number of isolated ordinary double points. When is `Xₙ` factorial (`Cl(Xₙ) = ℤ`)? If `|Sing Xₙ| <
(n-1)²`, then is `Cl(Xₙ) = ℤ`? (A further question asks about generic projections `ℙ⁴ ⇢ ℙ²` of `Sing
Xₙ`.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.FactorialHypersurfacesAIMAlgebraicGeometryProblem318Wanted

/-!
Source: AIM workshop Numerical invariants of singularities and higher-dimensional algebraic
varieties, problem list, Problem 18 (Cheltsov),
https://aimath.org/WWN/singularvariety/problems_final.pdf. UnsolvedMath record UM-20000318
(`AIM-ALGEBRAIC_GEOMETRY-0318`), dataset ulamai/UnsolvedMath v1.8.0.

The second question is formalized. Factoriality (every Weil divisor Cartier, `Cl(X) = ℤ`) is stated
as: the homogeneous coordinate ring `ℂ[x₀, …, x₄] / (f)` is a unique factorization domain, an
equivalence recorded in Cheltsov's Remark 1.2; a UFD is a domain in which every nonzero element is
associated to a product of primes. Singular points are the points of `ℙ⁴` where all partial
derivatives of `f` vanish; an ordinary double point is one where the Hessian of `f` has rank `4`
(the point spans its kernel by Euler's formula); 'a finite number of isolated ordinary double
points' means finitely many singular points, all of them nodes. The degree is `d ≥ 3`, as in
Cheltsov's theorem. Not formalized: the open-ended first question and the projection question, whose
range of `k` and hypotheses on `Xₙ` are not stated.
-/

open MvPolynomial

/-- The singular locus of the hypersurface `{f = 0} ⊆ ℙ⁴(ℂ)`: the points at which all partial
derivatives of `f` vanish (for homogeneous `f` of positive degree these lie on the hypersurface by
Euler's formula, and the condition does not depend on the representative). -/
def singularLocus (f : MvPolynomial (Fin 5) ℂ) : Set (Projectivization ℂ (Fin 5 → ℂ)) :=
  {P | ∀ i, eval P.rep (pderiv i f) = 0}

/-- The Hessian matrix `(∂²f / ∂xᵢ ∂xⱼ)(a)` of `f` at `a ∈ ℂ⁵`. -/
noncomputable def hessianAt (f : MvPolynomial (Fin 5) ℂ) (a : Fin 5 → ℂ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => eval a (pderiv j (pderiv i f))

/-- The hypersurface `{f = 0} ⊆ ℙ⁴` has at most isolated ordinary double points: finitely many
singular points, at each of which the Hessian of `f` has rank `4` (the maximum, since the point
itself lies in the kernel by Euler's formula). -/
def HasOnlyFinitelyManyNodes (f : MvPolynomial (Fin 5) ℂ) : Prop :=
  (singularLocus f).Finite ∧ ∀ P ∈ singularLocus f, (hessianAt f P.rep).rank = 4

/-- Cheltsov's theorem in the form asked in the AIM list: a hypersurface `X = {f = 0} ⊆ ℙ⁴` of
degree `d ≥ 3` with at most isolated ordinary double points, fewer than `(d - 1)²` of them, is
factorial, i.e. (equivalently, by Cheltsov's Remark 1.2) its homogeneous coordinate ring
`ℂ[x₀, …, x₄] / (f)` is a unique factorization domain: a domain in which every nonzero element is
associated to a product of primes. -/
def factorialBelowBound : Prop :=
  ∀ (d : ℕ) (f : MvPolynomial (Fin 5) ℂ), 3 ≤ d → f.IsHomogeneous d → HasOnlyFinitelyManyNodes f →
    (singularLocus f).ncard < (d - 1) ^ 2 →
    IsDomain (MvPolynomial (Fin 5) ℂ ⧸ Ideal.span {f}) ∧
      ∀ a : MvPolynomial (Fin 5) ℂ ⧸ Ideal.span {f}, a ≠ 0 →
        ∃ m : Multiset (MvPolynomial (Fin 5) ℂ ⧸ Ideal.span {f}),
          (∀ p ∈ m, Prime p) ∧ Associated m.prod a

/--
Resolved true: Cheltsov proved that a hypersurface in `ℙ⁴` of degree `d ≥ 3` with at most isolated
ordinary double points, fewer than `(d - 1)²` of them, is factorial, which by his Remark 1.2 means
that `ℂ[x₀, …, x₄] / (f)` is a unique factorization domain; his Example 1.3 shows the bound is
sharp. Source: AIM workshop Numerical invariants of singularities and higher-dimensional algebraic
varieties, problem list, Problem 18 (Cheltsov),
https://aimath.org/WWN/singularvariety/problems_final.pdf; resolution: I. Cheltsov, Factorial
threefold hypersurfaces, J. Algebraic Geom. 19 (2010), 781-791, arXiv:0803.3301, Theorem 1.4: for X
⊂ ℙ⁴ of degree d ≥ 3 with at most isolated ordinary double points, |Sing(X)| < (d - 1)² implies X
factorial; Remark 1.2: X factorial ⟺ every Weil divisor is Cartier ⟺ ℂ[x, y, z, t, u]/⟨f⟩ is a
unique factorization domain ⟺ Sing(X) imposes independent linear conditions on forms of degree 2d -
5; Example 1.3: xg + yh = 0 with general g, h has (d - 1)² nodes and is not factorial,
https://arxiv.org/abs/0803.3301.
-/
public theorem_wanted factorialBelowBound_holds : factorialBelowBound

end MathlibExt.AlgebraicGeometry.FactorialHypersurfacesAIMAlgebraicGeometryProblem318Wanted
