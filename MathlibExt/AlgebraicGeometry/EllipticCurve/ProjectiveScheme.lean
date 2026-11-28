/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HomogeneousIdealQuotient
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveWeierstrassPrime
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The projective Weierstrass curve as a scheme

Let `W` be a Weierstrass curve over a commutative ring `R`, with homogeneous Weierstrass polynomial
`F = Y² Z + a₁ X Y Z + a₃ Y Z² - X³ - a₂ X² Z - a₄ X Z² - a₆ Z³` in `R[X, Y, Z]`
(`WeierstrassCurve.Projective.polynomial`). Its homogeneous coordinate ring
`S_W = R[X, Y, Z] / (F)` is graded by total degree, since `F` is homogeneous, and the projective
Weierstrass curve is `Proj S_W`, the closed subscheme of the projective plane over `R` cut out by
`F`.

## Main definitions

* `WeierstrassCurve.HomogeneousCoordinateRing`: `S_W = R[X, Y, Z] / (F)`.
* `WeierstrassCurve.projectiveGrading`: its grading by total degree.
* `WeierstrassCurve.ProjectiveScheme`: the scheme `Proj S_W`.
* `WeierstrassCurve.projectiveSchemeToSpec`: its structure morphism to `Spec R`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The homogeneous coordinate ring of a Weierstrass curve.** For a Weierstrass curve `W` over
a commutative ring `R`, this is `S_W = R[X, Y, Z] / (F)` for the homogeneous Weierstrass polynomial
`F = Y² Z + a₁ X Y Z + a₃ Y Z² - X³ - a₂ X² Z - a₄ X Z² - a₆ Z³`
(`WeierstrassCurve.Projective.polynomial`), with `X, Y, Z` the variables `0, 1, 2`. -/
abbrev HomogeneousCoordinateRing : Type u :=
  MvPolynomial (Fin 3) R ⧸ Ideal.span {W.toProjective.polynomial}

/-- The ideal `(F)` is homogeneous for the grading by total degree. -/
theorem isHomogeneous_span_polynomial :
    (Ideal.span {W.toProjective.polynomial}).IsHomogeneous (homogeneousSubmodule (Fin 3) R) :=
  Ideal.homogeneous_span _ _ fun _ hx => by
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨3, (mem_homogeneousSubmodule _ _).mpr (Projective.isHomogeneous_polynomial _)⟩

/-- **The grading of the homogeneous coordinate ring.** The degree `n` part of
`S_W = R[X, Y, Z] / (F)` is the image of the homogeneous polynomials of degree `n`. -/
noncomputable abbrev projectiveGrading : ℕ → Submodule R W.HomogeneousCoordinateRing :=
  Ideal.quotientGrading (homogeneousSubmodule (Fin 3) R) (Ideal.span {W.toProjective.polynomial})

noncomputable instance : GradedAlgebra W.projectiveGrading :=
  W.isHomogeneous_span_polynomial.gradedAlgebra

/-- The class of a homogeneous polynomial of degree `n` has degree `n` in `S_W`. -/
theorem mk_mem_projectiveGrading {n : ℕ} {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous n) :
    Ideal.Quotient.mk _ p ∈ W.projectiveGrading n :=
  Ideal.mk_mem_quotientGrading (𝒜 := homogeneousSubmodule (Fin 3) R) hp

/-- The class of the variable `i` of `R[X, Y, Z]` in `S_W`; it has degree `1`. -/
noncomputable def projectiveCoordinate (i : Fin 3) : W.HomogeneousCoordinateRing :=
  Ideal.Quotient.mk _ (X i)

theorem projectiveCoordinate_mem (i : Fin 3) : W.projectiveCoordinate i ∈ W.projectiveGrading 1 :=
  W.mk_mem_projectiveGrading (isHomogeneous_X R i)

/-- **The projective Weierstrass curve.** For a Weierstrass curve `W` over a commutative ring `R`,
this is the scheme `Proj S_W` of the homogeneous coordinate ring `S_W = R[X, Y, Z] / (F)`, graded
by total degree: the closed subscheme of the projective plane over `R` cut out by the homogeneous
Weierstrass polynomial `F = Y² Z + a₁ X Y Z + a₃ Y Z² - X³ - a₂ X² Z - a₄ X Z² - a₆ Z³`. -/
noncomputable abbrev ProjectiveScheme : Scheme.{u} :=
  Proj W.projectiveGrading

/-- **The structure morphism of the projective Weierstrass curve.** The morphism
`Proj S_W → Spec R`, the composite of the structure morphism `Proj S_W → Spec (S_W)₀` with the
morphism induced by `R → (S_W)₀`. -/
noncomputable def projectiveSchemeToSpec : W.ProjectiveScheme ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero W.projectiveGrading ≫ Spec.map (CommRingCat.ofHom (algebraMap R _))

end WeierstrassCurve
