/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeVariableChange
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeIntegralCurve
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeIsoFixingInfinity

/-!
# Isomorphisms of projective Weierstrass curves that are variable changes on the affine chart

Let `W` be a Weierstrass curve over a field `F` and `C = (u, r, s, t)` a variable change. A morphism
`φ : (C • W).ProjectiveScheme ⟶ W.ProjectiveScheme` over `Spec F` whose restriction to the affine
chart is the affine variable change `x ↦ u² x' + r`, `y ↦ u³ y' + u² s x' + t` is the isomorphism
`(x : y : z) ↦ (u² x + r z : u³ y + s u² x + t z : z)`
(`WeierstrassCurve.eq_projectiveSchemeVariableChangeIso_hom`): the affine chart is dense, the
source is reduced and the target is separated over `F`. Combined with the restriction of an
isomorphism fixing the point at infinity to the affine charts
(`WeierstrassCurve.affineChartAlgEquiv`), an isomorphism `φ : E' ⟶ E` fixing `O` whose
restriction is the affine variable change of `C` with `W' = C • W` is that variable change
(`WeierstrassCurve.eq_projectiveSchemeVariableChangeIso_hom_of_affineChartAlgEquiv`).

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(b), p. 52, and the proof of
  Theorem 2.1(b), pp. 50–51.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace WeierstrassCurve

variable {F : Type u} [Field F]

instance (W : WeierstrassCurve F) : IsDominant W.affineChart :=
  ⟨W.dense_range_affineChart⟩

/-- **A morphism that is a variable change on the affine chart is that variable change.** Let `W`
be a Weierstrass curve over a field `F` and `C = (u, r, s, t)` a variable change, and let
`φ : (C • W).ProjectiveScheme ⟶ W.ProjectiveScheme` be a morphism over `Spec F` whose restriction
to the affine chart `Spec A_{C • W}` is `Spec` of the affine variable change
`x ↦ u² x' + r`, `y ↦ u³ y' + u² s x' + t` (`WeierstrassCurve.affineVariableChange`). Then `φ` is
the isomorphism `(x : y : z) ↦ (u² x + r z : u³ y + s u² x + t z : z)`
(`WeierstrassCurve.projectiveSchemeVariableChangeIso`). The discriminant is not used.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(b), p. 52 (the form of the
isomorphism), and the proof of Theorem 2.1(b), pp. 50–51 (two maps agreeing on the affine part). -/
theorem eq_projectiveSchemeVariableChangeIso_hom (W : WeierstrassCurve F) (C : VariableChange F)
    (φ : (C • W).ProjectiveScheme ⟶ W.ProjectiveScheme)
    (hφ : φ ≫ W.projectiveSchemeToSpec = (C • W).projectiveSchemeToSpec)
    (h : (C • W).affineChart ≫ φ =
      Spec.map (CommRingCat.ofHom (W.affineVariableChange C)) ≫ W.affineChart) :
    φ = (W.projectiveSchemeVariableChangeIso C).hom :=
  ext_of_isDominant_of_isSeparated W.projectiveSchemeToSpec
    (by rw [hφ, projectiveSchemeVariableChangeIso_hom_projectiveSchemeToSpec])
    (C • W).affineChart (by rw [h, affineChart_comp_projectiveSchemeVariableChangeIso_hom])

/-- **An isomorphism fixing `O` that is a variable change on the affine chart.** Let `W` be a
Weierstrass curve over a field `F`, `C` a variable change, and `φ : (C • W).ProjectiveScheme ⟶
W.ProjectiveScheme` an isomorphism over `Spec F` carrying `O` to `O`. If the `F`-algebra
isomorphism `A_W ≃ₐ[F] A_{C • W}`, `f ↦ f ∘ φ`, by which `φ` acts on the affine charts
(`WeierstrassCurve.affineChartAlgEquiv`) is the affine variable change of `C`, then `φ` is the
isomorphism `(x : y : z) ↦ (u² x + r z : u³ y + s u² x + t z : z)`.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(b), p. 52, and the proof of
Theorem 2.1(b), pp. 50–51. -/
theorem eq_projectiveSchemeVariableChangeIso_hom_of_affineChartAlgEquiv (W : WeierstrassCurve F)
    (C : VariableChange F) (φ : (C • W).ProjectiveScheme ⟶ W.ProjectiveScheme) [IsIso φ]
    (hO : (C • W).zeroSection ≫ φ = W.zeroSection)
    (hφ : φ ≫ W.projectiveSchemeToSpec = (C • W).projectiveSchemeToSpec)
    (he : ((affineChartAlgEquiv φ hO hφ : W.toAffine.CoordinateRing →+*
      (C • W).toAffine.CoordinateRing)) = W.affineVariableChange C) :
    φ = (W.projectiveSchemeVariableChangeIso C).hom :=
  W.eq_projectiveSchemeVariableChangeIso_hom C φ hφ (by rw [affineChart_comp_eq φ hO hφ, he])

end WeierstrassCurve
