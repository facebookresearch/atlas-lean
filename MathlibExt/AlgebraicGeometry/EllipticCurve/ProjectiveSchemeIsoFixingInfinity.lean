/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeZeroSection

/-!
# Isomorphisms of projective Weierstrass curves fixing the point at infinity

Let `W` and `W'` be Weierstrass curves over a field `F`, with projective curves `E` and `E'` and
points at infinity `O = [0 : 1 : 0]`, `O' = [0 : 1 : 0]`. An isomorphism `φ : E' ⟶ E` of schemes
over `F` with `φ (O') = O` maps the affine chart `E' ∖ {O'} = Spec A_{W'}` onto
`E ∖ {O} = Spec A_W`, so it is given there by an isomorphism of `F`-algebras
`A_W ≃ₐ[F] A_{W'}`, `f ↦ f ∘ φ` (`WeierstrassCurve.affineChartAlgEquiv`).

## Main results

* `WeierstrassCurve.affineChartAlgEquiv`: the `F`-algebra isomorphism `A_W ≃ₐ[F] A_{W'}`.
* `WeierstrassCurve.affineChart_comp_eq`: `φ` restricted to `Spec A_{W'}` is `Spec` of it.

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter II, proof of Theorem 2.1(b), p. 50.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace WeierstrassCurve

variable {F : Type u} [Field F] {W W' : WeierstrassCurve F}

/-- An isomorphism carrying `O'` to `O` carries the other points of `E'` to the other points of
`E`. -/
theorem base_mem_range_zeroSection_iff (φ : W'.ProjectiveScheme ⟶ W.ProjectiveScheme) [IsIso φ]
    (hO : W'.zeroSection ≫ φ = W.zeroSection) (x : W'.ProjectiveScheme) :
    φ.base x ∈ Set.range W.zeroSection.base ↔ x ∈ Set.range W'.zeroSection.base := by
  constructor
  · rintro ⟨pt, hpt⟩
    refine ⟨pt, φ.isOpenEmbedding.injective ?_⟩
    rw [← hpt, ← hO, Scheme.Hom.comp_base, TopCat.comp_app]
  · rintro ⟨pt, rfl⟩
    refine ⟨pt, ?_⟩
    rw [← hO, Scheme.Hom.comp_base, TopCat.comp_app]

/-- An isomorphism carrying `O'` to `O` maps the affine chart of `E'` into that of `E`. -/
theorem range_affineChart_comp_subset (φ : W'.ProjectiveScheme ⟶ W.ProjectiveScheme) [IsIso φ]
    (hO : W'.zeroSection ≫ φ = W.zeroSection) :
    Set.range (W'.affineChart ≫ φ).base ⊆ Set.range W.affineChart.base := by
  rintro _ ⟨a, rfl⟩
  have h₁ : W'.affineChart.base a ∉ Set.range W'.zeroSection.base := by
    rw [range_zeroSection_eq_compl_basicOpen, Set.notMem_compl_iff, SetLike.mem_coe,
      ← opensRange_affineChart]
    exact ⟨a, rfl⟩
  have h₂ : φ.base (W'.affineChart.base a) ∈
      (Proj.basicOpen W.projectiveGrading (W.projectiveCoordinate 2) : Set W.ProjectiveScheme) := by
    rw [← Set.notMem_compl_iff, ← range_zeroSection_eq_compl_basicOpen,
      base_mem_range_zeroSection_iff φ hO]
    exact h₁
  rw [← opensRange_affineChart] at h₂
  rw [Scheme.Hom.comp_base, TopCat.comp_app]
  exact h₂

variable (φ : W'.ProjectiveScheme ⟶ W.ProjectiveScheme) [IsIso φ]
  (hO : W'.zeroSection ≫ φ = W.zeroSection)

include hO in
/-- If `φ (O') = O`, then `φ⁻¹ (O) = O'`. -/
theorem zeroSection_comp_inv : W.zeroSection ≫ inv φ = W'.zeroSection := by
  rw [← hO, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The restriction `Spec A_{W'} ⟶ Spec A_W` of `φ` to the affine charts. -/
noncomputable def affineChartRestrict :
    Spec (CommRingCat.of W'.toAffine.CoordinateRing) ⟶
      Spec (CommRingCat.of W.toAffine.CoordinateRing) :=
  IsOpenImmersion.lift W.affineChart (W'.affineChart ≫ φ) (range_affineChart_comp_subset φ hO)

theorem affineChartRestrict_comp :
    affineChartRestrict φ hO ≫ W.affineChart = W'.affineChart ≫ φ :=
  IsOpenImmersion.lift_fac _ _ _

theorem affineChartRestrict_inv_comp_affineChartRestrict :
    affineChartRestrict (inv φ) (zeroSection_comp_inv φ hO) ≫ affineChartRestrict φ hO = 𝟙 _ := by
  rw [← cancel_mono W.affineChart, Category.assoc, affineChartRestrict_comp,
    ← Category.assoc, affineChartRestrict_comp, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id, Category.id_comp]

theorem affineChartRestrict_comp_affineChartRestrict_inv :
    affineChartRestrict φ hO ≫ affineChartRestrict (inv φ) (zeroSection_comp_inv φ hO) = 𝟙 _ := by
  rw [← cancel_mono W'.affineChart, Category.assoc, affineChartRestrict_comp,
    ← Category.assoc, affineChartRestrict_comp, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id, Category.id_comp]

/-- The ring isomorphism `A_W ≃+* A_{W'}` underlying the restriction of `φ`. -/
noncomputable def affineChartRingEquiv :
    W.toAffine.CoordinateRing ≃+* W'.toAffine.CoordinateRing :=
  RingEquiv.ofRingHom (Spec.preimage (affineChartRestrict φ hO)).hom
    (Spec.preimage (affineChartRestrict (inv φ) (zeroSection_comp_inv φ hO))).hom
    (by
      rw [← CommRingCat.hom_comp, ← Spec.preimage_comp,
        affineChartRestrict_comp_affineChartRestrict_inv, Spec.preimage_id, CommRingCat.hom_id])
    (by
      rw [← CommRingCat.hom_comp, ← Spec.preimage_comp,
        affineChartRestrict_inv_comp_affineChartRestrict, Spec.preimage_id, CommRingCat.hom_id])

theorem specMap_affineChartRingEquiv :
    Spec.map (CommRingCat.ofHom (affineChartRingEquiv φ hO : W.toAffine.CoordinateRing →+*
      W'.toAffine.CoordinateRing)) = affineChartRestrict φ hO :=
  Spec.map_preimage _

variable (hφ : φ ≫ W.projectiveSchemeToSpec = W'.projectiveSchemeToSpec)
include hφ

theorem affineChartRingEquiv_algebraMap (c : F) :
    affineChartRingEquiv φ hO (algebraMap F _ c) = algebraMap F _ c := by
  have h : Spec.map (CommRingCat.ofHom ((affineChartRingEquiv φ hO :
      W.toAffine.CoordinateRing →+* W'.toAffine.CoordinateRing).comp
        (algebraMap F W.toAffine.CoordinateRing))) =
      Spec.map (CommRingCat.ofHom (algebraMap F W'.toAffine.CoordinateRing)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_affineChartRingEquiv,
      ← affineChart_projectiveSchemeToSpec, ← Category.assoc, affineChartRestrict_comp,
      Category.assoc, hφ, affineChart_projectiveSchemeToSpec]
  have := congrArg (fun f => f.hom c) (Spec.map_injective h)
  exact this

/-- **Pulling back functions along an isomorphism that fixes the point at infinity.** Let `F` be
a field, let `W` and `W'` be Weierstrass curves over `F` with projective curves `E` and `E'` and
points at infinity `O = O' = [0 : 1 : 0]`, and let `φ : E' ⟶ E` be an isomorphism of schemes over
`Spec F` with `φ (O') = O`. Then `φ` restricts to an isomorphism `E' ∖ {O'} ⟶ E ∖ {O}` of the
affine charts, given by an isomorphism of `F`-algebras `A_W ≃ₐ[F] A_{W'}`, `f ↦ f ∘ φ`
(`affineChart_comp_eq`). The discriminants are not used.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, proof of Theorem 2.1(b), p. 50:
"`f ↦ f ∘ φ` is a homomorphism `k[x, y] → k[x', y']`". -/
noncomputable def affineChartAlgEquiv :
    W.toAffine.CoordinateRing ≃ₐ[F] W'.toAffine.CoordinateRing :=
  AlgEquiv.ofRingEquiv (f := affineChartRingEquiv φ hO) (affineChartRingEquiv_algebraMap φ hO hφ)

/-- The isomorphism `φ` restricted to the affine chart of `E'` is `Spec` of
`affineChartAlgEquiv φ hO hφ : A_W ≃ₐ[F] A_{W'}`, followed by the affine chart of `E`. -/
theorem affineChart_comp_eq :
    W'.affineChart ≫ φ =
      Spec.map (CommRingCat.ofHom (affineChartAlgEquiv φ hO hφ : W.toAffine.CoordinateRing →+*
        W'.toAffine.CoordinateRing)) ≫ W.affineChart := by
  rw [← affineChartRestrict_comp φ hO, ← specMap_affineChartRingEquiv φ hO]
  rfl

end WeierstrassCurve
