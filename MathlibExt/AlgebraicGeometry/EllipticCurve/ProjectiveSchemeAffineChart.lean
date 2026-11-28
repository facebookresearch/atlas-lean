/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveScheme
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ChartAtInfinity

/-!
# The affine chart `Z ≠ 0` of the projective Weierstrass curve

Let `W` be a Weierstrass curve over a commutative ring `R`, with homogeneous coordinate ring
`S_W = R[X, Y, Z] / (F)` and projective curve `Proj S_W` (`WeierstrassCurve.ProjectiveScheme`).
The degree `0` part `S_(Z)` of `S_W[1 / Z]` is the affine coordinate ring
`A_W = R[x, y] / (y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆)` (Mathlib's
`WeierstrassCurve.Affine.CoordinateRing`), through `X / Z ↦ x`, `Y / Z ↦ y`
(`WeierstrassCurve.awayZRingEquiv`). So the basic open `D₊(Z)` of `Proj S_W` is `Spec A_W`
(`WeierstrassCurve.affineChart`), compatibly with the structure morphisms to `Spec R`.

## Main results

* `WeierstrassCurve.awayZRingEquiv`: `S_(Z) ≃+* A_W`, sending `X / Z` to `x` and `Y / Z` to `y`.
* `WeierstrassCurve.affineChart`: the open immersion `Spec A_W ⟶ Proj S_W` with image `D₊(Z)`.
* `WeierstrassCurve.affineChart_projectiveSchemeToSpec`: it lies over `Spec R`.

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34: a projective plane curve is the
  union of its affine pieces `C₀ ∪ C₁ ∪ C₂` "in the usual way".
* B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015),
  <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, (2.1), p. 2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem projectiveCoordinate_two_mem : W.projectiveCoordinate 2 ∈ W.projectiveGrading 1 :=
  W.projectiveCoordinate_mem 2

/-- The degree `0` part `S_(Z)` of `S_W[1 / Z]`. -/
abbrev AwayZ : Type u := Away W.projectiveGrading (W.projectiveCoordinate 2)

/-- Dehomogenization at `Z`: the ring map `S_W → A_W` sending `X, Y, Z` to `x, y, 1`. -/
noncomputable def dehomogenizeZ : W.HomogeneousCoordinateRing →+* W.toAffine.CoordinateRing :=
  Ideal.Quotient.lift _ (aeval ![W.affineX, W.affineY, 1]).toRingHom (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
    convert mul_zero _
    rw [Projective.polynomial]
    have h0 : (![W.affineX, W.affineY, 1] : Fin 3 → W.toAffine.CoordinateRing) 0 = W.affineX := rfl
    have h1 : (![W.affineX, W.affineY, 1] : Fin 3 → W.toAffine.CoordinateRing) 1 = W.affineY := rfl
    have h2 : (![W.affineX, W.affineY, 1] : Fin 3 → W.toAffine.CoordinateRing) 2 = 1 := rfl
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, h0, h1, h2, toProjective]
    linear_combination W.relation_affine)

theorem dehomogenizeZ_mk (p : MvPolynomial (Fin 3) R) :
    W.dehomogenizeZ (Ideal.Quotient.mk _ p) = aeval ![W.affineX, W.affineY, 1] p :=
  rfl

theorem dehomogenizeZ_coordinate_zero : W.dehomogenizeZ (W.projectiveCoordinate 0) = W.affineX := by
  simp [projectiveCoordinate, dehomogenizeZ_mk]

theorem dehomogenizeZ_coordinate_one : W.dehomogenizeZ (W.projectiveCoordinate 1) = W.affineY := by
  simp [projectiveCoordinate, dehomogenizeZ_mk]

theorem dehomogenizeZ_coordinate_two : W.dehomogenizeZ (W.projectiveCoordinate 2) = 1 := by
  simp [projectiveCoordinate, dehomogenizeZ_mk]

theorem dehomogenizeZ_algebraMap (r : R) :
    W.dehomogenizeZ (algebraMap R _ r) = algebraMap R _ r := by
  rw [show algebraMap R W.HomogeneousCoordinateRing r = Ideal.Quotient.mk _ (C r) from rfl,
    dehomogenizeZ_mk, MvPolynomial.aeval_C]

/-- Dehomogenization on the localization away from `Z`. -/
noncomputable def dehomogenizeZLoc :
    Localization.Away (W.projectiveCoordinate 2) →+* W.toAffine.CoordinateRing :=
  IsLocalization.Away.lift (W.projectiveCoordinate 2) (g := W.dehomogenizeZ)
    (by rw [dehomogenizeZ_coordinate_two]; exact isUnit_one)

/-- The forward map `S_(Z) → A_W`. -/
noncomputable def awayZToAffine : W.AwayZ →+* W.toAffine.CoordinateRing :=
  W.dehomogenizeZLoc.comp (algebraMap W.AwayZ (Localization.Away (W.projectiveCoordinate 2)))

theorem awayZToAffine_mk (n : ℕ) (a : W.HomogeneousCoordinateRing)
    (ha : a ∈ W.projectiveGrading (n • 1)) :
    W.awayZToAffine (Away.mk _ W.projectiveCoordinate_two_mem n a ha) = W.dehomogenizeZ a := by
  rw [awayZToAffine, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    dehomogenizeZLoc, Localization.mk_eq_mk', IsLocalization.Away.lift, IsLocalization.lift_mk']
  convert mul_one (W.dehomogenizeZ a)
  rw [← Units.val_one, Units.val_inj, inv_eq_one, Units.ext_iff]
  simp [IsUnit.coe_liftRight, dehomogenizeZ_coordinate_two]

/-- The image of `F` in `S_W` vanishes, written in the coordinates. -/
theorem coordinate_relation :
    W.projectiveCoordinate 1 ^ 2 * W.projectiveCoordinate 2 +
        algebraMap R _ W.a₁ * W.projectiveCoordinate 0 * W.projectiveCoordinate 1 *
          W.projectiveCoordinate 2 +
        algebraMap R _ W.a₃ * W.projectiveCoordinate 1 * W.projectiveCoordinate 2 ^ 2 -
      (W.projectiveCoordinate 0 ^ 3 +
        algebraMap R _ W.a₂ * W.projectiveCoordinate 0 ^ 2 * W.projectiveCoordinate 2 +
        algebraMap R _ W.a₄ * W.projectiveCoordinate 0 * W.projectiveCoordinate 2 ^ 2 +
        algebraMap R _ W.a₆ * W.projectiveCoordinate 2 ^ 3) = 0 := by
  have h : Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial})
      W.toProjective.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  rw [← h]
  rfl

/-- Dehomogenized coordinates satisfy the affine Weierstrass equation: if `ρ (Z) u = 1`, then
`(ρ (X) u, ρ (Y) u)` satisfies `y² + a₁ x y + a₃ y = x³ + a₂ x² + a₄ x + a₆`. -/
theorem affine_relation_of_mul_eq_one {T : Type*} [CommRing T]
    (ρ : W.HomogeneousCoordinateRing →+* T) {u : T} (hu : ρ (W.projectiveCoordinate 2) * u = 1) :
    (ρ (W.projectiveCoordinate 1) * u) ^ 2 +
        ρ (algebraMap R _ W.a₁) * (ρ (W.projectiveCoordinate 0) * u) *
          (ρ (W.projectiveCoordinate 1) * u) +
        ρ (algebraMap R _ W.a₃) * (ρ (W.projectiveCoordinate 1) * u) -
      ((ρ (W.projectiveCoordinate 0) * u) ^ 3 +
        ρ (algebraMap R _ W.a₂) * (ρ (W.projectiveCoordinate 0) * u) ^ 2 +
        ρ (algebraMap R _ W.a₄) * (ρ (W.projectiveCoordinate 0) * u) +
        ρ (algebraMap R _ W.a₆)) = 0 := by
  have hF := congrArg ρ W.coordinate_relation
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at hF
  set X := ρ (W.projectiveCoordinate 0)
  set Y := ρ (W.projectiveCoordinate 1)
  set Z := ρ (W.projectiveCoordinate 2)
  linear_combination u ^ 3 * hF + (-(Y ^ 2 * u ^ 2) - ρ (algebraMap R _ W.a₁) * X * Y * u ^ 2 -
    ρ (algebraMap R _ W.a₃) * Y * u * (Z * u + 1) + ρ (algebraMap R _ W.a₂) * X ^ 2 * u ^ 2 +
    ρ (algebraMap R _ W.a₄) * X * u * (Z * u + 1) +
    ρ (algebraMap R _ W.a₆) * ((Z * u) ^ 2 + Z * u + 1)) * hu

/-- The localization `S_W[1/Z]`. -/
abbrev LocZ : Type u := Localization.Away (W.projectiveCoordinate 2)

/-- `1 / Z` in `S_W[1/Z]`. -/
noncomputable def invZ : W.LocZ :=
  IsLocalization.mk' W.LocZ (1 : W.HomogeneousCoordinateRing)
    (⟨W.projectiveCoordinate 2, Submonoid.mem_powers _⟩ : Submonoid.powers _)

theorem algebraMap_coordinate_two_mul_invZ :
    algebraMap _ W.LocZ (W.projectiveCoordinate 2) * W.invZ = 1 := by
  rw [invZ, mul_comm, IsLocalization.mk'_spec, map_one]

theorem mem_projectiveGrading_one_nsmul (i : Fin 3) :
    W.projectiveCoordinate i ∈ W.projectiveGrading (1 • 1) := by
  simpa using W.projectiveCoordinate_mem i

/-- The constants `R → S_(Z)`. -/
noncomputable def constZ : R →+* W.AwayZ :=
  (fromZeroRingHom W.projectiveGrading _).comp (algebraMap R (W.projectiveGrading 0))

theorem val_constZ (r : R) :
    (W.constZ r).val = algebraMap _ W.LocZ (algebraMap R W.HomogeneousCoordinateRing r) := by
  simp [constZ, fromZeroRingHom]
  rfl

/-- `X / Z` in `S_(Z)`. -/
noncomputable def xZ : W.AwayZ :=
  Away.mk _ W.projectiveCoordinate_two_mem 1 (W.projectiveCoordinate 0)
    (W.mem_projectiveGrading_one_nsmul 0)

/-- `Y / Z` in `S_(Z)`. -/
noncomputable def yZ : W.AwayZ :=
  Away.mk _ W.projectiveCoordinate_two_mem 1 (W.projectiveCoordinate 1)
    (W.mem_projectiveGrading_one_nsmul 1)

theorem val_xZ : W.xZ.val = algebraMap _ W.LocZ (W.projectiveCoordinate 0) * W.invZ := by
  rw [xZ, Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one, invZ]
  congr
  simp

theorem val_yZ : W.yZ.val = algebraMap _ W.LocZ (W.projectiveCoordinate 1) * W.invZ := by
  rw [yZ, Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one, invZ]
  congr
  simp

theorem eval₂_yZ_polynomial :
    Polynomial.eval₂ (Polynomial.eval₂RingHom W.constZ W.xZ) W.yZ W.toAffine.polynomial = 0 := by
  apply val_injective
  rw [val_zero]
  have key := W.affine_relation_of_mul_eq_one (algebraMap _ W.LocZ)
    W.algebraMap_coordinate_two_mul_invZ
  rw [← key]
  simp only [Affine.polynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_pow, val_add, val_sub, val_mul, val_pow, val_constZ, val_xZ, val_yZ]
  ring

/-- The backward map `A_W → S_(Z)`: `x ↦ X / Z`, `y ↦ Y / Z`. -/
noncomputable def affineToAwayZ : W.toAffine.CoordinateRing →+* W.AwayZ :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom W.constZ W.xZ) W.yZ W.eval₂_yZ_polynomial

theorem affineToAwayZ_affineX : W.affineToAwayZ W.affineX = W.xZ := by
  simp [affineToAwayZ, affineX]

theorem affineToAwayZ_affineY : W.affineToAwayZ W.affineY = W.yZ := by
  simp [affineToAwayZ, affineY]

theorem affineToAwayZ_algebraMap (r : R) :
    W.affineToAwayZ (algebraMap R _ r) = W.constZ r := by
  rw [show algebraMap R W.toAffine.CoordinateRing r =
    AdjoinRoot.of W.toAffine.polynomial (Polynomial.C r) from rfl]
  simp [affineToAwayZ]

theorem awayZToAffine_constZ (r : R) : W.awayZToAffine (W.constZ r) = algebraMap R _ r := by
  rw [awayZToAffine, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, val_constZ,
    dehomogenizeZLoc, IsLocalization.Away.lift, IsLocalization.lift_eq, dehomogenizeZ_algebraMap]

theorem awayZToAffine_xZ : W.awayZToAffine W.xZ = W.affineX := by
  rw [xZ, awayZToAffine_mk, dehomogenizeZ_coordinate_zero]

theorem awayZToAffine_yZ : W.awayZToAffine W.yZ = W.affineY := by
  rw [yZ, awayZToAffine_mk, dehomogenizeZ_coordinate_one]

theorem awayZToAffine_comp_affineToAwayZ :
    W.awayZToAffine.comp W.affineToAwayZ = RingHom.id _ := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · have := W.affineToAwayZ_algebraMap r
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [show AdjoinRoot.of W.toAffine.polynomial (Polynomial.C r) =
        algebraMap R W.toAffine.CoordinateRing r from rfl, this, awayZToAffine_constZ]
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [show AdjoinRoot.of W.toAffine.polynomial Polynomial.X = W.affineX from rfl,
        affineToAwayZ_affineX, awayZToAffine_xZ]
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [show AdjoinRoot.root W.toAffine.polynomial = W.affineY from rfl,
      affineToAwayZ_affineY, awayZToAffine_yZ]

theorem aeval_coordinates (p : MvPolynomial (Fin 3) R) :
    aeval W.projectiveCoordinate p = Ideal.Quotient.mk _ p := by
  have h := MvPolynomial.comp_aeval_apply (X : Fin 3 → MvPolynomial (Fin 3) R)
    (Ideal.Quotient.mkₐ R (Ideal.span {W.toProjective.polynomial})) p
  rw [show W.projectiveCoordinate = fun i => Ideal.Quotient.mk _ (X i) from rfl]
  simpa [aeval_X_left] using h.symm

theorem val_affineToAwayZ_dehomogenizeZ {n : ℕ} {p : MvPolynomial (Fin 3) R}
    (hp : p.IsHomogeneous n) :
    (W.affineToAwayZ (W.dehomogenizeZ
        (Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial}) p))).val =
      W.invZ ^ n *
        algebraMap _ W.LocZ (Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial}) p) := by
  rw [dehomogenizeZ_mk, ← HomogeneousLocalization.algebraMap_apply, aeval_def, eval₂_comp_left,
    eval₂_comp_left]
  have hf : ((algebraMap W.AwayZ W.LocZ).comp (W.affineToAwayZ.comp
      (algebraMap R W.toAffine.CoordinateRing))) = algebraMap R W.LocZ := by
    ext r
    simp only [RingHom.comp_apply, affineToAwayZ_algebraMap,
      HomogeneousLocalization.algebraMap_apply,
      val_constZ]
    rfl
  have hg : (⇑(algebraMap W.AwayZ W.LocZ) ∘ ⇑W.affineToAwayZ ∘ ![W.affineX, W.affineY, 1]) =
      W.invZ • fun i => algebraMap _ W.LocZ (W.projectiveCoordinate i) := by
    funext i
    fin_cases i
    · simp [affineToAwayZ_affineX, val_xZ, mul_comm]
    · simp [affineToAwayZ_affineY, val_yZ, mul_comm]
    · change (algebraMap W.AwayZ W.LocZ) (W.affineToAwayZ 1) =
        W.invZ * (algebraMap W.HomogeneousCoordinateRing W.LocZ) (W.projectiveCoordinate 2)
      rw [mul_comm, W.algebraMap_coordinate_two_mul_invZ, map_one, map_one]
  rw [hf, hg, ← aeval_def, ← aeval_map_algebraMap W.LocZ, (hp.map _).aeval_smul,
    aeval_map_algebraMap, smul_eq_mul]
  congr 1
  rw [← W.aeval_coordinates p, ← IsScalarTower.toAlgHom_apply R W.HomogeneousCoordinateRing W.LocZ]
  exact (MvPolynomial.comp_aeval_apply W.projectiveCoordinate
    (IsScalarTower.toAlgHom R W.HomogeneousCoordinateRing W.LocZ) p).symm

theorem affineToAwayZ_comp_awayZToAffine :
    W.affineToAwayZ.comp W.awayZToAffine = RingHom.id _ := by
  ext x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ W.projectiveCoordinate_two_mem x
  obtain ⟨p, hp, hpa⟩ := id ha
  have hp' : p.IsHomogeneous n := by simpa using (mem_homogeneousSubmodule _ _).mp hp
  have hpa' : a = Ideal.Quotient.mk _ p := hpa.symm
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [awayZToAffine_mk, Away.val_mk, hpa', val_affineToAwayZ_dehomogenizeZ W hp',
    Localization.mk_eq_mk',
    IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
  congr 1
  rw [invZ, ← IsLocalization.mk'_pow]
  congr 1
  · simp


/-- **The chart `Z ≠ 0` of the homogeneous coordinate ring.** Let `W` be a Weierstrass curve over
a commutative ring `R`, with `S_W = R[X, Y, Z] / (F)`. The degree `0` part `S_(Z)` of
`S_W[1 / Z]` is isomorphic to the affine coordinate ring
`A_W = R[x, y] / (y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆)`: the class of `p / Z^n`, for `p`
homogeneous of degree `n`, goes to `p(x, y, 1)`, and the inverse sends `x` to `X / Z` and `y` to
`Y / Z`.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34 (the affine pieces of a projective
plane curve). -/
noncomputable def awayZRingEquiv : W.AwayZ ≃+* W.toAffine.CoordinateRing :=
  RingEquiv.ofRingHom W.awayZToAffine W.affineToAwayZ W.awayZToAffine_comp_affineToAwayZ
    W.affineToAwayZ_comp_awayZToAffine

theorem awayZRingEquiv_xZ : W.awayZRingEquiv W.xZ = W.affineX := W.awayZToAffine_xZ

theorem awayZRingEquiv_yZ : W.awayZRingEquiv W.yZ = W.affineY := W.awayZToAffine_yZ

theorem awayZRingEquiv_constZ (r : R) : W.awayZRingEquiv (W.constZ r) = algebraMap R _ r :=
  W.awayZToAffine_constZ r

/-- **The affine chart of the projective Weierstrass curve.** Let `W` be a Weierstrass curve over
a commutative ring `R`. This is the morphism `Spec A_W ⟶ Proj S_W` given by
`S_(Z) ≃ A_W` (`awayZRingEquiv`) followed by the inclusion of the basic open `D₊(Z)`
(`AlgebraicGeometry.Proj.awayι`); it is an open immersion with image `D₊(Z)`. -/
noncomputable def affineChart :
    Spec (CommRingCat.of W.toAffine.CoordinateRing) ⟶ W.ProjectiveScheme :=
  Spec.map (CommRingCat.ofHom W.awayZToAffine) ≫
    Proj.awayι W.projectiveGrading (W.projectiveCoordinate 2) W.projectiveCoordinate_two_mem
      one_pos

instance : IsIso (Spec.map (CommRingCat.ofHom W.awayZToAffine)) := by
  have : IsIso (CommRingCat.ofHom W.awayZToAffine) :=
    inferInstanceAs (IsIso W.awayZRingEquiv.toCommRingCatIso.hom)
  infer_instance

instance : IsOpenImmersion W.affineChart :=
  inferInstanceAs
    (IsOpenImmersion (Spec.map (CommRingCat.ofHom W.awayZToAffine) ≫ Proj.awayι _ _ _ _))

/-- The image of the affine chart is the basic open `D₊(Z)` of `Proj S_W`. -/
theorem opensRange_affineChart :
    W.affineChart.opensRange = Proj.basicOpen W.projectiveGrading (W.projectiveCoordinate 2) := by
  simp only [affineChart]
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

/-- The affine chart lies over `Spec R`: composed with the structure morphism of `Proj S_W` it
is the morphism `Spec A_W ⟶ Spec R` induced by `R → A_W`. -/
theorem affineChart_projectiveSchemeToSpec :
    W.affineChart ≫ W.projectiveSchemeToSpec =
      Spec.map (CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing)) := by
  simp only [affineChart, projectiveSchemeToSpec]
  rw [Category.assoc, ← Category.assoc (Proj.awayι _ _ _ _),
    Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact W.awayZToAffine_constZ r

end WeierstrassCurve
