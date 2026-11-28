/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveScheme
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ChartAtInfinity
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.Tactic.LinearCombination

/-!
# The chart at infinity of the projective Weierstrass scheme

Let `W` be a Weierstrass curve over a commutative ring `R`, with homogeneous coordinate ring
`S_W = R[X, Y, Z] / (F)` and projective scheme `Proj S_W`
(`WeierstrassCurve.ProjectiveScheme`). Its chart `Y ≠ 0` is the open subscheme `D₊(Y)`, and
dehomogenizing at `Y` identifies its ring of sections `(S_W[1 / Y])₀` with the coordinate ring
at infinity `B_W = R[z, w] / (h)`, `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`,
via `X / Y ↦ z` and `Z / Y ↦ w`. The point `O = (0 : 1 : 0)` is the point `z = w = 0` of this
chart, and gives a section of the structure morphism `Proj S_W → Spec R`.

## Main definitions and results

* `WeierstrassCurve.awayYRingEquiv`: the ring isomorphism `(S_W[1 / Y])₀ ≃ B_W`, with
  `X / Y ↦ z`, `Z / Y ↦ w`, compatible with the maps from `R`
  (`WeierstrassCurve.awayYRingEquiv_algebraMap`).
* `WeierstrassCurve.chartAtInfinity`: the open immersion `Spec B_W → Proj S_W` with image
  `D₊(Y)` (`WeierstrassCurve.opensRange_chartAtInfinity`), over `Spec R`
  (`WeierstrassCurve.chartAtInfinity_projectiveSchemeToSpec`).
* `WeierstrassCurve.zeroSection`: the section `Spec R → Proj S_W` given by the point
  `z = w = 0` of the chart at infinity, i.e. `O = (0 : 1 : 0)`
  (`WeierstrassCurve.zeroSection_projectiveSchemeToSpec`).

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34, and Example 4.20, p. 38.
* B. Conrad, *Minimal models for elliptic curves*, notes, 2015,
  <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, (2.1) and Definition 2.1, p. 2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Dehomogenization at `Y` -/

/-- **The relation `F(z, 1, w) = h(z, w)`.** Let `W` be a Weierstrass curve over a commutative
ring `R`, let `T` be a commutative `R`-algebra and `x, y, z, u ∈ T` with `y u = 1`. Then
`h(x u, z u) = u³ F(x, y, z)`, where `F` is the homogeneous Weierstrass polynomial and `h` the
polynomial at infinity. -/
theorem aeval_polynomialAtInfinity_mul {T : Type*} [CommRing T] [Algebra R T] (x y z u : T)
    (hu : y * u = 1) :
    MvPolynomial.aeval ![x * u, z * u] W.polynomialAtInfinity =
      u ^ 3 * MvPolynomial.aeval ![x, y, z] W.toProjective.polynomial := by
  rw [aeval_polynomialAtInfinity]
  simp only [Projective.polynomial, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (-(z * u * (y * u + 1)) - algebraMap R T W.a₁ * x * z * u ^ 2 -
    algebraMap R T W.a₃ * z ^ 2 * u ^ 2) * hu

/-- The dehomogenization `R[X, Y, Z] → B_W` at `Y`: `X ↦ z`, `Y ↦ 1`, `Z ↦ w`. -/
noncomputable def dehomogenizeY : MvPolynomial (Fin 3) R →ₐ[R] W.CoordinateRingAtInfinity :=
  MvPolynomial.aeval ![W.zAtInfinity, 1, W.wAtInfinity]

/-- Dehomogenization at `Y` kills `F`: `F(z, 1, w) = h(z, w) = 0` in `B_W`. -/
theorem dehomogenizeY_polynomial : W.dehomogenizeY W.toProjective.polynomial = 0 := by
  have h := W.aeval_polynomialAtInfinity_mul W.zAtInfinity 1 W.wAtInfinity 1 (mul_one 1)
  simp only [mul_one, one_pow, one_mul] at h
  rw [dehomogenizeY, ← h]
  have : MvPolynomial.aeval ![W.zAtInfinity, W.wAtInfinity] W.polynomialAtInfinity =
      Ideal.Quotient.mk _ W.polynomialAtInfinity := by
    have e : ![W.zAtInfinity, W.wAtInfinity] =
        (Ideal.Quotient.mkₐ R (Ideal.span {W.polynomialAtInfinity})) ∘ X := by
      funext i
      fin_cases i <;> rfl
    rw [← Ideal.Quotient.mkₐ_eq_mk R, MvPolynomial.aeval_unique (Ideal.Quotient.mkₐ R _), e]
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

/-- The dehomogenization `S_W → B_W` at `Y`: `X ↦ z`, `Y ↦ 1`, `Z ↦ w`. -/
noncomputable def homogeneousToAtInfinity :
    W.HomogeneousCoordinateRing →ₐ[R] W.CoordinateRingAtInfinity :=
  Ideal.Quotient.liftₐ _ W.dehomogenizeY (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, dehomogenizeY_polynomial, mul_zero])

/-- `S_W → B_W` sends the class of `p` to `p(z, 1, w)`. -/
theorem homogeneousToAtInfinity_mk (p : MvPolynomial (Fin 3) R) :
    W.homogeneousToAtInfinity (Ideal.Quotient.mk _ p) = W.dehomogenizeY p := rfl

/-- `S_W → B_W` sends `Y` to `1`. -/
theorem homogeneousToAtInfinity_projectiveCoordinate_one :
    W.homogeneousToAtInfinity (W.projectiveCoordinate 1) = 1 := by
  simp [projectiveCoordinate, homogeneousToAtInfinity_mk, dehomogenizeY]

/-! ### The ring of sections of the chart `Y ≠ 0` -/

/-- The coordinate `i` lies in degree `1 • 1`, as `Away.mk` asks for. -/
theorem projectiveCoordinate_mem_one_smul (i : Fin 3) :
    W.projectiveCoordinate i ∈ W.projectiveGrading (1 • 1) := by
  simpa using W.projectiveCoordinate_mem i

/-- The element `X / Y` of `(S_W[1 / Y])₀`. -/
noncomputable def xOverY : Away W.projectiveGrading (W.projectiveCoordinate 1) :=
  Away.mk W.projectiveGrading (W.projectiveCoordinate_mem 1) 1 (W.projectiveCoordinate 0)
    (W.projectiveCoordinate_mem_one_smul 0)

/-- The element `Z / Y` of `(S_W[1 / Y])₀`. -/
noncomputable def zOverY : Away W.projectiveGrading (W.projectiveCoordinate 1) :=
  Away.mk W.projectiveGrading (W.projectiveCoordinate_mem 1) 1 (W.projectiveCoordinate 2)
    (W.projectiveCoordinate_mem_one_smul 2)

/-- The map `R → (S_W)₀ → (S_W[1 / Y])₀`. -/
noncomputable def awayYAlgebraMap : R →+* Away W.projectiveGrading (W.projectiveCoordinate 1) :=
  (algebraMap (W.projectiveGrading 0) _).comp (algebraMap R (W.projectiveGrading 0))

/-- The dehomogenization `(S_W[1 / Y])₀ → B_W`, sending `a / Y ^ n` to the image of `a` under
`X ↦ z`, `Y ↦ 1`, `Z ↦ w`. -/
noncomputable def awayYDehomogenize :
    Away W.projectiveGrading (W.projectiveCoordinate 1) →+* W.CoordinateRingAtInfinity :=
  (Localization.awayLift W.homogeneousToAtInfinity.toRingHom (W.projectiveCoordinate 1)
    (by simp [W.homogeneousToAtInfinity_projectiveCoordinate_one])).comp
    (algebraMap _ (Localization.Away (W.projectiveCoordinate 1)))

/-- `(S_W[1 / Y])₀ → B_W` sends `a / Y ^ n` to the image of `a` under `S_W → B_W`. -/
theorem awayYDehomogenize_mk (n : ℕ) (a : W.HomogeneousCoordinateRing)
    (ha : a ∈ W.projectiveGrading (n • 1)) :
    W.awayYDehomogenize (Away.mk W.projectiveGrading (W.projectiveCoordinate_mem 1) n a ha) =
      W.homogeneousToAtInfinity a := by
  simp only [awayYDehomogenize, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  rw [Localization.awayLift_mk _ _ _ 1
    (by simp [W.homogeneousToAtInfinity_projectiveCoordinate_one])]
  simp

private abbrev LY : Type u := Localization.Away (W.projectiveCoordinate 1)

private noncomputable abbrev uY : W.LY := IsLocalization.Away.invSelf (W.projectiveCoordinate 1)

private lemma val_mk_eq (n : ℕ) (a : W.HomogeneousCoordinateRing) (h) :
    (Localization.mk a ⟨W.projectiveCoordinate 1 ^ n, h⟩ : W.LY) =
      algebraMap _ W.LY a * W.uY ^ n := by
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp only [map_pow]
  rw [mul_assoc, ← mul_pow, mul_comm W.uY, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

private lemma val_xOverY :
    W.xOverY.val = algebraMap _ W.LY (W.projectiveCoordinate 0) * W.uY := by
  rw [xOverY, Away.val_mk, val_mk_eq, pow_one]

private lemma val_zOverY :
    W.zOverY.val = algebraMap _ W.LY (W.projectiveCoordinate 2) * W.uY := by
  rw [zOverY, Away.val_mk, val_mk_eq, pow_one]

private lemma val_awayYAlgebraMap (r : R) :
    (W.awayYAlgebraMap r).val = algebraMap R W.LY r := by
  change (Localization.mk ((algebraMap R (W.projectiveGrading 0) r :
    W.HomogeneousCoordinateRing)) 1 : W.LY) = _
  rw [Localization.mk_one_eq_algebraMap, SetLike.GradeZero.coe_algebraMap,
    ← IsScalarTower.algebraMap_apply]

private lemma aeval_coords (p : MvPolynomial (Fin 3) R) :
    MvPolynomial.aeval ![algebraMap _ W.LY (W.projectiveCoordinate 0),
      algebraMap _ W.LY (W.projectiveCoordinate 1),
      algebraMap _ W.LY (W.projectiveCoordinate 2)] p =
      algebraMap _ W.LY (Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial}) p) := by
  have e : ![algebraMap _ W.LY (W.projectiveCoordinate 0),
      algebraMap _ W.LY (W.projectiveCoordinate 1), algebraMap _ W.LY (W.projectiveCoordinate 2)] =
      ((IsScalarTower.toAlgHom R W.HomogeneousCoordinateRing W.LY).comp
        (Ideal.Quotient.mkₐ R _)) ∘ X := by
    funext i
    fin_cases i <;> rfl
  rw [e, ← MvPolynomial.aeval_unique]
  rfl

/-- `h(X / Y, Z / Y) = 0` in `(S_W[1 / Y])₀`. -/
theorem eval₂Hom_polynomialAtInfinity :
    MvPolynomial.eval₂Hom W.awayYAlgebraMap ![W.xOverY, W.zOverY] W.polynomialAtInfinity = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [val_zero]
  change algebraMap (Away W.projectiveGrading (W.projectiveCoordinate 1)) W.LY _ = 0
  rw [← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  have e1 : (algebraMap (Away W.projectiveGrading (W.projectiveCoordinate 1)) W.LY).comp
      W.awayYAlgebraMap = algebraMap R W.LY :=
    RingHom.ext W.val_awayYAlgebraMap
  have e2 : (fun i ↦ algebraMap (Away W.projectiveGrading (W.projectiveCoordinate 1)) W.LY
      (![W.xOverY, W.zOverY] i)) =
      ![algebraMap _ W.LY (W.projectiveCoordinate 0) * W.uY,
        algebraMap _ W.LY (W.projectiveCoordinate 2) * W.uY] := by
    funext i
    fin_cases i
    · exact W.val_xOverY
    · exact W.val_zOverY
  rw [e1, e2, coe_eval₂Hom, ← aeval_def,
    W.aeval_polynomialAtInfinity_mul _ (algebraMap _ W.LY (W.projectiveCoordinate 1)) _ _
      (IsLocalization.Away.mul_invSelf _), aeval_coords,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl), map_zero, mul_zero]

/-- The homogenization `B_W → (S_W[1 / Y])₀`: `z ↦ X / Y`, `w ↦ Z / Y`. -/
noncomputable def awayYHomogenize :
    W.CoordinateRingAtInfinity →+* Away W.projectiveGrading (W.projectiveCoordinate 1) :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom W.awayYAlgebraMap ![W.xOverY, W.zOverY]) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, W.eval₂Hom_polynomialAtInfinity, mul_zero])

/-- `B_W → (S_W[1 / Y])₀` sends `z` to `X / Y`. -/
theorem awayYHomogenize_zAtInfinity : W.awayYHomogenize W.zAtInfinity = W.xOverY := by
  simp [awayYHomogenize, zAtInfinity]

/-- `B_W → (S_W[1 / Y])₀` sends `w` to `Z / Y`. -/
theorem awayYHomogenize_wAtInfinity : W.awayYHomogenize W.wAtInfinity = W.zOverY := by
  simp [awayYHomogenize, wAtInfinity]

/-- `B_W → (S_W[1 / Y])₀` is compatible with the maps from `R`. -/
theorem awayYHomogenize_algebraMap (r : R) :
    W.awayYHomogenize (algebraMap R _ r) = W.awayYAlgebraMap r := by
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) W.CoordinateRingAtInfinity,
    MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq]
  simp [awayYHomogenize]

/-- `(S_W[1 / Y])₀ → B_W` is compatible with the maps from `R`. -/
theorem awayYDehomogenize_awayYAlgebraMap (r : R) :
    W.awayYDehomogenize (W.awayYAlgebraMap r) = algebraMap R _ r := by
  simp only [awayYDehomogenize, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    val_awayYAlgebraMap]
  rw [IsScalarTower.algebraMap_apply R W.HomogeneousCoordinateRing W.LY, Localization.awayLift,
    IsLocalization.Away.lift_eq]
  simp

/-- `(S_W[1 / Y])₀ → B_W` sends `X / Y` to `z`. -/
theorem awayYDehomogenize_xOverY : W.awayYDehomogenize W.xOverY = W.zAtInfinity := by
  rw [xOverY, awayYDehomogenize_mk]
  simp [projectiveCoordinate, homogeneousToAtInfinity_mk, dehomogenizeY]

/-- `(S_W[1 / Y])₀ → B_W` sends `Z / Y` to `w`. -/
theorem awayYDehomogenize_zOverY : W.awayYDehomogenize W.zOverY = W.wAtInfinity := by
  rw [zOverY, awayYDehomogenize_mk]
  simp [projectiveCoordinate, homogeneousToAtInfinity_mk, dehomogenizeY]

/-- `B_W → (S_W[1 / Y])₀ → B_W` is the identity. -/
theorem awayYDehomogenize_comp_awayYHomogenize :
    W.awayYDehomogenize.comp W.awayYHomogenize = RingHom.id _ := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_))
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply, awayYHomogenize_algebraMap,
      awayYDehomogenize_awayYAlgebraMap]
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    fin_cases i
    · exact (congrArg W.awayYDehomogenize W.awayYHomogenize_zAtInfinity).trans
        W.awayYDehomogenize_xOverY
    · exact (congrArg W.awayYDehomogenize W.awayYHomogenize_wAtInfinity).trans
        W.awayYDehomogenize_zOverY

private lemma val_awayYHomogenize_homogeneousToAtInfinity (p : MvPolynomial (Fin 3) R) :
    (W.awayYHomogenize (W.homogeneousToAtInfinity (Ideal.Quotient.mk _ p))).val =
      MvPolynomial.aeval ![algebraMap _ W.LY (W.projectiveCoordinate 0) * W.uY, 1,
        algebraMap _ W.LY (W.projectiveCoordinate 2) * W.uY] p := by
  have : (algebraMap (Away W.projectiveGrading (W.projectiveCoordinate 1)) W.LY).comp
      (W.awayYHomogenize.comp
      (W.homogeneousToAtInfinity.toRingHom.comp (Ideal.Quotient.mk _))) =
      (MvPolynomial.aeval ![algebraMap _ W.LY (W.projectiveCoordinate 0) * W.uY, 1,
        algebraMap _ W.LY (W.projectiveCoordinate 2) * W.uY]).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        homogeneousToAtInfinity_mk, dehomogenizeY, aeval_C, awayYHomogenize_algebraMap,
        HomogeneousLocalization.algebraMap_apply, val_awayYAlgebraMap]
    · fin_cases i
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          homogeneousToAtInfinity_mk, dehomogenizeY, aeval_X,
          HomogeneousLocalization.algebraMap_apply]
        simpa [awayYHomogenize_zAtInfinity] using W.val_xOverY
      · simp [homogeneousToAtInfinity_mk, dehomogenizeY]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          homogeneousToAtInfinity_mk, dehomogenizeY, aeval_X,
          HomogeneousLocalization.algebraMap_apply]
        simpa [awayYHomogenize_wAtInfinity] using W.val_zOverY
  exact RingHom.congr_fun this p

private lemma val_awayYHomogenize_homogeneousToAtInfinity_of_isHomogeneous {n : ℕ}
    {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous n) :
    (W.awayYHomogenize (W.homogeneousToAtInfinity (Ideal.Quotient.mk _ p))).val =
      algebraMap _ W.LY (Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial}) p) *
        W.uY ^ n := by
  have e : ![algebraMap _ W.LY (W.projectiveCoordinate 0) * W.uY, 1,
      algebraMap _ W.LY (W.projectiveCoordinate 2) * W.uY] =
      W.uY • ![algebraMap _ W.LY (W.projectiveCoordinate 0),
        algebraMap _ W.LY (W.projectiveCoordinate 1),
        algebraMap _ W.LY (W.projectiveCoordinate 2)] := by
    funext i
    fin_cases i
    · simp [mul_comm]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Pi.smul_apply, smul_eq_mul]
      rw [mul_comm, IsLocalization.Away.mul_invSelf]
    · simp [mul_comm]
  rw [val_awayYHomogenize_homogeneousToAtInfinity, e, aeval_def, ← eval_map,
    (hp.map _).eval_smul, eval_map, ← aeval_def, aeval_coords, mul_comm]

/-- `(S_W[1 / Y])₀ → B_W → (S_W[1 / Y])₀` is the identity. -/
theorem awayYHomogenize_comp_awayYDehomogenize :
    W.awayYHomogenize.comp W.awayYDehomogenize = RingHom.id _ := by
  ext x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective W.projectiveGrading (W.projectiveCoordinate_mem 1) x
  have ha' := ha
  obtain ⟨p, hp, rfl⟩ := ha'
  have hp' : p.IsHomogeneous n := by simpa using (mem_homogeneousSubmodule _ _).mp hp
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [awayYDehomogenize_mk, Away.val_mk, val_mk_eq]
  exact W.val_awayYHomogenize_homogeneousToAtInfinity_of_isHomogeneous hp'

/-- **Dehomogenization at `Y`.** Let `W` be a Weierstrass curve over a commutative ring `R`, with
homogeneous coordinate ring `S_W = R[X, Y, Z] / (F)`,
`F = Y² Z + a₁ X Y Z + a₃ Y Z² - X³ - a₂ X² Z - a₄ X Z² - a₆ Z³`, graded by total degree. Then
the degree zero part `(S_W[1 / Y])₀` of the localization at `Y`
(`HomogeneousLocalization.Away`) is isomorphic as a ring to the coordinate ring at infinity
`B_W = R[z, w] / (h)`, `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`. The
isomorphism sends `a / Y ^ n` to `a(z, 1, w)` (`awayYRingEquiv_mk`), in particular `X / Y ↦ z`
and `Z / Y ↦ w`; its inverse sends `z ↦ X / Y` and `w ↦ Z / Y`
(`awayYRingEquiv_xOverY`, `awayYRingEquiv_zOverY`, `awayYRingEquiv_symm_zAtInfinity`,
`awayYRingEquiv_symm_wAtInfinity`). It is compatible with the maps from `R`
(`awayYRingEquiv_algebraMap`); it is stated as a ring isomorphism since Mathlib puts no
`R`-algebra structure on `(S_W[1 / Y])₀`.

This is the identification of the chart `Y ≠ 0` of the projective curve with `Spec B_W`, with
`z = X / Y` and `w = Z / Y`. The source states this over a field with `Δ_W ≠ 0`; neither
hypothesis is used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34 (a projective plane curve is the
union of its standard affine charts); B. Conrad, *Minimal models for elliptic curves*, 2015,
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, (2.1), p. 2. -/
noncomputable def awayYRingEquiv :
    Away W.projectiveGrading (W.projectiveCoordinate 1) ≃+* W.CoordinateRingAtInfinity :=
  RingEquiv.ofRingHom W.awayYDehomogenize W.awayYHomogenize
    W.awayYDehomogenize_comp_awayYHomogenize W.awayYHomogenize_comp_awayYDehomogenize

/-- The isomorphism `(S_W[1 / Y])₀ ≃ B_W` sends `a / Y ^ n` to the image of `a` under
`X ↦ z`, `Y ↦ 1`, `Z ↦ w`. -/
theorem awayYRingEquiv_mk (n : ℕ) (a : W.HomogeneousCoordinateRing)
    (ha : a ∈ W.projectiveGrading (n • 1)) :
    W.awayYRingEquiv (Away.mk W.projectiveGrading (W.projectiveCoordinate_mem 1) n a ha) =
      W.homogeneousToAtInfinity a :=
  W.awayYDehomogenize_mk n a ha

/-- The isomorphism `(S_W[1 / Y])₀ ≃ B_W` sends `X / Y` to `z`. -/
theorem awayYRingEquiv_xOverY : W.awayYRingEquiv W.xOverY = W.zAtInfinity :=
  W.awayYDehomogenize_xOverY

/-- The isomorphism `(S_W[1 / Y])₀ ≃ B_W` sends `Z / Y` to `w`. -/
theorem awayYRingEquiv_zOverY : W.awayYRingEquiv W.zOverY = W.wAtInfinity :=
  W.awayYDehomogenize_zOverY

/-- The inverse of `(S_W[1 / Y])₀ ≃ B_W` sends `z` to `X / Y`. -/
theorem awayYRingEquiv_symm_zAtInfinity : W.awayYRingEquiv.symm W.zAtInfinity = W.xOverY :=
  W.awayYHomogenize_zAtInfinity

/-- The inverse of `(S_W[1 / Y])₀ ≃ B_W` sends `w` to `Z / Y`. -/
theorem awayYRingEquiv_symm_wAtInfinity : W.awayYRingEquiv.symm W.wAtInfinity = W.zOverY :=
  W.awayYHomogenize_wAtInfinity

/-- The isomorphism `(S_W[1 / Y])₀ ≃ B_W` is compatible with the maps from `R`: it sends the
image of `r ∈ R` under `R → (S_W)₀ → (S_W[1 / Y])₀` to the image of `r` in `B_W`. -/
theorem awayYRingEquiv_algebraMap (r : R) :
    W.awayYRingEquiv (algebraMap (W.projectiveGrading 0) _
      (algebraMap R (W.projectiveGrading 0) r)) = algebraMap R W.CoordinateRingAtInfinity r :=
  W.awayYDehomogenize_awayYAlgebraMap r

/-! ### The chart at infinity -/

/-- **The chart at infinity of the projective Weierstrass scheme.** Let `W` be a Weierstrass
curve over a commutative ring `R`. This is the morphism `Spec B_W → Proj S_W`, for
`B_W = R[z, w] / (h)` the coordinate ring at infinity and `S_W = R[X, Y, Z] / (F)` the
homogeneous coordinate ring: the isomorphism `Spec B_W ≅ Spec (S_W[1 / Y])₀` induced by
`awayYRingEquiv` followed by the inclusion `Proj.awayι` of the basic open set `D₊(Y)`. It is an
open immersion (`isOpenImmersion_chartAtInfinity`) with image `D₊(Y)`
(`opensRange_chartAtInfinity`), over `Spec R` (`chartAtInfinity_projectiveSchemeToSpec`).

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34; B. Conrad, *Minimal models for
elliptic curves*, 2015, <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, (2.1),
p. 2. -/
noncomputable def chartAtInfinity :
    Spec (CommRingCat.of W.CoordinateRingAtInfinity) ⟶ W.ProjectiveScheme :=
  Spec.map W.awayYRingEquiv.toCommRingCatIso.hom ≫
    Proj.awayι W.projectiveGrading (W.projectiveCoordinate 1) (W.projectiveCoordinate_mem 1)
      Nat.one_pos

/-- **The chart at infinity is an open immersion.** Let `W` be a Weierstrass curve over a
commutative ring `R`. Then `chartAtInfinity W : Spec B_W → Proj S_W` is an open immersion. -/
instance isOpenImmersion_chartAtInfinity : IsOpenImmersion W.chartAtInfinity := by
  unfold chartAtInfinity
  infer_instance

/-- **The image of the chart at infinity.** Let `W` be a Weierstrass curve over a commutative
ring `R`. The open immersion `chartAtInfinity W : Spec B_W → Proj S_W` has image the basic open
set `D₊(Y)` of `Proj S_W`, the locus `Y ≠ 0`. -/
theorem opensRange_chartAtInfinity :
    W.chartAtInfinity.opensRange =
      Proj.basicOpen W.projectiveGrading (W.projectiveCoordinate 1) :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Proj.opensRange_awayι _ _ _ _)

/-- **The chart at infinity lies over `Spec R`.** Let `W` be a Weierstrass curve over a
commutative ring `R`. The composite of `chartAtInfinity W : Spec B_W → Proj S_W` with the
structure morphism `Proj S_W → Spec R` is the morphism `Spec B_W → Spec R` induced by the
structure map `R → B_W`. -/
theorem chartAtInfinity_projectiveSchemeToSpec :
    W.chartAtInfinity ≫ W.projectiveSchemeToSpec =
      Spec.map (CommRingCat.ofHom (algebraMap R W.CoordinateRingAtInfinity)) := by
  rw [chartAtInfinity, projectiveSchemeToSpec, Category.assoc, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact W.awayYRingEquiv_algebraMap r

/-! ### The zero section -/

/-- **The zero section of the projective Weierstrass scheme.** Let `W` be a Weierstrass curve
over a commutative ring `R`. This is the morphism `Spec R → Proj S_W` given by the point
`z = w = 0` of the chart at infinity, that is, `Spec` of the evaluation `B_W → R` at
`z = w = 0` (`evalAtInfinity`) followed by `chartAtInfinity W`: the point `O = (0 : 1 : 0)`. It
is a section of the structure morphism (`zeroSection_projectiveSchemeToSpec`).

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Example 4.20, p. 38 (the point at infinity
`(0 : 1 : 0)`); B. Conrad, *Minimal models for elliptic curves*, 2015,
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, Definition 2.1, p. 2 (the
identity section corresponding to `[0, 1, 0]`). -/
noncomputable def zeroSection : Spec (CommRingCat.of R) ⟶ W.ProjectiveScheme :=
  Spec.map (CommRingCat.ofHom W.evalAtInfinity.toRingHom) ≫ W.chartAtInfinity

/-- **The zero section is a section.** Let `W` be a Weierstrass curve over a commutative ring
`R`. The composite of `zeroSection W : Spec R → Proj S_W` with the structure morphism
`Proj S_W → Spec R` is the identity of `Spec R`. -/
theorem zeroSection_projectiveSchemeToSpec :
    W.zeroSection ≫ W.projectiveSchemeToSpec = 𝟙 _ := by
  rw [zeroSection, Category.assoc, chartAtInfinity_projectiveSchemeToSpec, ← Spec.map_comp,
    ← Spec.map_id]
  congr 1
  ext r
  exact W.evalAtInfinity.commutes r

end WeierstrassCurve
