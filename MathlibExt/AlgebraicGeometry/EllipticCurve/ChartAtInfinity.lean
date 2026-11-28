/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The two affine charts of a projective Weierstrass cubic

Let `W` be a Weierstrass curve over a commutative ring `R`, with projective equation
`Y² Z + a₁ X Y Z + a₃ Y Z² = X³ + a₂ X² Z + a₄ X Z² + a₆ Z³`. Its chart `Z ≠ 0` has coordinate ring
`A_W = R[x, y] / (g)`, with `g = y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆`, which is Mathlib's
`WeierstrassCurve.Affine.CoordinateRing`. Its chart `Y ≠ 0` has coordinates `z = X / Y` and
`w = Z / Y` and coordinate ring `B_W = R[z, w] / (h)`, with
`h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`.

This file defines `h` (`WeierstrassCurve.polynomialAtInfinity`), `B_W`
(`WeierstrassCurve.CoordinateRingAtInfinity`) and the evaluation `B_W → R` at the point at infinity
`z = w = 0` (`WeierstrassCurve.evalAtInfinity`), and proves:

* over a field, the only point of the projective curve with `Z = 0` is `(0 : 1 : 0)`, and a point
  with `Y ≠ 0` lies on the curve exactly when `h(X / Y, Z / Y) = 0`;
* the identities `w³ g(z / w, 1 / w) = h(z, w)` and `y³ h(x / y, 1 / y) = g(x, y)`, for a unit `w`,
  respectively `y`, of any commutative `R`-algebra;
* the `R`-algebra isomorphism `A_W[1 / y] ≃ B_W[1 / w]` with `x ↦ z / w` and `y ↦ 1 / w`, whose
  inverse sends `z ↦ x / y` and `w ↦ 1 / y`
  (`WeierstrassCurve.awayYEquivAwayW`).

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34, and Example 4.20, p. 38.
* B. Conrad, *Minimal models for elliptic curves*, notes, 2015,
  <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, (2.1) and Definition 2.1, p. 2.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The equation in the chart at infinity -/

/-- **The Weierstrass polynomial in the chart at infinity.** Let `W` be a Weierstrass curve over a
commutative ring `R` with coefficients `a₁, a₂, a₃, a₄, a₆`. Its polynomial at infinity is
`h(z, w) = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³` in `R[z, w]`, the projective
equation `Y² Z + a₁ X Y Z + a₃ Y Z² - X³ - a₂ X² Z - a₄ X Z² - a₆ Z³` read at `Y = 1`, `X = z`,
`Z = w`. Here `R[z, w]` is `MvPolynomial (Fin 2) R`, with `z` the variable `0` and `w` the
variable `1`. -/
noncomputable def polynomialAtInfinity : MvPolynomial (Fin 2) R :=
  MvPolynomial.X 1 + MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.C W.a₃ * MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 -
    MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 -
    MvPolynomial.C W.a₄ * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 -
    MvPolynomial.C W.a₆ * MvPolynomial.X 1 ^ 3

/-- **Evaluating the polynomial at infinity.** Let `W` be a Weierstrass curve over a commutative
ring `R`, let `S` be a commutative `R`-algebra and let `z, w ∈ S`. Then the value of
`h = polynomialAtInfinity W` at `(z, w)` is
`w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`, with the coefficients mapped to `S`. -/
theorem aeval_polynomialAtInfinity {S : Type*} [CommRing S] [Algebra R S] (z w : S) :
    MvPolynomial.aeval ![z, w] W.polynomialAtInfinity =
      w + algebraMap R S W.a₁ * z * w + algebraMap R S W.a₃ * w ^ 2 - z ^ 3 -
        algebraMap R S W.a₂ * z ^ 2 * w - algebraMap R S W.a₄ * z * w ^ 2 -
        algebraMap R S W.a₆ * w ^ 3 := by
  simp [polynomialAtInfinity]

/-- **The coordinate ring of the chart at infinity.** Let `W` be a Weierstrass curve over a
commutative ring `R`. Its coordinate ring at infinity is `B_W = R[z, w] / (h)`, for
`h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³` (`polynomialAtInfinity W`): the
coordinate ring of the chart `Y ≠ 0` of the projective curve, with `z = X / Y` and `w = Z / Y`. -/
abbrev CoordinateRingAtInfinity : Type _ :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span {W.polynomialAtInfinity}

/-- The coordinate `z = X / Y` of the chart at infinity, as an element of `B_W`. -/
noncomputable def zAtInfinity : W.CoordinateRingAtInfinity :=
  Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The coordinate `w = Z / Y` of the chart at infinity, as an element of `B_W`. -/
noncomputable def wAtInfinity : W.CoordinateRingAtInfinity :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The coordinate `x = X / Z` of the affine chart, as an element of `A_W`. -/
noncomputable def affineX : W.toAffine.CoordinateRing :=
  AdjoinRoot.of W.toAffine.polynomial Polynomial.X

/-- The coordinate `y = Y / Z` of the affine chart, as an element of `A_W`. -/
noncomputable def affineY : W.toAffine.CoordinateRing :=
  AdjoinRoot.root W.toAffine.polynomial

/-- **The relation in `B_W`.** Let `W` be a Weierstrass curve over a commutative ring `R`. In
`B_W`, the coordinates `z` and `w` satisfy
`w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³ = 0`. -/
theorem relation_atInfinity :
    W.wAtInfinity + algebraMap R _ W.a₁ * W.zAtInfinity * W.wAtInfinity +
        algebraMap R _ W.a₃ * W.wAtInfinity ^ 2 - W.zAtInfinity ^ 3 -
        algebraMap R _ W.a₂ * W.zAtInfinity ^ 2 * W.wAtInfinity -
        algebraMap R _ W.a₄ * W.zAtInfinity * W.wAtInfinity ^ 2 -
        algebraMap R _ W.a₆ * W.wAtInfinity ^ 3 = 0 := by
  have h : Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) W.polynomialAtInfinity = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have key : ∀ I : Ideal (MvPolynomial (Fin 2) R), Ideal.Quotient.mk I W.polynomialAtInfinity =
      Ideal.Quotient.mk I (MvPolynomial.X 1) +
        algebraMap R _ W.a₁ * Ideal.Quotient.mk I (MvPolynomial.X 0) *
          Ideal.Quotient.mk I (MvPolynomial.X 1) +
        algebraMap R _ W.a₃ * Ideal.Quotient.mk I (MvPolynomial.X 1) ^ 2 -
        Ideal.Quotient.mk I (MvPolynomial.X 0) ^ 3 -
        algebraMap R _ W.a₂ * Ideal.Quotient.mk I (MvPolynomial.X 0) ^ 2 *
          Ideal.Quotient.mk I (MvPolynomial.X 1) -
        algebraMap R _ W.a₄ * Ideal.Quotient.mk I (MvPolynomial.X 0) *
          Ideal.Quotient.mk I (MvPolynomial.X 1) ^ 2 -
        algebraMap R _ W.a₆ * Ideal.Quotient.mk I (MvPolynomial.X 1) ^ 3 := by
    intro I
    simp only [polynomialAtInfinity, map_add, map_sub, map_mul, map_pow,
      ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  rw [key] at h
  exact h

/-- **The relation in `A_W`.** Let `W` be a Weierstrass curve over a commutative ring `R`. In
`A_W`, the coordinates `x` and `y` satisfy
`y² + a₁ x y + a₃ y - (x³ + a₂ x² + a₄ x + a₆) = 0`. -/
theorem relation_affine :
    W.affineY ^ 2 + algebraMap R _ W.a₁ * W.affineX * W.affineY +
        algebraMap R _ W.a₃ * W.affineY -
        (W.affineX ^ 3 + algebraMap R _ W.a₂ * W.affineX ^ 2 +
          algebraMap R _ W.a₄ * W.affineX + algebraMap R _ W.a₆) = 0 := by
  have h : AdjoinRoot.mk W.toAffine.polynomial
      (X ^ 2 + C (C W.a₁ * X + C W.a₃) * X - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) =
        0 :=
    AdjoinRoot.mk_self
  simp only [map_add, map_sub, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  simp only [affineX, affineY, IsScalarTower.algebraMap_apply R R[X] (AdjoinRoot _),
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdjoinRoot.algebraMap_eq]
  linear_combination h

/-! ### Evaluation at the point at infinity -/

/-- **Evaluation at the point at infinity.** Let `W` be a Weierstrass curve over a commutative
ring `R`. This is the `R`-algebra map `B_W → R` sending the class of `p(z, w)` to `p(0, 0)`, so
`z ↦ 0` and `w ↦ 0`; it is well defined since `h(0, 0) = 0`. -/
noncomputable def evalAtInfinity : W.CoordinateRingAtInfinity →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval 0) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    refine mul_eq_zero_of_right _ ?_
    rw [MvPolynomial.aeval_zero]
    simp [polynomialAtInfinity])

/-- Evaluation at the point at infinity sends the class of `p ∈ R[z, w]` to its constant
coefficient `p(0, 0)`. -/
theorem evalAtInfinity_mk (p : MvPolynomial (Fin 2) R) :
    W.evalAtInfinity (Ideal.Quotient.mk _ p) = MvPolynomial.constantCoeff p := by
  simp [evalAtInfinity]

/-- Evaluation at the point at infinity sends `z` to `0`. -/
theorem evalAtInfinity_zAtInfinity : W.evalAtInfinity W.zAtInfinity = 0 := by
  simp [zAtInfinity, evalAtInfinity_mk]

/-- Evaluation at the point at infinity sends `w` to `0`. -/
theorem evalAtInfinity_wAtInfinity : W.evalAtInfinity W.wAtInfinity = 0 := by
  simp [wAtInfinity, evalAtInfinity_mk]

/-! ### Points of the projective curve -/

open WeierstrassCurve.Projective in
/-- **The only point at infinity is `(0 : 1 : 0)`.** Let `W` be a Weierstrass curve over a field
`F` and let `P = (X, Y, Z)` be a nonzero solution of the projective equation
`Y² Z + a₁ X Y Z + a₃ Y Z² = X³ + a₂ X² Z + a₄ X Z² + a₆ Z³` with `Z = 0`. Then `P` is equivalent
to `(0, 1, 0)`, that is, `P = (0 : 1 : 0)` as a projective point.

Since `F` is any field, this applies over every field extension of the field of definition, to the
base change of the curve. Mathlib's `WeierstrassCurve.Projective.equiv_zero_of_Z_eq_zero` assumes
`P` nonsingular; this version needs only that `P` is a nonzero solution. -/
theorem Projective.equiv_zero_of_equation_of_Z_eq_zero {F : Type*} [Field F]
    {W : WeierstrassCurve.Projective F} {P : Fin 3 → F} (hP : W.Equation P) (hP0 : P ≠ 0)
    (hPz : P 2 = 0) : P ≈ ![0, 1, 0] := by
  have hPx : P 0 = 0 := X_eq_zero_of_Z_eq_zero hP hPz
  have hPy : P 1 ≠ 0 := by
    intro hPy
    apply hP0
    funext i
    fin_cases i <;> simp [hPx, hPy, hPz]
  refine ⟨Units.mk0 (P 1) hPy, ?_⟩
  funext i
  fin_cases i <;> simp [hPx, hPz]

open WeierstrassCurve.Projective in
/-- **Points with `Y ≠ 0` lie in the chart at infinity.** Let `W` be a Weierstrass curve over a
field `F` and let `P = (X, Y, Z)` with `Y ≠ 0`. Then `P` solves the projective equation
`Y² Z + a₁ X Y Z + a₃ Y Z² = X³ + a₂ X² Z + a₄ X Z² + a₆ Z³` if and only if
`(z, w) = (X / Y, Z / Y)` solves
`h(z, w) = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³ = 0`. In particular
`(0 : 1 : 0)` is the point `z = w = 0` of the chart at infinity. -/
theorem Projective.equation_iff_aeval_polynomialAtInfinity {F : Type*} [Field F]
    (W : WeierstrassCurve F) {P : Fin 3 → F} (hPy : P 1 ≠ 0) :
    W.toProjective.Equation P ↔
      MvPolynomial.aeval ![P 0 / P 1, P 2 / P 1] W.polynomialAtInfinity = 0 := by
  rw [equation_iff, aeval_polynomialAtInfinity]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  have h3 : P 1 ^ 3 ≠ 0 := pow_ne_zero 3 hPy
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    field_simp at h
    linear_combination h

/-! ### The identities between the two equations -/

/-- **From the affine equation to the equation at infinity.** Let `W` be a Weierstrass curve over
a commutative ring `R`, let `S` be a commutative `R`-algebra, let `z ∈ S` and let `w` be a unit
of `S`. Then `w³ g(z / w, 1 / w) = h(z, w)`, where
`g(x, y) = y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆` is the Weierstrass polynomial of `W` over
`S` and `h(z, w) = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`. Taking for `S` the ring
`R[z, w, w⁻¹]` gives the identity of polynomials. -/
theorem pow_three_mul_evalEval_polynomial_div {S : Type*} [CommRing S] [Algebra R S] (z : S)
    (w : Sˣ) :
    (w : S) ^ 3 * (W.baseChange S).toAffine.polynomial.evalEval (z * ↑w⁻¹) ↑w⁻¹ =
      MvPolynomial.aeval ![z, (w : S)] W.polynomialAtInfinity := by
  rw [Affine.evalEval_polynomial, aeval_polynomialAtInfinity]
  have hw : (w : S) * ↑w⁻¹ = 1 := w.mul_inv
  set u : S := ↑w⁻¹
  set v : S := (w : S)
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  linear_combination
    (v * (v * u + 1) + algebraMap R S W.a₁ * z * v * (v * u + 1) + algebraMap R S W.a₃ * v ^ 2 -
      z ^ 3 * (v ^ 2 * u ^ 2 + v * u + 1) - algebraMap R S W.a₂ * z ^ 2 * v * (v * u + 1) -
      algebraMap R S W.a₄ * z * v ^ 2) * hw

/-- **From the equation at infinity to the affine equation.** Let `W` be a Weierstrass curve over
a commutative ring `R`, let `S` be a commutative `R`-algebra, let `x ∈ S` and let `y` be a unit of
`S`. Then `y³ h(x / y, 1 / y) = g(x, y)`, where
`h(z, w) = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³` and
`g(x, y) = y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆` is the Weierstrass polynomial of `W` over
`S`. Taking for `S` the ring `R[x, y, y⁻¹]` gives the identity of polynomials. -/
theorem pow_three_mul_aeval_polynomialAtInfinity_div {S : Type*} [CommRing S] [Algebra R S]
    (x : S) (y : Sˣ) :
    (y : S) ^ 3 * MvPolynomial.aeval ![x * ↑y⁻¹, (↑y⁻¹ : S)] W.polynomialAtInfinity =
      (W.baseChange S).toAffine.polynomial.evalEval x y := by
  rw [Affine.evalEval_polynomial, aeval_polynomialAtInfinity]
  have hy : (y : S) * ↑y⁻¹ = 1 := y.mul_inv
  set u : S := ↑y⁻¹
  set v : S := (y : S)
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  linear_combination
    (v ^ 2 + (algebraMap R S W.a₁ * x * v + algebraMap R S W.a₃ * v) * (v * u + 1) -
      (x ^ 3 + algebraMap R S W.a₂ * x ^ 2 + algebraMap R S W.a₄ * x + algebraMap R S W.a₆) *
        (v ^ 2 * u ^ 2 + v * u + 1)) * hy

/-! ### The isomorphism of the two charts on their overlap -/

/-- A ring homomorphism out of the localization `S = R[1 / x]` sends `1 / x` to the inverse of the
image of `x`. -/
private lemma map_invSelf_eq {A S T : Type*} [CommRing A] [CommRing S] [CommRing T] [Algebra A S]
    (x : A) [IsLocalization.Away x S] (φ : S →+* T) {t : T}
    (ht : φ (algebraMap A S x) * t = 1) : φ (IsLocalization.Away.invSelf x) = t := by
  calc φ (IsLocalization.Away.invSelf x)
      = φ (IsLocalization.Away.invSelf x) * (φ (algebraMap A S x) * t) := by rw [ht, mul_one]
    _ = φ (algebraMap A S x * IsLocalization.Away.invSelf x) * t := by rw [map_mul]; ring
    _ = t := by rw [IsLocalization.Away.mul_invSelf, map_one, one_mul]

/-- The affine chart `A_W[1 / y]` of the overlap. -/
abbrev AffineAwayY : Type _ := Localization.Away W.affineY

/-- The chart at infinity `B_W[1 / w]` of the overlap. -/
abbrev AtInfinityAwayW : Type _ := Localization.Away W.wAtInfinity

/-- The map `A_W → B_W[1 / w]`, `x ↦ z / w`, `y ↦ 1 / w`. -/
noncomputable def affineToAwayW : W.toAffine.CoordinateRing →+* W.AtInfinityAwayW :=
  AdjoinRoot.lift
    (Polynomial.eval₂RingHom (algebraMap R W.AtInfinityAwayW)
      (algebraMap _ W.AtInfinityAwayW W.zAtInfinity * IsLocalization.Away.invSelf W.wAtInfinity))
    (IsLocalization.Away.invSelf W.wAtInfinity) (by
      have hrel := congrArg (algebraMap _ W.AtInfinityAwayW) W.relation_atInfinity
      have hw := IsLocalization.Away.mul_invSelf (S := W.AtInfinityAwayW) W.wAtInfinity
      simp only [map_sub, map_add, map_mul, map_pow, map_zero,
        ← IsScalarTower.algebraMap_apply] at hrel
      set Z := algebraMap _ W.AtInfinityAwayW W.zAtInfinity
      set w' := algebraMap _ W.AtInfinityAwayW W.wAtInfinity
      set v := IsLocalization.Away.invSelf (S := W.AtInfinityAwayW) W.wAtInfinity
      simp only [Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
        eval₂_C, coe_eval₂RingHom]
      linear_combination v ^ 3 * hrel -
        (v ^ 2 + algebraMap R _ W.a₁ * Z * v ^ 2 + algebraMap R _ W.a₃ * v * (1 + v * w') -
          algebraMap R _ W.a₂ * Z ^ 2 * v ^ 2 - algebraMap R _ W.a₄ * Z * v * (1 + v * w') -
          algebraMap R _ W.a₆ * (1 + v * w' + v ^ 2 * w' ^ 2)) * hw)

/-- The map `B_W → A_W[1 / y]`, `z ↦ x / y`, `w ↦ 1 / y`. -/
noncomputable def atInfinityToAwayY : W.CoordinateRingAtInfinity →+* W.AffineAwayY :=
  Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom (algebraMap R W.AffineAwayY)
      ![algebraMap _ W.AffineAwayY W.affineX * IsLocalization.Away.invSelf W.affineY,
        IsLocalization.Away.invSelf W.affineY]) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul]
      refine mul_eq_zero_of_right _ ?_
      have hrel := congrArg (algebraMap _ W.AffineAwayY) W.relation_affine
      have hy := IsLocalization.Away.mul_invSelf (S := W.AffineAwayY) W.affineY
      simp only [map_sub, map_add, map_mul, map_pow, map_zero,
        ← IsScalarTower.algebraMap_apply] at hrel
      set X' := algebraMap _ W.AffineAwayY W.affineX
      set Y' := algebraMap _ W.AffineAwayY W.affineY
      set u := IsLocalization.Away.invSelf (S := W.AffineAwayY) W.affineY
      simp only [polynomialAtInfinity, map_sub, map_add, map_mul, map_pow,
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      linear_combination u ^ 3 * hrel -
        (u * (1 + u * Y') + algebraMap R _ W.a₁ * X' * u ^ 2 + algebraMap R _ W.a₃ * u ^ 2) * hy)

theorem affineToAwayW_affineX :
    W.affineToAwayW W.affineX =
      algebraMap _ W.AtInfinityAwayW W.zAtInfinity * IsLocalization.Away.invSelf W.wAtInfinity := by
  simp [affineToAwayW, affineX]

theorem affineToAwayW_affineY :
    W.affineToAwayW W.affineY = IsLocalization.Away.invSelf W.wAtInfinity := by
  simp [affineToAwayW, affineY]

theorem atInfinityToAwayY_zAtInfinity :
    W.atInfinityToAwayY W.zAtInfinity =
      algebraMap _ W.AffineAwayY W.affineX * IsLocalization.Away.invSelf W.affineY := by
  simp [atInfinityToAwayY, zAtInfinity]

theorem atInfinityToAwayY_wAtInfinity :
    W.atInfinityToAwayY W.wAtInfinity = IsLocalization.Away.invSelf W.affineY := by
  simp [atInfinityToAwayY, wAtInfinity]

private lemma isUnit_invSelf {A S : Type*} [CommRing A] [CommRing S] [Algebra A S] (x : A)
    [IsLocalization.Away x S] : IsUnit (IsLocalization.Away.invSelf (S := S) x) :=
  isUnit_iff_exists_inv.mpr ⟨algebraMap A S x, by rw [mul_comm, IsLocalization.Away.mul_invSelf]⟩

/-- The map `A_W[1 / y] → B_W[1 / w]`, `x ↦ z / w`, `y ↦ 1 / w`. -/
noncomputable def awayYToAwayW : W.AffineAwayY →+* W.AtInfinityAwayW :=
  IsLocalization.Away.lift W.affineY (g := W.affineToAwayW)
    (by rw [affineToAwayW_affineY]; exact isUnit_invSelf _)

/-- The map `B_W[1 / w] → A_W[1 / y]`, `z ↦ x / y`, `w ↦ 1 / y`. -/
noncomputable def awayWToAwayY : W.AtInfinityAwayW →+* W.AffineAwayY :=
  IsLocalization.Away.lift W.wAtInfinity (g := W.atInfinityToAwayY)
    (by rw [atInfinityToAwayY_wAtInfinity]; exact isUnit_invSelf _)

private lemma awayYToAwayW_algebraMap (a : W.toAffine.CoordinateRing) :
    W.awayYToAwayW (algebraMap _ _ a) = W.affineToAwayW a :=
  IsLocalization.Away.lift_eq _ _ a

private lemma awayWToAwayY_algebraMap (a : W.CoordinateRingAtInfinity) :
    W.awayWToAwayY (algebraMap _ _ a) = W.atInfinityToAwayY a :=
  IsLocalization.Away.lift_eq _ _ a

private lemma awayYToAwayW_invSelf :
    W.awayYToAwayW (IsLocalization.Away.invSelf W.affineY) =
      algebraMap _ W.AtInfinityAwayW W.wAtInfinity :=
  map_invSelf_eq _ _ (by
    rw [awayYToAwayW_algebraMap, affineToAwayW_affineY, mul_comm,
      IsLocalization.Away.mul_invSelf])

private lemma awayWToAwayY_invSelf :
    W.awayWToAwayY (IsLocalization.Away.invSelf W.wAtInfinity) =
      algebraMap _ W.AffineAwayY W.affineY :=
  map_invSelf_eq _ _ (by
    rw [awayWToAwayY_algebraMap, atInfinityToAwayY_wAtInfinity, mul_comm,
      IsLocalization.Away.mul_invSelf])

private lemma affineToAwayW_algebraMap (r : R) :
    W.affineToAwayW (algebraMap R _ r) = algebraMap R _ r := by
  simp [affineToAwayW, IsScalarTower.algebraMap_apply R R[X] (AdjoinRoot _),
    AdjoinRoot.algebraMap_eq]

private lemma atInfinityToAwayY_algebraMap (r : R) :
    W.atInfinityToAwayY (algebraMap R _ r) = algebraMap R _ r := by
  simp [atInfinityToAwayY, IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R)
    W.CoordinateRingAtInfinity]

theorem awayWToAwayY_comp_awayYToAwayW :
    W.awayWToAwayY.comp W.awayYToAwayW = RingHom.id _ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers W.affineY) ?_
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
    · simp only [RingHom.comp_apply, RingHom.id_apply, awayYToAwayW_algebraMap]
      have e : AdjoinRoot.of W.toAffine.polynomial (C r) =
          algebraMap R W.toAffine.CoordinateRing r := by
        simp [IsScalarTower.algebraMap_apply R R[X] (AdjoinRoot _), AdjoinRoot.algebraMap_eq]
      rw [e, affineToAwayW_algebraMap, IsScalarTower.algebraMap_apply R
        W.CoordinateRingAtInfinity, awayWToAwayY_algebraMap, atInfinityToAwayY_algebraMap,
        ← IsScalarTower.algebraMap_apply]
    · simp only [RingHom.comp_apply, RingHom.id_apply, awayYToAwayW_algebraMap]
      change W.awayWToAwayY (W.affineToAwayW W.affineX) = algebraMap _ _ W.affineX
      rw [affineToAwayW_affineX, map_mul, awayWToAwayY_algebraMap, awayWToAwayY_invSelf,
        atInfinityToAwayY_zAtInfinity, mul_assoc, mul_comm (IsLocalization.Away.invSelf _),
        IsLocalization.Away.mul_invSelf, mul_one]
  · simp only [RingHom.comp_apply, RingHom.id_apply, awayYToAwayW_algebraMap]
    change W.awayWToAwayY (W.affineToAwayW W.affineY) = algebraMap _ _ W.affineY
    rw [affineToAwayW_affineY, awayWToAwayY_invSelf]

theorem awayYToAwayW_comp_awayWToAwayY :
    W.awayYToAwayW.comp W.awayWToAwayY = RingHom.id _ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers W.wAtInfinity) ?_
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_))
  · simp only [RingHom.comp_apply, RingHom.id_apply, awayWToAwayY_algebraMap]
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap, atInfinityToAwayY_algebraMap,
      IsScalarTower.algebraMap_apply R W.toAffine.CoordinateRing, awayYToAwayW_algebraMap,
      affineToAwayW_algebraMap, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R W.CoordinateRingAtInfinity]
  · simp only [RingHom.comp_apply, RingHom.id_apply, awayWToAwayY_algebraMap]
    fin_cases i
    · change W.awayYToAwayW (W.atInfinityToAwayY W.zAtInfinity) = algebraMap _ _ W.zAtInfinity
      rw [atInfinityToAwayY_zAtInfinity, map_mul, awayYToAwayW_algebraMap, awayYToAwayW_invSelf,
        affineToAwayW_affineX, mul_assoc, mul_comm (IsLocalization.Away.invSelf _),
        IsLocalization.Away.mul_invSelf, mul_one]
    · change W.awayYToAwayW (W.atInfinityToAwayY W.wAtInfinity) = algebraMap _ _ W.wAtInfinity
      rw [atInfinityToAwayY_wAtInfinity, awayYToAwayW_invSelf]

/-- **The two charts agree on their overlap.** Let `W` be a Weierstrass curve over a commutative
ring `R`, with affine coordinate ring `A_W = R[x, y] / (g)`,
`g = y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆`, and coordinate ring at infinity
`B_W = R[z, w] / (h)`, `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`. Then there is
an isomorphism of `R`-algebras `A_W[1 / y] ≃ B_W[1 / w]` sending `x ↦ z / w` and `y ↦ 1 / w`; its
inverse sends `z ↦ x / y` and `w ↦ 1 / y` (`awayYEquivAwayW_affineX`, `awayYEquivAwayW_affineY`,
`awayYEquivAwayW_symm_zAtInfinity`, `awayYEquivAwayW_symm_wAtInfinity`). It identifies the two
charts of the projective curve on their overlap `Y Z ≠ 0`.

The source states this over a field with `Δ_W ≠ 0`; neither hypothesis is used: `R` is any
commutative ring and `W` any Weierstrass curve.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34: a projective plane curve is
written "as a union of affine curves $C = C_0 \cup C_1 \cup C_2$ in the usual way"; B. Conrad,
*Minimal models for elliptic curves*, 2015,
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, (2.1), p. 2, the projective
planar Weierstrass curve. -/
noncomputable def awayYEquivAwayW : W.AffineAwayY ≃ₐ[R] W.AtInfinityAwayW :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom W.awayYToAwayW W.awayWToAwayY
    W.awayYToAwayW_comp_awayWToAwayY W.awayWToAwayY_comp_awayYToAwayW) (fun r ↦ by
      change W.awayYToAwayW (algebraMap R _ r) = _
      rw [IsScalarTower.algebraMap_apply R W.toAffine.CoordinateRing, awayYToAwayW_algebraMap,
        affineToAwayW_algebraMap])

private lemma awayYEquivAwayW_apply (a : W.AffineAwayY) :
    W.awayYEquivAwayW a = W.awayYToAwayW a := rfl

private lemma awayYEquivAwayW_symm_apply (a : W.AtInfinityAwayW) :
    W.awayYEquivAwayW.symm a = W.awayWToAwayY a := rfl

/-- The isomorphism `A_W[1 / y] ≃ B_W[1 / w]` sends `x` to `z / w`. -/
theorem awayYEquivAwayW_affineX :
    W.awayYEquivAwayW (algebraMap _ _ W.affineX) =
      algebraMap _ _ W.zAtInfinity * IsLocalization.Away.invSelf W.wAtInfinity := by
  rw [awayYEquivAwayW_apply]
  rw [awayYToAwayW_algebraMap, affineToAwayW_affineX]

/-- The isomorphism `A_W[1 / y] ≃ B_W[1 / w]` sends `y` to `1 / w`. -/
theorem awayYEquivAwayW_affineY :
    W.awayYEquivAwayW (algebraMap _ _ W.affineY) = IsLocalization.Away.invSelf W.wAtInfinity := by
  rw [awayYEquivAwayW_apply]
  rw [awayYToAwayW_algebraMap, affineToAwayW_affineY]

/-- The inverse of `A_W[1 / y] ≃ B_W[1 / w]` sends `z` to `x / y`. -/
theorem awayYEquivAwayW_symm_zAtInfinity :
    W.awayYEquivAwayW.symm (algebraMap _ _ W.zAtInfinity) =
      algebraMap _ _ W.affineX * IsLocalization.Away.invSelf W.affineY := by
  rw [awayYEquivAwayW_symm_apply]
  rw [awayWToAwayY_algebraMap, atInfinityToAwayY_zAtInfinity]

/-- The inverse of `A_W[1 / y] ≃ B_W[1 / w]` sends `w` to `1 / y`. -/
theorem awayYEquivAwayW_symm_wAtInfinity :
    W.awayYEquivAwayW.symm (algebraMap _ _ W.wAtInfinity) =
      IsLocalization.Away.invSelf W.affineY := by
  rw [awayYEquivAwayW_symm_apply]
  rw [awayWToAwayY_algebraMap, atInfinityToAwayY_wAtInfinity]

end WeierstrassCurve
