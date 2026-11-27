/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WeierstrassCurve_Affine_Point_vcInvFun_add.lean`,
`Definitions/Def_WeierstrassCurve_VariableChangePointEquiv.lean`
and
`P2M/Sol/S_WeierstrassCurve_Affine_Point_vcInvFun_add.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import MathlibExt.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic.Ring

/-!
# Variable changes on affine Weierstrass points

This file transports affine solutions, nonsingular affine points and rational points along an
admissible variable change `C`. The coordinate map of `C` preserves the Weierstrass equation
(`equation_mapAffineCoordinates_iff`) and nonsingularity (`nonsingular_mapAffineCoordinates_iff`),
so it gives the additive equivalence of points
`Affine.Point.variableChangeAddEquiv : (C • W).toAffine.Point ≃+ W.toAffine.Point`, whose inverse
applies the coordinate map of `C⁻¹`. The equivalence needs no ellipticity hypothesis; for elliptic
`W`, its underlying equivalence is the bijection `pointEquiv`
(`Affine.Point.variableChangeAddEquiv_toEquiv`).
-/

@[expose] public section

namespace WeierstrassCurve.VariableChange

universe u

variable {F : Type u} [Field F]

/-- **Coordinate map of a Weierstrass variable change.** For a variable change $C = (u, r, s, t)$
over a field $F$, with $u \in F^\times$ and $r, s, t \in F$, the affine coordinate map of $C$
sends $(x, y) \in F^2$ to $(u^2 x + r,\ u^3 y + u^2 s x + t)$. -/
def mapAffineCoordinates (C : VariableChange F) (xy : F × F) : F × F :=
  (C.u ^ 2 * xy.1 + C.r,
    C.u ^ 3 * xy.2 + C.u ^ 2 * C.s * xy.1 + C.t)

@[simp]
theorem mapAffineCoordinates_one (xy : F × F) :
    mapAffineCoordinates (1 : VariableChange F) xy = xy := by
  ext <;> simp [mapAffineCoordinates, one_def]

theorem mapAffineCoordinates_mul (C C' : VariableChange F) (xy : F × F) :
    mapAffineCoordinates (C * C') xy =
      mapAffineCoordinates C' (mapAffineCoordinates C xy) := by
  ext <;> simp only [mapAffineCoordinates, mul_def, Units.val_mul]
  · ring
  · ring

@[simp]
theorem mapAffineCoordinates_inv_apply (C : VariableChange F) (xy : F × F) :
    mapAffineCoordinates C⁻¹ (mapAffineCoordinates C xy) = xy := by
  rw [← mapAffineCoordinates_mul]
  simp

@[simp]
theorem mapAffineCoordinates_apply_inv (C : VariableChange F) (xy : F × F) :
    mapAffineCoordinates C (mapAffineCoordinates C⁻¹ xy) = xy := by
  rw [← mapAffineCoordinates_mul]
  simp

/-- **Variable changes act bijectively on affine coordinates.** For a variable change
$C = (u, r, s, t)$ over a field $F$, the map $(x, y) \mapsto (u^2 x + r,\ u^3 y + u^2 s x + t)$
is a bijection $F^2 \to F^2$, whose inverse is the corresponding map of the inverse variable
change $C^{-1}$. -/
def affineCoordinatesEquiv (C : VariableChange F) : F × F ≃ F × F where
  toFun := mapAffineCoordinates C
  invFun := mapAffineCoordinates C⁻¹
  left_inv := mapAffineCoordinates_inv_apply C
  right_inv := mapAffineCoordinates_apply_inv C

/-- **Variable changes transform the Weierstrass equation.** Let $W$ be a Weierstrass curve over
a field $F$, let $C = (u, r, s, t)$ be a variable change and let $C \cdot W$ be the transformed
curve. A pair $(x, y) \in F^2$ satisfies the Weierstrass equation of $C \cdot W$ if and only if
$(u^2 x + r,\ u^3 y + u^2 s x + t)$ satisfies the Weierstrass equation of $W$. -/
theorem equation_mapAffineCoordinates_iff (C : VariableChange F) (W : WeierstrassCurve F)
    (xy : F × F) :
    (C • W).toAffine.Equation xy.1 xy.2 ↔
      W.toAffine.Equation (mapAffineCoordinates C xy).1
        (mapAffineCoordinates C xy).2 := by
  rcases xy with ⟨x, y⟩
  change (C • W).toAffine.Equation x y ↔
    W.toAffine.Equation
      (C.u ^ 2 * x + C.r)
      (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)
  rw [(C • W).toAffine.equation_iff_variableChange,
    W.toAffine.equation_iff_variableChange]
  rw [← mul_smul]
  simp only [Affine.equation_zero, variableChange_a₆]
  simp only [mul_def, one_mul, mul_zero, zero_add, Units.val_inv_eq_inv_val,
    inv_pow, mul_eq_zero, inv_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_eq_zero_iff, Units.ne_zero, false_or, inv_one,
    Units.val_one, one_pow]
  constructor <;> intro h <;> ring_nf at h ⊢ <;> exact h

/-- **Variable changes biject affine solutions.** Let $W$ be a Weierstrass curve over a field $F$,
let $C = (u, r, s, t)$ be a variable change and let $C \cdot W$ be the transformed curve. The map
$(x, y) \mapsto (u^2 x + r,\ u^3 y + u^2 s x + t)$ is a bijection from the solutions
$(x, y) \in F^2$ of the Weierstrass equation of $C \cdot W$ onto the solutions in $F^2$ of the
Weierstrass equation of $W$; its inverse is the corresponding map of $C^{-1}$. -/
def affineEquationEquiv (C : VariableChange F) (W : WeierstrassCurve F) :
    {xy : F × F // (C • W).toAffine.Equation xy.1 xy.2} ≃
      {xy : F × F // W.toAffine.Equation xy.1 xy.2} where
  toFun xy :=
    ⟨mapAffineCoordinates C xy.1,
      (equation_mapAffineCoordinates_iff C W xy.1).mp xy.2⟩
  invFun xy :=
    ⟨mapAffineCoordinates C⁻¹ xy.1, by
      rw [equation_mapAffineCoordinates_iff]
      simpa using xy.2⟩
  left_inv xy := by
    apply Subtype.ext
    exact mapAffineCoordinates_inv_apply C xy.1
  right_inv xy := by
    apply Subtype.ext
    exact mapAffineCoordinates_apply_inv C xy.1

/-- **Variable changes biject rational points.** Let $W$ be an elliptic Weierstrass curve over a
field $F$, let $C = (u, r, s, t)$ be a variable change and let $C \cdot W$ be the transformed
curve. There is a bijection from the rational points of $C \cdot W$ to the rational points of
$W$, where in both cases the point at infinity is included; it sends the point at infinity to
the point at infinity and an affine point $(x, y)$ to $(u^2 x + r,\ u^3 y + u^2 s x + t)$. -/
noncomputable def pointEquiv (C : VariableChange F) (W : WeierstrassCurve F)
    [W.IsElliptic] :
    (C • W).toAffine.Point ≃ W.toAffine.Point :=
  (C • W).toAffine.pointEquiv |>.trans
    ((affineEquationEquiv C W).optionCongr.trans W.toAffine.pointEquiv.symm)

/-- **Variable changes preserve the point count.** Let $W$ be an elliptic Weierstrass curve over
a finite field $F$, let $C$ be a variable change and let $C \cdot W$ be the transformed curve.
Then $C \cdot W$ and $W$ have the same number of rational points. -/
theorem natCard_point_eq [Finite F] (C : VariableChange F) (W : WeierstrassCurve F)
    [W.IsElliptic] :
    Nat.card ((C • W).toAffine.Point) = Nat.card W.toAffine.Point :=
  Nat.card_congr (pointEquiv C W)

variable (C : VariableChange F) (W : WeierstrassCurve F)

private lemma partialX_mapAffineCoordinates (x y : F) :
    W.a₁ * (mapAffineCoordinates C (x, y)).2 -
        (3 * (mapAffineCoordinates C (x, y)).1 ^ 2 +
          2 * W.a₂ * (mapAffineCoordinates C (x, y)).1 + W.a₄) +
      C.s * (2 * (mapAffineCoordinates C (x, y)).2 +
        W.a₁ * (mapAffineCoordinates C (x, y)).1 + W.a₃) =
    (C.u : F) ^ 4 * ((C • W).a₁ * y - (3 * x ^ 2 + 2 * (C • W).a₂ * x + (C • W).a₄)) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [mapAffineCoordinates, variableChange_a₁, variableChange_a₂, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma partialY_mapAffineCoordinates (x y : F) :
    2 * (mapAffineCoordinates C (x, y)).2 + W.a₁ * (mapAffineCoordinates C (x, y)).1 + W.a₃ =
      (C.u : F) ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [mapAffineCoordinates, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma partials_zero_iff (x y : F) :
    ((C • W).a₁ * y - (3 * x ^ 2 + 2 * (C • W).a₂ * x + (C • W).a₄) = 0 ∧
        2 * y + (C • W).a₁ * x + (C • W).a₃ = 0) ↔
      (W.a₁ * (mapAffineCoordinates C (x, y)).2 -
          (3 * (mapAffineCoordinates C (x, y)).1 ^ 2 +
            2 * W.a₂ * (mapAffineCoordinates C (x, y)).1 + W.a₄) = 0 ∧
        2 * (mapAffineCoordinates C (x, y)).2 + W.a₁ * (mapAffineCoordinates C (x, y)).1 +
          W.a₃ = 0) := by
  have hX := partialX_mapAffineCoordinates C W x y
  have hY := partialY_mapAffineCoordinates C W x y
  constructor
  · rintro ⟨hX', hY'⟩
    rw [hY', mul_zero] at hY
    rw [hX', mul_zero, hY, mul_zero, add_zero] at hX
    exact ⟨hX, hY⟩
  · rintro ⟨hX₀, hY₀⟩
    rw [hY₀] at hY
    rw [hX₀, hY₀, mul_zero, add_zero] at hX
    exact ⟨(mul_eq_zero.mp hX.symm).resolve_left (pow_ne_zero 4 C.u.ne_zero),
      (mul_eq_zero.mp hY.symm).resolve_left (pow_ne_zero 3 C.u.ne_zero)⟩

/-- **Variable changes transform nonsingular points.** Let $W$ be a Weierstrass curve over a field
$F$, let $C = (u, r, s, t)$ be a variable change and let $C \cdot W$ be the transformed curve. A
pair $(x, y) \in F^2$ is a nonsingular point of $C \cdot W$ if and only if
$(u^2 x + r,\ u^3 y + u^2 s x + t)$ is a nonsingular point of $W$. -/
theorem nonsingular_mapAffineCoordinates_iff (xy : F × F) :
    (C • W).toAffine.Nonsingular xy.1 xy.2 ↔
      W.toAffine.Nonsingular (mapAffineCoordinates C xy).1 (mapAffineCoordinates C xy).2 := by
  rw [Affine.nonsingular_iff', Affine.nonsingular_iff', equation_mapAffineCoordinates_iff]
  refine and_congr_right fun _ => not_iff_not.mp ?_
  push Not
  exact partials_zero_iff C W xy.1 xy.2

private lemma fst_mapAffineCoordinates_injective {x₁ x₂ : F} (y₁ y₂ : F)
    (h : (mapAffineCoordinates C (x₁, y₁)).1 = (mapAffineCoordinates C (x₂, y₂)).1) :
    x₁ = x₂ := by
  simp only [mapAffineCoordinates] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 C.u.ne_zero) (by linear_combination h)

private lemma snd_mapAffineCoordinates_injective (x : F) {y₁ y₂ : F}
    (h : (mapAffineCoordinates C (x, y₁)).2 = (mapAffineCoordinates C (x, y₂)).2) :
    y₁ = y₂ := by
  simp only [mapAffineCoordinates] at h
  exact mul_left_cancel₀ (pow_ne_zero 3 C.u.ne_zero) (by linear_combination h)

private lemma negY_mapAffineCoordinates (x y : F) :
    W.toAffine.negY (mapAffineCoordinates C (x, y)).1 (mapAffineCoordinates C (x, y)).2 =
      (mapAffineCoordinates C (x, (C • W).toAffine.negY x y)).2 := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [Affine.negY, mapAffineCoordinates, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma yeq_mapAffineCoordinates_iff (x₁ x₂ y₁ y₂ : F) :
    ((mapAffineCoordinates C (x₁, y₁)).1 = (mapAffineCoordinates C (x₂, y₂)).1 ∧
        (mapAffineCoordinates C (x₁, y₁)).2 =
          W.toAffine.negY (mapAffineCoordinates C (x₂, y₂)).1
            (mapAffineCoordinates C (x₂, y₂)).2) ↔
      (x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂) := by
  constructor
  · rintro ⟨hx, hy⟩
    obtain rfl := fst_mapAffineCoordinates_injective C y₁ y₂ hx
    rw [negY_mapAffineCoordinates] at hy
    exact ⟨rfl, snd_mapAffineCoordinates_injective C x₁ hy⟩
  · rintro ⟨rfl, hy⟩
    exact ⟨rfl, by rw [negY_mapAffineCoordinates, hy]⟩

private lemma slope_mapAffineCoordinates [DecidableEq F] (x₁ x₂ y₁ y₂ : F)
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope (mapAffineCoordinates C (x₁, y₁)).1 (mapAffineCoordinates C (x₂, y₂)).1
        (mapAffineCoordinates C (x₁, y₁)).2 (mapAffineCoordinates C (x₂, y₂)).2 =
      (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (C • W).toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    obtain rfl := hx
    obtain rfl := (Affine.Y_eq_of_X_eq h₁ h₂ rfl).resolve_right hy
    have hyW : (mapAffineCoordinates C (x₁, y₁)).2 ≠
        W.toAffine.negY (mapAffineCoordinates C (x₁, y₁)).1
          (mapAffineCoordinates C (x₁, y₁)).2 :=
      fun h => hy ((yeq_mapAffineCoordinates_iff C W x₁ x₁ y₁ y₁).mp ⟨rfl, h⟩).2
    rw [Affine.slope_of_Y_ne rfl hyW, Affine.slope_of_Y_ne rfl hy]
    have hd : (mapAffineCoordinates C (x₁, y₁)).2 -
          W.toAffine.negY (mapAffineCoordinates C (x₁, y₁)).1
            (mapAffineCoordinates C (x₁, y₁)).2 =
        (C.u : F) ^ 3 * (y₁ - (C • W).toAffine.negY x₁ y₁) := by
      rw [negY_mapAffineCoordinates]
      simp only [mapAffineCoordinates]
      ring
    have hPYden : y₁ - (C • W).toAffine.negY x₁ y₁ =
        2 * y₁ + (C • W).a₁ * x₁ + (C • W).a₃ := by
      simp only [Affine.negY]
      ring
    have hn : 3 * (mapAffineCoordinates C (x₁, y₁)).1 ^ 2 +
          2 * W.a₂ * (mapAffineCoordinates C (x₁, y₁)).1 + W.a₄ -
          W.a₁ * (mapAffineCoordinates C (x₁, y₁)).2 =
        (C.u : F) ^ 4 * (3 * x₁ ^ 2 + 2 * (C • W).a₂ * x₁ + (C • W).a₄ - (C • W).a₁ * y₁) +
          C.s * ((C.u : F) ^ 3 * (y₁ - (C • W).toAffine.negY x₁ y₁)) := by
      have hX := partialX_mapAffineCoordinates C W x₁ y₁
      have hY := partialY_mapAffineCoordinates C W x₁ y₁
      rw [hPYden]
      linear_combination (-1 : F) * hX + C.s * hY
    have hden : y₁ - (C • W).toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero_of_ne hy
    rw [hd, hn]
    field_simp
  · have hxW : (mapAffineCoordinates C (x₁, y₁)).1 ≠ (mapAffineCoordinates C (x₂, y₂)).1 :=
      fun h => hx (fst_mapAffineCoordinates_injective C y₁ y₂ h)
    rw [Affine.slope_of_X_ne hxW, Affine.slope_of_X_ne hx]
    have hd : (mapAffineCoordinates C (x₁, y₁)).1 - (mapAffineCoordinates C (x₂, y₂)).1 =
        (C.u : F) ^ 2 * (x₁ - x₂) := by
      simp only [mapAffineCoordinates]
      ring
    have hn : (mapAffineCoordinates C (x₁, y₁)).2 - (mapAffineCoordinates C (x₂, y₂)).2 =
        (C.u : F) ^ 3 * (y₁ - y₂) + (C.u : F) ^ 2 * C.s * (x₁ - x₂) := by
      simp only [mapAffineCoordinates]
      ring
    have hxne : x₁ - x₂ ≠ 0 := sub_ne_zero_of_ne hx
    rw [hd, hn]
    field_simp

private lemma addX_mapAffineCoordinates (x₁ x₂ y₁ y₂ L : F) :
    W.toAffine.addX (mapAffineCoordinates C (x₁, y₁)).1 (mapAffineCoordinates C (x₂, y₂)).1
        ((C.u : F) * L + C.s) =
      (mapAffineCoordinates C
        ((C • W).toAffine.addX x₁ x₂ L, (C • W).toAffine.addY x₁ x₂ y₁ L)).1 := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [Affine.addX, mapAffineCoordinates, variableChange_a₁, variableChange_a₂,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma addY_mapAffineCoordinates (x₁ x₂ y₁ y₂ L : F) :
    W.toAffine.addY (mapAffineCoordinates C (x₁, y₁)).1 (mapAffineCoordinates C (x₂, y₂)).1
        (mapAffineCoordinates C (x₁, y₁)).2 ((C.u : F) * L + C.s) =
      (mapAffineCoordinates C
        ((C • W).toAffine.addX x₁ x₂ L, (C • W).toAffine.addY x₁ x₂ y₁ L)).2 := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, mapAffineCoordinates,
    variableChange_a₁, variableChange_a₂, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

end WeierstrassCurve.VariableChange

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] (C : VariableChange F) (W : WeierstrassCurve F)

open VariableChange

/-- The equivalence of points underlying `variableChangeAddEquiv`. -/
private def variableChangeEquivAux : (C • W).toAffine.Point ≃ W.toAffine.Point :=
  (C • W).toAffine.nonsingularPointEquiv.trans <|
    (Equiv.subtypeEquiv (q := fun xy : F × F => W.toAffine.Nonsingular xy.1 xy.2)
        (affineCoordinatesEquiv C) (nonsingular_mapAffineCoordinates_iff C W)).optionCongr.trans
      W.toAffine.nonsingularPointEquiv.symm

variable {C W}

private lemma variableChangeEquivAux_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    variableChangeEquivAux C W (.some x y h) =
      .some (mapAffineCoordinates C (x, y)).1 (mapAffineCoordinates C (x, y)).2
        ((nonsingular_mapAffineCoordinates_iff C W (x, y)).mp h) :=
  rfl

private lemma some_congr {W' : Affine F} {x₁ y₁ x₂ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx hy
  rfl

variable [DecidableEq F]

private theorem variableChangeEquivAux_add (P Q : (C • W).toAffine.Point) :
    variableChangeEquivAux C W (P + Q) =
      variableChangeEquivAux C W P + variableChangeEquivAux C W Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · have hxyW := (yeq_mapAffineCoordinates_iff C W x₁ x₂ y₁ y₂).mpr hxy
    rw [add_of_Y_eq hxy.1 hxy.2, variableChangeEquivAux_some, variableChangeEquivAux_some,
      add_of_Y_eq hxyW.1 hxyW.2]
    rfl
  · have hxyW := mt (yeq_mapAffineCoordinates_iff C W x₁ x₂ y₁ y₂).mp hxy
    have hslope := slope_mapAffineCoordinates C W x₁ x₂ y₁ y₂ h₁.1 h₂.1 hxy
    rw [add_some hxy, variableChangeEquivAux_some, variableChangeEquivAux_some,
      variableChangeEquivAux_some, add_some hxyW]
    exact some_congr (by rw [hslope, addX_mapAffineCoordinates])
      (by rw [hslope, addY_mapAffineCoordinates])

variable (C W) in
/-- **Variable changes give additive equivalences of points.** Let $W$ be a Weierstrass curve
over a field $F$, let $C = (u, r, s, t)$ be a variable change and let $C \cdot W$ be the
transformed curve. The map on points that fixes the point at infinity and sends an affine point
$(x, y)$ of $C \cdot W$ to $(u^2 x + r,\ u^3 y + u^2 s x + t)$ is an additive equivalence onto
the points of $W$; its inverse applies the coordinate map of $C^{-1}$. -/
@[no_expose] def variableChangeAddEquiv : (C • W).toAffine.Point ≃+ W.toAffine.Point where
  toEquiv := variableChangeEquivAux C W
  map_add' := variableChangeEquivAux_add

@[simp]
lemma variableChangeAddEquiv_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    variableChangeAddEquiv C W (.some x y h) =
      .some (mapAffineCoordinates C (x, y)).1 (mapAffineCoordinates C (x, y)).2
        ((nonsingular_mapAffineCoordinates_iff C W (x, y)).mp h) := by
  rfl

@[simp]
lemma variableChangeAddEquiv_symm_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    (variableChangeAddEquiv C W).symm (.some x y h) =
      .some (mapAffineCoordinates C⁻¹ (x, y)).1 (mapAffineCoordinates C⁻¹ (x, y)).2
        ((nonsingular_mapAffineCoordinates_iff C W _).mpr
          (by rw [mapAffineCoordinates_apply_inv]; exact h)) := by
  rfl

theorem variableChangeAddEquiv_toEquiv [W.IsElliptic] :
    (variableChangeAddEquiv C W).toEquiv = VariableChange.pointEquiv C W := by
  ext P
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

end WeierstrassCurve.Affine.Point
