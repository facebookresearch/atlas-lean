/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_WeierstrassCurve_MapPoint.lean`,
`Definitions/Def_WeierstrassCurve_PointAddEquivOfEq.lean`
and
`Definitions/Def_WeierstrassCurve_VariableChangePointEquiv.lean`
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
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import MathlibExt.AlgebraicGeometry.EllipticCurve.VariableChangePoint
import Mathlib.Tactic.FieldSimp

/-!
# Transport of affine Weierstrass points

This file transports nonsingular affine points of a Weierstrass curve
along three kinds of identification: a ring homomorphism between
fields (`mapPoint`, a group homomorphism), an equality of curves
(`pointAddEquivOfEq`, an additive equivalence), and an admissible
variable change (`Point.variableChangeEquiv`, an equivalence with an
explicit coordinate formula).

The variable-change equivalence moves affine points by
`VariableChange.mapAffineCoordinates`; nonsingularity is transported by
`VariableChange.nonsingular_mapAffineCoordinates_iff`, so unlike
`VariableChange.pointEquiv` it needs no ellipticity hypothesis.
-/

@[expose] public section

namespace WeierstrassCurve

universe u v w

variable {F : Type u} {k : Type v} [Field F] [Field k] (f : F →+* k)
  {W₀ : WeierstrassCurve F}

private lemma Affine.Point.some_congr' {V : Affine k} {x₁ y₁ x₂ y₂ : k}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁)
    (h₂ : V.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

/-- The map on nonsingular affine points induced by a ring
homomorphism `f : F →+* k`, applying `f` to both coordinates. -/
def mapPoint : W₀.toAffine.Point → (W₀.map f).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h)

@[simp]
lemma mapPoint_zero : mapPoint f (0 : W₀.toAffine.Point) = 0 :=
  rfl

lemma mapPoint_some {x y : F} (h : W₀.toAffine.Nonsingular x y) :
    mapPoint f (.some x y h) =
      .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) :=
  rfl

lemma mapPoint_injective : Function.Injective (mapPoint f (W₀ := W₀)) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Affine.Point.some_ne_zero _)
  · exact absurd h (Affine.Point.some_ne_zero _)
  · rw [mapPoint_some, mapPoint_some, Affine.Point.some.injEq] at h
    exact Affine.Point.some_congr' (f.injective h.1) (f.injective h.2) _ _

theorem mapPoint_add [DecidableEq F] [DecidableEq k]
    (P Q : W₀.toAffine.Point) :
    mapPoint f (P + Q) = mapPoint f P + mapPoint f Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W₀.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, mapPoint_zero, mapPoint_some,
      mapPoint_some,
      Affine.Point.add_of_Y_eq (congrArg f hxy.1)
        (by rw [hxy.2, Affine.map_negY])]
  · have hxy' : ¬(f x₁ = f x₂ ∧
        f y₁ = (W₀.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hx, hy⟩
      rw [Affine.map_negY] at hy
      exact hxy ⟨f.injective hx, f.injective hy⟩
    rw [Affine.Point.add_some hxy, mapPoint_some, mapPoint_some,
      mapPoint_some, Affine.Point.add_some hxy']
    exact Affine.Point.some_congr'
      (by rw [Affine.map_slope, Affine.map_addX])
      (by rw [Affine.map_slope, Affine.map_addY]) _ _

/-- The group homomorphism on nonsingular affine points induced by a
ring homomorphism between fields. -/
@[simps]
def mapPointHom [DecidableEq F] [DecidableEq k] :
    W₀.toAffine.Point →+ (W₀.map f).toAffine.Point where
  toFun := mapPoint f
  map_zero' := rfl
  map_add' := mapPoint_add f

lemma mapPointHom_injective [DecidableEq F] [DecidableEq k] :
    Function.Injective (mapPointHom f (W₀ := W₀)) :=
  mapPoint_injective f

theorem addOrderOf_mapPoint [DecidableEq F] [DecidableEq k]
    (P : W₀.toAffine.Point) :
    addOrderOf (mapPoint f P) = addOrderOf P :=
  addOrderOf_injective (mapPointHom f (W₀ := W₀)) (mapPoint_injective f) P

theorem mapPoint_nsmul [DecidableEq F] [DecidableEq k] (n : ℕ)
    (P : W₀.toAffine.Point) :
    mapPoint f (n • P) = n • mapPoint f P :=
  map_nsmul (mapPointHom f (W₀ := W₀)) n P

theorem mapPoint_neg [DecidableEq F] [DecidableEq k]
    (P : W₀.toAffine.Point) :
    mapPoint f (-P) = -mapPoint f P :=
  map_neg (mapPointHom f (W₀ := W₀)) P

/-- The additive equivalence on affine points induced by an equality
of Weierstrass curves. -/
def pointAddEquivOfEq {L : Type w} [Field L] [DecidableEq L]
    {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point :=
  e ▸ AddEquiv.refl _

@[simp]
theorem pointAddEquivOfEq_refl {L : Type w} [Field L] [DecidableEq L]
    (W : WeierstrassCurve L) :
    pointAddEquivOfEq (rfl : W = W) = AddEquiv.refl _ :=
  rfl

theorem pointAddEquivOfEq_symm {L : Type w} [Field L] [DecidableEq L]
    {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) :
    (pointAddEquivOfEq e).symm = pointAddEquivOfEq e.symm := by
  subst e; rfl

theorem pointAddEquivOfEq_some {L : Type w} [Field L] [DecidableEq L]
    {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) {x y : L}
    (h : W₁.toAffine.Nonsingular x y) :
    pointAddEquivOfEq e (.some x y h) = .some x y (e ▸ h) := by
  subst e; rfl

end WeierstrassCurve

namespace WeierstrassCurve.VariableChange

universe u

variable {K : Type u} [Field K] (C : VariableChange K) (W : WeierstrassCurve K)

private lemma partialX_mapAffineCoordinates (xy : K × K) :
    W.a₁ * (mapAffineCoordinates C xy).2 -
        (3 * (mapAffineCoordinates C xy).1 ^ 2 +
          2 * W.a₂ * (mapAffineCoordinates C xy).1 + W.a₄) +
      C.s * (2 * (mapAffineCoordinates C xy).2 +
        W.a₁ * (mapAffineCoordinates C xy).1 + W.a₃) =
    (C.u : K) ^ 4 *
      ((C • W).a₁ * xy.2 - (3 * xy.1 ^ 2 + 2 * (C • W).a₂ * xy.1 + (C • W).a₄)) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [mapAffineCoordinates, variableChange_a₁, variableChange_a₂,
    variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma partialY_mapAffineCoordinates (xy : K × K) :
    2 * (mapAffineCoordinates C xy).2 + W.a₁ * (mapAffineCoordinates C xy).1 + W.a₃ =
      (C.u : K) ^ 3 * (2 * xy.2 + (C • W).a₁ * xy.1 + (C • W).a₃) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [mapAffineCoordinates, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma partials_zero_iff (xy : K × K) :
    ((C • W).a₁ * xy.2 - (3 * xy.1 ^ 2 + 2 * (C • W).a₂ * xy.1 + (C • W).a₄) = 0 ∧
        2 * xy.2 + (C • W).a₁ * xy.1 + (C • W).a₃ = 0) ↔
      (W.a₁ * (mapAffineCoordinates C xy).2 -
          (3 * (mapAffineCoordinates C xy).1 ^ 2 +
            2 * W.a₂ * (mapAffineCoordinates C xy).1 + W.a₄) = 0 ∧
        2 * (mapAffineCoordinates C xy).2 + W.a₁ * (mapAffineCoordinates C xy).1 +
          W.a₃ = 0) := by
  have hX := partialX_mapAffineCoordinates C W xy
  have hY := partialY_mapAffineCoordinates C W xy
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

theorem nonsingular_mapAffineCoordinates_iff (xy : K × K) :
    (C • W).toAffine.Nonsingular xy.1 xy.2 ↔
      W.toAffine.Nonsingular (mapAffineCoordinates C xy).1 (mapAffineCoordinates C xy).2 := by
  rw [Affine.nonsingular_iff', Affine.nonsingular_iff', equation_mapAffineCoordinates_iff]
  refine and_congr_right fun _ => not_iff_not.mp ?_
  push Not
  exact partials_zero_iff C W xy

end WeierstrassCurve.VariableChange

namespace WeierstrassCurve.Affine.Point

universe u

variable {K : Type u} [Field K] (C : VariableChange K) (W : WeierstrassCurve K)

open VariableChange

/-- The equivalence on nonsingular affine points induced by an
admissible variable change `C`: it fixes the point at infinity and moves
an affine point by `VariableChange.mapAffineCoordinates C`, with inverse
`mapAffineCoordinates C⁻¹`. -/
noncomputable def variableChangeEquiv :
    (C • W).toAffine.Point ≃ W.toAffine.Point :=
  (C • W).toAffine.nonsingularPointEquiv.trans <|
    (Equiv.subtypeEquiv (q := fun xy : K × K => W.toAffine.Nonsingular xy.1 xy.2)
        (affineCoordinatesEquiv C) (nonsingular_mapAffineCoordinates_iff C W)).optionCongr.trans
      W.toAffine.nonsingularPointEquiv.symm

variable {C W}

@[simp]
lemma variableChangeEquiv_zero : variableChangeEquiv C W 0 = 0 :=
  rfl

@[simp]
lemma variableChangeEquiv_some {x y : K} (h : (C • W).toAffine.Nonsingular x y) :
    variableChangeEquiv C W (.some x y h) =
      .some (mapAffineCoordinates C (x, y)).1 (mapAffineCoordinates C (x, y)).2
        ((nonsingular_mapAffineCoordinates_iff C W (x, y)).mp h) :=
  rfl

@[simp]
lemma variableChangeEquiv_symm_zero : (variableChangeEquiv C W).symm 0 = 0 :=
  rfl

@[simp]
lemma variableChangeEquiv_symm_some {x y : K} (h : W.toAffine.Nonsingular x y) :
    (variableChangeEquiv C W).symm (.some x y h) =
      .some (mapAffineCoordinates C⁻¹ (x, y)).1 (mapAffineCoordinates C⁻¹ (x, y)).2
        ((nonsingular_mapAffineCoordinates_iff C W _).mpr
          (by rw [mapAffineCoordinates_apply_inv]; exact h)) :=
  rfl

/-- The equivalence on points induced by a variable change that is
equal to a given curve `V`. -/
noncomputable def equivOfVariableChangeEq {V : WeierstrassCurve K}
    (h : C • W = V) : V.toAffine.Point ≃ W.toAffine.Point := by
  subst h; exact variableChangeEquiv C W

end WeierstrassCurve.Affine.Point
