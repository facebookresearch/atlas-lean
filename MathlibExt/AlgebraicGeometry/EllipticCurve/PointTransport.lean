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
import Mathlib.Tactic.FieldSimp

/-!
# Transport of affine Weierstrass points

This file transports nonsingular affine points of a Weierstrass curve
along three kinds of identification: a ring homomorphism between
fields (`mapPoint`, a group homomorphism), an equality of curves
(`pointAddEquivOfEq`, an additive equivalence), and an admissible
variable change (`Point.variableChangeEquiv`, an equivalence with an
explicit coordinate formula).
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

namespace WeierstrassCurve.Affine

universe u

variable {K : Type u} [Field K]

section Formulas

variable (C : VariableChange K) (W : WeierstrassCurve K)

/-- The `x`-coordinate after applying the variable change `C`:
`x = u²x' + r`. -/
def vcX (x' : K) : K :=
  (C.u : K) ^ 2 * x' + C.r

/-- The `y`-coordinate after applying the variable change `C`:
`y = u³y' + u²sx' + t`. -/
def vcY (x' y' : K) : K :=
  (C.u : K) ^ 3 * y' + (C.u : K) ^ 2 * C.s * x' + C.t

/-- The inverse `x`-coordinate formula for the variable change `C`. -/
def vcXInv (x : K) : K :=
  ((C.u⁻¹ : Kˣ) : K) ^ 2 * (x - C.r)

/-- The inverse `y`-coordinate formula for the variable change `C`. -/
def vcYInv (x y : K) : K :=
  ((C.u⁻¹ : Kˣ) : K) ^ 3 * (y - C.t - C.s * (x - C.r))

variable {C W}

private lemma u_ne_zero : (C.u : K) ≠ 0 :=
  C.u.ne_zero

private lemma u_pow_ne_zero (n : ℕ) : ((C.u : K)) ^ n ≠ 0 :=
  pow_ne_zero n C.u.ne_zero

@[simp]
lemma vcX_vcXInv (x : K) : vcX C (vcXInv C x) = x := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcXInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp]
lemma vcY_vcYInv (x y : K) : vcY C (vcXInv C x) (vcYInv C x y) = y := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcY, vcXInv, vcYInv, Units.val_inv_eq_inv_val]
  field_simp; ring

@[simp]
lemma vcXInv_vcX (x' : K) : vcXInv C (vcX C x') = x' := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcXInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp]
lemma vcYInv_vcY (x' y' : K) : vcYInv C (vcX C x') (vcY C x' y') = y' := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, vcYInv, Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma equation_aux (x' y' : K) :
    vcY C x' y' ^ 2 + W.a₁ * vcX C x' * vcY C x' y' + W.a₃ * vcY C x' y' -
      (vcX C x' ^ 3 + W.a₂ * vcX C x' ^ 2 + W.a₄ * vcX C x' + W.a₆)
    = (C.u : K) ^ 6 *
      (y' ^ 2 + (C • W).a₁ * x' * y' + (C • W).a₃ * y' -
        (x' ^ 3 + (C • W).a₂ * x' ^ 2 + (C • W).a₄ * x' + (C • W).a₆)) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆,
    Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma partialX_aux (x' y' : K) :
    W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄) +
      C.s * (2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃)
    = (C.u : K) ^ 4 *
      ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' +
        (C • W).a₄)) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂,
    variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma partialY_aux (x' y' : K) :
    2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃
      = (C.u : K) ^ 3 * (2 * y' + (C • W).a₁ * x' + (C • W).a₃) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp; ring

lemma equation_variableChange_iff (x' y' : K) :
    (C • W).toAffine.Equation x' y' ↔
      W.toAffine.Equation (vcX C x') (vcY C x' y') := by
  rw [Affine.equation_iff', Affine.equation_iff', equation_aux x' y',
    mul_eq_zero, or_iff_right (u_pow_ne_zero 6)]

private lemma partials_zero_iff (x' y' : K) :
    ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄) = 0
        ∧ 2 * y' + (C • W).a₁ * x' + (C • W).a₃ = 0)
      ↔ (W.a₁ * vcY C x' y' -
          (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄) = 0
        ∧ 2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃ = 0) := by
  constructor
  · rintro ⟨hX', hY'⟩
    have hY : 2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃ = 0 := by
      rw [partialY_aux x' y', hY', mul_zero]
    refine ⟨?_, hY⟩
    have hX := partialX_aux (C := C) (W := W) x' y'
    rw [hX', mul_zero, hY, mul_zero, add_zero] at hX
    exact hX
  · rintro ⟨hX, hY⟩
    have hY' : 2 * y' + (C • W).a₁ * x' + (C • W).a₃ = 0 := by
      have h := partialY_aux (C := C) (W := W) x' y'
      rw [hY] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (u_pow_ne_zero 3)
    refine ⟨?_, hY'⟩
    have h := partialX_aux (C := C) (W := W) x' y'
    rw [hX, hY, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (u_pow_ne_zero 4)

lemma nonsingular_variableChange_iff (x' y' : K) :
    (C • W).toAffine.Nonsingular x' y' ↔
      W.toAffine.Nonsingular (vcX C x') (vcY C x' y') := by
  rw [Affine.nonsingular_iff', Affine.nonsingular_iff',
    equation_variableChange_iff x' y']
  refine and_congr_right fun _ => not_iff_not.mp ?_
  push_neg
  exact partials_zero_iff x' y'

end Formulas

section PointEquiv

variable [DecidableEq K] (C : VariableChange K) (W : WeierstrassCurve K)

namespace Point

/-- The forward point map of a variable change, with the explicit
coordinate formulas `vcX` and `vcY`. -/
def vcFun : (C • W).toAffine.Point → W.toAffine.Point
  | 0 => 0
  | .some x' y' h => .some (vcX C x') (vcY C x' y')
      ((nonsingular_variableChange_iff x' y').mp h)

/-- The inverse point map of a variable change, with the explicit
coordinate formulas `vcXInv` and `vcYInv`. -/
def vcInvFun : W.toAffine.Point → (C • W).toAffine.Point
  | 0 => 0
  | .some x y h => .some (vcXInv C x) (vcYInv C x y)
      ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv]))

variable {C W}

@[simp]
lemma vcFun_zero : vcFun C W 0 = 0 :=
  rfl

@[simp]
lemma vcInvFun_zero : vcInvFun C W 0 = 0 :=
  rfl

lemma vcFun_some {x' y' : K} (h : (C • W).toAffine.Nonsingular x' y') :
    vcFun C W (.some x' y' h) =
      .some (vcX C x') (vcY C x' y')
        ((nonsingular_variableChange_iff x' y').mp h) :=
  rfl

lemma vcInvFun_some {x y : K} (h : W.toAffine.Nonsingular x y) :
    vcInvFun C W (.some x y h) =
      .some (vcXInv C x) (vcYInv C x y)
        ((nonsingular_variableChange_iff (vcXInv C x)
          (vcYInv C x y)).mpr (by rwa [vcX_vcXInv, vcY_vcYInv])) :=
  rfl

private lemma some_eq_some {W' : WeierstrassCurve.Affine K}
    {x₁ y₁ x₂ y₂ : K} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

lemma vcFun_leftInverse :
    Function.LeftInverse (vcInvFun C W) (vcFun C W) := by
  rintro (_ | ⟨x', y', h⟩)
  · rfl
  · simp only [vcFun, vcInvFun]
    exact some_eq_some (vcXInv_vcX x') (vcYInv_vcY x' y')

lemma vcFun_rightInverse :
    Function.RightInverse (vcInvFun C W) (vcFun C W) := by
  rintro (_ | ⟨x, y, h⟩)
  · rfl
  · simp only [vcFun, vcInvFun]
    exact some_eq_some (vcX_vcXInv x) (vcY_vcYInv x y)

variable (C W) in
/-- The equivalence on nonsingular affine points induced by an
admissible variable change, with explicit coordinate formulas in both
directions. -/
noncomputable def variableChangeEquiv :
    (C • W).toAffine.Point ≃ W.toAffine.Point :=
  ⟨vcFun C W, vcInvFun C W, vcFun_leftInverse, vcFun_rightInverse⟩

/-- The equivalence on points induced by a variable change that is
equal to a given curve `V`. -/
noncomputable def equivOfVariableChangeEq {V : WeierstrassCurve K}
    (h : C • W = V) : V.toAffine.Point ≃ W.toAffine.Point := by
  subst h; exact variableChangeEquiv C W

end Point

end PointEquiv

end WeierstrassCurve.Affine
