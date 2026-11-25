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

This file transports affine solutions and rational points along an admissible variable change.
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

end WeierstrassCurve.VariableChange

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K]

section Formulas

variable (C : VariableChange K) (W : WeierstrassCurve.Affine K)

/-- The `x`-coordinate obtained by applying a variable change. -/
def vcX (x' : K) : K :=
  (C.u : K) ^ 2 * x' + C.r

/-- The `y`-coordinate obtained by applying a variable change. -/
def vcY (x' y' : K) : K :=
  (C.u : K) ^ 3 * y' + (C.u : K) ^ 2 * C.s * x' + C.t

/-- The `x`-coordinate obtained by applying the inverse variable change. -/
def vcXInv (x : K) : K :=
  ((C.u⁻¹ : Kˣ) : K) ^ 2 * (x - C.r)

/-- The `y`-coordinate obtained by applying the inverse variable change. -/
def vcYInv (x y : K) : K :=
  ((C.u⁻¹ : Kˣ) : K) ^ 3 * (y - C.t - C.s * (x - C.r))

variable {C W}

private lemma vcAdd_u_ne_zero : (C.u : K) ≠ 0 :=
  C.u.ne_zero

private lemma vcAdd_u_pow_ne_zero (n : ℕ) : ((C.u : K)) ^ n ≠ 0 :=
  pow_ne_zero n C.u.ne_zero

@[simp]
private lemma vcX_vcXInv (x : K) : vcX C (vcXInv C x) = x := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcX, vcXInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp]
private lemma vcY_vcYInv (x y : K) : vcY C (vcXInv C x) (vcYInv C x y) = y := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcY, vcXInv, vcYInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp]
private lemma vcXInv_vcX (x' : K) : vcXInv C (vcX C x') = x' := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcX, vcXInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp]
private lemma vcYInv_vcY (x' y' : K) : vcYInv C (vcX C x') (vcY C x' y') = y' := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcX, vcY, vcYInv, Units.val_inv_eq_inv_val]; field_simp; ring

private lemma equation_aux (x' y' : K) :
    vcY C x' y' ^ 2 + W.a₁ * vcX C x' * vcY C x' y' + W.a₃ * vcY C x' y'
        - (vcX C x' ^ 3 + W.a₂ * vcX C x' ^ 2 + W.a₄ * vcX C x' + W.a₆)
      = (C.u : K) ^ 6 *
        (y' ^ 2 + (C • W).a₁ * x' * y' + (C • W).a₃ * y'
          - (x' ^ 3 + (C • W).a₂ * x' ^ 2 + (C • W).a₄ * x' + (C • W).a₆)) := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma partialX_aux (x' y' : K) :
    W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄)
        + C.s * (2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃)
      = (C.u : K) ^ 4 *
        ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄)) := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma partialY_aux (x' y' : K) :
    2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃
      = (C.u : K) ^ 3 * (2 * y' + (C • W).a₁ * x' + (C • W).a₃) := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp; ring

/-- A pair satisfies the transformed Weierstrass equation if and only if its
image under the variable change satisfies the original equation. -/
theorem equation_variableChange_iff (x' y' : K) :
    (C • W).toAffine.Equation x' y' ↔ W.Equation (vcX C x') (vcY C x' y') := by
  rw [equation_iff', equation_iff', equation_aux x' y', mul_eq_zero,
    or_iff_right (vcAdd_u_pow_ne_zero 6)]

private lemma partials_zero_iff (x' y' : K) :
    ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄) = 0
        ∧ 2 * y' + (C • W).a₁ * x' + (C • W).a₃ = 0)
      ↔ (W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄) = 0
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
      exact (mul_eq_zero.mp h.symm).resolve_left (vcAdd_u_pow_ne_zero 3)
    refine ⟨?_, hY'⟩
    have h := partialX_aux (C := C) (W := W) x' y'
    rw [hX, hY, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (vcAdd_u_pow_ne_zero 4)

/-- A pair is nonsingular for the transformed curve if and only if its image
under the variable change is nonsingular for the original curve. -/
theorem nonsingular_variableChange_iff (x' y' : K) :
    (C • W).toAffine.Nonsingular x' y' ↔ W.Nonsingular (vcX C x') (vcY C x' y') := by
  rw [nonsingular_iff', nonsingular_iff', equation_variableChange_iff x' y']
  refine and_congr_right fun _ => not_iff_not.mp ?_
  push Not
  exact partials_zero_iff x' y'

private lemma vcX_injective : Function.Injective (vcX C) := by
  intro a b h
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcX] at h
  have h' : (C.u : K) ^ 2 * a = (C.u : K) ^ 2 * b := by linear_combination h
  exact mul_left_cancel₀ (pow_ne_zero 2 hu) h'

private lemma vcY_injective (x' : K) : Function.Injective (vcY C x') := by
  intro a b h
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcY] at h
  have h' : (C.u : K) ^ 3 * a = (C.u : K) ^ 3 * b := by linear_combination h
  exact mul_left_cancel₀ (pow_ne_zero 3 hu) h'

private lemma negY_variableChange (x' y' : K) :
    W.negY (vcX C x') (vcY C x' y') = vcY C x' ((C • W).toAffine.negY x' y') := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [negY, vcX, vcY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma yeq_variableChange_iff (x₁' x₂' y₁' y₂' : K) :
    (vcX C x₁' = vcX C x₂' ∧ vcY C x₁' y₁' = W.negY (vcX C x₂') (vcY C x₂' y₂'))
      ↔ (x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂') := by
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : x₁' = x₂' := vcX_injective hx
    subst hx'
    refine ⟨rfl, ?_⟩
    rw [negY_variableChange x₁' y₂'] at hy
    exact vcY_injective x₁' hy
  · rintro ⟨hx, hy⟩
    subst hx
    exact ⟨rfl, by rw [negY_variableChange x₁' y₂', hy]⟩

private lemma slope_variableChange [DecidableEq K] (x₁' x₂' y₁' y₂' : K)
    (h₁ : (C • W).toAffine.Equation x₁' y₁') (h₂ : (C • W).toAffine.Equation x₂' y₂')
    (hxy : ¬(x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂')) :
    W.slope (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') (vcY C x₂' y₂')
      = (C.u : K) * (C • W).toAffine.slope x₁' x₂' y₁' y₂' + C.s := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  by_cases hx : x₁' = x₂'
  · have hy : y₁' ≠ (C • W).toAffine.negY x₂' y₂' := fun h => hxy ⟨hx, h⟩
    have hyy : y₁' = y₂' := (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy
    subst hx
    subst hyy
    have hyW : vcY C x₁' y₁' ≠ W.negY (vcX C x₁') (vcY C x₁' y₁') := by
      intro h
      exact hy ((yeq_variableChange_iff x₁' x₁' y₁' y₁').mp ⟨rfl, h⟩).2
    rw [slope_of_Y_ne rfl hyW, slope_of_Y_ne rfl hy]
    have hd : vcY C x₁' y₁' - W.negY (vcX C x₁') (vcY C x₁' y₁')
        = (C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁') := by
      rw [negY_variableChange x₁' y₁']
      simp only [vcY]
      ring
    have hPYden : y₁' - (C • W).toAffine.negY x₁' y₁'
        = 2 * y₁' + (C • W).a₁ * x₁' + (C • W).a₃ := by
      simp only [negY]
      ring
    have hn : 3 * vcX C x₁' ^ 2 + 2 * W.a₂ * vcX C x₁' + W.a₄ - W.a₁ * vcY C x₁' y₁'
        = (C.u : K) ^ 4 * (3 * x₁' ^ 2 + 2 * (C • W).a₂ * x₁'
            + (C • W).a₄ - (C • W).a₁ * y₁')
          + C.s * ((C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁')) := by
      have hX := partialX_aux (C := C) (W := W) x₁' y₁'
      have hY := partialY_aux (C := C) (W := W) x₁' y₁'
      rw [hPYden]
      linear_combination (-1 : K) * hX + C.s * hY
    have hden' : y₁' - (C • W).toAffine.negY x₁' y₁' ≠ 0 := sub_ne_zero_of_ne hy
    rw [hd, hn]
    field_simp
  · have hxW : vcX C x₁' ≠ vcX C x₂' := fun h => hx (vcX_injective h)
    rw [slope_of_X_ne hxW, slope_of_X_ne hx]
    have hd : vcX C x₁' - vcX C x₂' = (C.u : K) ^ 2 * (x₁' - x₂') := by
      simp only [vcX]; ring
    have hn : vcY C x₁' y₁' - vcY C x₂' y₂'
        = (C.u : K) ^ 3 * (y₁' - y₂') + (C.u : K) ^ 2 * C.s * (x₁' - x₂') := by
      simp only [vcY]; ring
    rw [hd, hn]
    have hxne : x₁' - x₂' ≠ 0 := sub_ne_zero_of_ne hx
    field_simp

private lemma addX_variableChange (x₁' x₂' L : K) :
    W.addX (vcX C x₁') (vcX C x₂') ((C.u : K) * L + C.s)
      = vcX C ((C • W).toAffine.addX x₁' x₂' L) := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [addX, vcX, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma addY_variableChange (x₁' x₂' y₁' L : K) :
    W.addY (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') ((C.u : K) * L + C.s)
      = vcY C ((C • W).toAffine.addX x₁' x₂' L)
        ((C • W).toAffine.addY x₁' x₂' y₁' L) := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [addY, negAddY, addX, negY, vcX, vcY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

end Formulas

section PointEquiv

variable (C : VariableChange K) (W : WeierstrassCurve.Affine K)

namespace Point

/-- The point of `W` obtained from a point of the transformed curve by
applying the variable change to its coordinates. -/
def vcFun : (C • W).toAffine.Point → W.Point
  | .zero => .zero
  | .some x' y' h => .some (vcX C x') (vcY C x' y')
      ((nonsingular_variableChange_iff x' y').mp h)

/-- The point of the transformed curve obtained from a point of `W` by
applying the inverse variable change to its coordinates. -/
def vcInvFun : W.Point → (C • W).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (vcXInv C x) (vcYInv C x y)
      ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv]))

variable {C W}

@[simp]
lemma vcFun_zero : vcFun C W 0 = 0 := rfl

@[simp]
lemma vcInvFun_zero : vcInvFun C W 0 = 0 := rfl

private lemma some_eq_some {W' : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

lemma vcFun_leftInverse : Function.LeftInverse (vcInvFun C W) (vcFun C W) := by
  rintro (_ | ⟨x', y', h⟩)
  · rfl
  · simp only [vcFun, vcInvFun]
    exact some_eq_some (vcXInv_vcX x') (vcYInv_vcY x' y')

lemma vcFun_rightInverse : Function.RightInverse (vcInvFun C W) (vcFun C W) := by
  rintro (_ | ⟨x, y, h⟩)
  · rfl
  · simp only [vcFun, vcInvFun]
    exact some_eq_some (vcX_vcXInv x) (vcY_vcYInv x y)

variable [DecidableEq K]

/-- Applying a variable change to coordinates preserves addition of points. -/
theorem vcFun_add (P Q : (C • W).toAffine.Point) :
    vcFun C W (P + Q) = vcFun C W P + vcFun C W Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · rw [add_of_Y_eq hxy.1 hxy.2, vcFun_zero]
    change (0 : W.Point) = Point.some (vcX C x₁) (vcY C x₁ y₁) _ +
      Point.some (vcX C x₂) (vcY C x₂ y₂) _
    have hxyW := (yeq_variableChange_iff (W := W) x₁ x₂ y₁ y₂).mpr hxy
    exact (add_of_Y_eq hxyW.1 hxyW.2).symm
  · have hxyW : ¬(vcX C x₁ = vcX C x₂ ∧
        vcY C x₁ y₁ = W.negY (vcX C x₂) (vcY C x₂ y₂)) :=
      fun h => hxy ((yeq_variableChange_iff x₁ x₂ y₁ y₂).mp h)
    have hslope := slope_variableChange (W := W) x₁ x₂ y₁ y₂ h₁.1 h₂.1 hxy
    rw [add_some hxy]
    change Point.some _ _ _ = Point.some (vcX C x₁) (vcY C x₁ y₁) _ +
      Point.some (vcX C x₂) (vcY C x₂ y₂) _
    rw [add_some hxyW]
    refine some_eq_some ?_ ?_
    · rw [hslope, addX_variableChange]
    · rw [hslope, addY_variableChange]

variable (C W) in
/-- The additive equivalence between points of the transformed curve and points
of the original curve induced by a variable change: it applies the variable change
to the coordinates of affine points and fixes the point at infinity. -/
def variableChangeAddEquiv : (C • W).toAffine.Point ≃+ W.Point where
  toFun := vcFun C W
  invFun := vcInvFun C W
  left_inv := vcFun_leftInverse
  right_inv := vcFun_rightInverse
  map_add' := vcFun_add

@[simp]
lemma variableChangeAddEquiv_apply (P : (C • W).toAffine.Point) :
    variableChangeAddEquiv C W P = vcFun C W P :=
  rfl

@[simp]
lemma variableChangeAddEquiv_symm_apply (P : W.Point) :
    (variableChangeAddEquiv C W).symm P = vcInvFun C W P :=
  rfl

/-- Applying the inverse variable change to coordinates preserves addition
of points. -/
public theorem vcInvFun_add (P Q : W.Point) :
    vcInvFun C W (P + Q) = vcInvFun C W P + vcInvFun C W Q :=
  (variableChangeAddEquiv C W).symm.map_add P Q

end Point

end PointEquiv

end WeierstrassCurve.Affine
