/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
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
