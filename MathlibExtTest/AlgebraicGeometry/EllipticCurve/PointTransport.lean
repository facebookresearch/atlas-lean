/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicGeometry.EllipticCurve.PointTransport
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointTransport

open WeierstrassCurve

universe u v

variable {F : Type u} {k : Type v} [Field F] [Field k] [DecidableEq F]
  [DecidableEq k] (f : F →+* k) {W₀ : WeierstrassCurve F}

/-- Unfolding consumer: `mapPoint` on a `some` point applies `f` to
both coordinates. -/
example {x y : F} (h : W₀.toAffine.Nonsingular x y) :
    mapPoint f (.some x y h) =
      .some (f x) (f y)
        ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) :=
  mapPoint_some f h

/-- The induced group homomorphism preserves addition, scalar
multiplication, and additive order, with all hypotheses instantiated. -/
example (P Q : W₀.toAffine.Point) (n : ℕ) :
    mapPoint f (P + Q) = mapPoint f P + mapPoint f Q ∧
      mapPoint f (n • P) = n • mapPoint f P ∧
        addOrderOf (mapPoint f P) = addOrderOf P :=
  ⟨mapPoint_add f P Q, mapPoint_nsmul f n P, addOrderOf_mapPoint f P⟩

/-- The additive equivalence from an equality of curves is the
identity on the diagonal. -/
example (W : WeierstrassCurve F) :
    pointAddEquivOfEq (rfl : W = W) = AddEquiv.refl _ :=
  pointAddEquivOfEq_refl W

/-- The variable-change coordinate formulas are two-sided inverses,
and nonsingularity transports along them. -/
example {K : Type u} [Field K] (C : VariableChange K)
    (W : WeierstrassCurve K) (x y : K) :
    Affine.vcX C (Affine.vcXInv C x) = x ∧
      Affine.vcY C (Affine.vcXInv C x) (Affine.vcYInv C x y) = y ∧
        ((C • W).toAffine.Nonsingular x y ↔
          W.toAffine.Nonsingular (Affine.vcX C x) (Affine.vcY C x y)) :=
  ⟨Affine.vcX_vcXInv x, Affine.vcY_vcYInv x y,
    Affine.nonsingular_variableChange_iff x y⟩

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Translation by one in the affine `x` coordinate. -/
private def change5 : VariableChange (ZMod 5) :=
  ⟨1, 1, 0, 0⟩

/-- The test curve `y² = x³ + x` over `ZMod 5`. -/
private def curve5 : WeierstrassCurve (ZMod 5) :=
  ⟨0, 0, 0, 1, 0⟩

/-- A nontrivial instance of the variable-change point equivalence:
translation by `1` in the `x`-coordinate on `y² = x³ + x` over
`ZMod 5`, applied to the zero point and checked on coordinates. -/
example :
    Affine.Point.variableChangeEquiv change5 curve5 0 = 0 ∧
      Affine.vcX change5 1 = 2 ∧ Affine.vcY change5 1 0 = 0 :=
  ⟨rfl, rfl, rfl⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointTransport
