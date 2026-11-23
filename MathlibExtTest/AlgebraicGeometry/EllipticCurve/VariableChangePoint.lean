/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicGeometry.EllipticCurve.VariableChangePoint
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The test curve `y² = x³ + x` over `ZMod 5`. -/
private def curve : WeierstrassCurve (ZMod 5) :=
  ⟨0, 0, 0, 1, 0⟩

private instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, isUnit_iff_ne_zero]
  decide

/-- Translation by one in the affine `x` coordinate. -/
private def change : VariableChange (ZMod 5) :=
  ⟨1, 1, 0, 0⟩

set_option maxHeartbeats 400000 in
-- Elaborating both concrete point types needs more than the default deterministic budget.
/-- A nontrivial translation preserves the number of points of a concrete curve over `ZMod 5`. -/
example : Nat.card ((change • curve).toAffine.Point) = Nat.card curve.toAffine.Point :=
  VariableChange.natCard_point_eq change curve

/-- `exactSource` consumer with the original binders. -/
example {K : Type*} [Field K] [DecidableEq K]
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve.Affine K)
    (P Q : W.Point) :
    WeierstrassCurve.Affine.Point.vcInvFun C W (P + Q) =
      WeierstrassCurve.Affine.Point.vcInvFun C W P +
        WeierstrassCurve.Affine.Point.vcInvFun C W Q :=
  WeierstrassCurve.Affine.Point.vcInvFun_add P Q

/-- The inverse variable change fixes the point at infinity, so the hypothesis
that a point is affine is essential for coordinate formulae: at infinity
there are no coordinates to transform. -/
example {K : Type*} [Field K] [DecidableEq K]
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve.Affine K) :
    WeierstrassCurve.Affine.Point.vcInvFun C W (0 : W.Point) = 0 :=
  WeierstrassCurve.Affine.Point.vcInvFun_zero

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
