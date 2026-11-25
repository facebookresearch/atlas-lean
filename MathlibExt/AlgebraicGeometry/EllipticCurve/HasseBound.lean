/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
import MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
import MathlibExt.AlgebraicGeometry.EllipticCurve.VariableChangePoint

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.HasseBoundWanted

/-!
# Hasse bound for elliptic curves

Records Hasse's bound on the number of points of an elliptic curve over a finite field.
-/

/--
**Hasse bound.** Let $F$ be a finite field with $q$ elements and let $E$ be an elliptic curve over
$F$ given by a Weierstrass equation. If $N$ is the number of points of $E$ with coordinates in $F$,
including the point at infinity, then $(q + 1 - N)^2 \le 4q$ in $\mathbb{Z}$.

Proof: Manin's elementary polynomial-degree argument on a twist over the rational function field
$F(t)$, done separately for the odd-characteristic and characteristic-two normal forms. In
characteristic two the point count uses the fibres of the additive maps $y \mapsto y^2 + by$ with
$b \in F$, followed by the same projective neighboring-degree recurrence, as in
Chahal--Soomro--Top, *Rocky Mountain J. Math.* 44 (2014).

Proves `Wanted` entry `hasse_bound`.

Source: H. Hasse, J.
Reine Angew. Math. 1936; modern Silverman, The Arithmetic of Elliptic Curves, 2nd ed.;
Lean states integral squared form of |N-(q+1)| ≤ 2√q including point at infinity.
-/
public theorem hasse_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] :
    (((Nat.card F : ℤ) + 1 - (Nat.card (W.toAffine.Point) : ℤ)) ^ 2 ≤
      4 * (Nat.card F : ℤ)) := by
  open MathlibExt.AlgebraicGeometry.EllipticCurve in
  by_cases hchar : ringChar F = 2
  · let _ : CharP F 2 := ringChar.of_eq hchar
    obtain ⟨C, hC⟩ := W.exists_variableChange_isCharTwoNF
    let _ : (C • W).IsCharTwoNF := hC
    have hbound := ManinTwistCharTwo.hasse_bound_of_isCharTwoNF (C • W)
    simpa only [WeierstrassCurve.VariableChange.natCard_point_eq C W] using hbound
  · let _ : Invertible (2 : F) := invertibleOfNonzero (Ring.two_ne_zero hchar)
    obtain ⟨C, hC⟩ := W.exists_variableChange_isCharNeTwoNF
    let _ : (C • W).IsCharNeTwoNF := hC
    have hbound := ManinTwist.hasse_bound_of_isCharNeTwoNF (C • W)
    simpa only [WeierstrassCurve.VariableChange.natCard_point_eq C W] using hbound

end MathlibExt.AlgebraicGeometry.EllipticCurve.HasseBoundWanted
