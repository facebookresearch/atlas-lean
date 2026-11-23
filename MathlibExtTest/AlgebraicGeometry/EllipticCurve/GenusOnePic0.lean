/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import MathlibExt.AlgebraicGeometry.EllipticCurve.GenusOnePic0

open WeierstrassCurve WeierstrassCurve.Affine

example {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [GenusOnePlaceGate W]
    (P : W.Point) : (placeOfPoint (W := W) P).deg = 1 :=
  deg_placeOfPoint P

example {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [GenusOnePlaceGate W]
    [AbelTheorem W] (P : W.Point) : pic0ToPoint (pointClass P) = P :=
  pic0ToPoint_pointClass P
