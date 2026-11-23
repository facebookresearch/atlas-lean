/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import MathlibExt.AlgebraicGeometry.EllipticCurve.GenusOnePlaceGateCentred

open WeierstrassCurve WeierstrassCurve.Affine

example {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [GenusOnePlaceGate W]
    [GenusOnePlaceGate.IsCentred W] {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  GenusOnePlaceGate.IsCentred.algebraMap_XClass_mem_nonunits h
