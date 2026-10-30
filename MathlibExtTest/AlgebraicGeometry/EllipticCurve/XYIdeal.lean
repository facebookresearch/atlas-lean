/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.XYIdeal

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

/-- Smoke test of `XYIdeal_ne_bot`. -/
example {R : Type*} [CommRing R] [Nontrivial R] {W : Affine R} (x : R) (y : R[X]) :
    XYIdeal W x y ≠ ⊥ :=
  WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot x y
