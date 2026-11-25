/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.GenusOnePlaceGateCentred

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [GenusOnePlaceGate W]
  [GenusOnePlaceGate.IsCentred W]

example {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  GenusOnePlaceGate.IsCentred.algebraMap_XClass_mem_nonunits h

example {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  GenusOnePlaceGate.IsCentred.algebraMap_YClass_mem_nonunits h

/-- A centred gate is given by the two conditions at every affine point. -/
example
    (hX : ∀ (x y : F) (h : W.Nonsingular x y),
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
        ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits)
    (hY : ∀ (x y : F) (h : W.Nonsingular x y),
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
        ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits) :
    GenusOnePlaceGate.IsCentred W :=
  ⟨hX, hY⟩

/-- At the place attached to an affine point `(x, y)`, the function `X - x` lies in the valuation
subring: it is a non-unit there. -/
example {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring :=
  ValuationSubring.mem_of_valuation_le_one _ _ (le_of_lt ((ValuationSubring.mem_nonunits_iff _).mp
    (GenusOnePlaceGate.IsCentred.algebraMap_XClass_mem_nonunits h)))
