/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_WeierstrassCurve_GenusOnePlaceGateCentred.lean`
`Definitions/Def_WeierstrassCurve_GenusOnePic0.lean`
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

public import MathlibExt.AlgebraicGeometry.EllipticCurve.GenusOnePic0

@[expose] public section

/-!
# Centred genus-one place gate

A genus-one place gate `GenusOnePlaceGate W` carries an arbitrary bijection from the points of an
affine Weierstrass curve `W` to the places of its function field. This file adds the condition
`GenusOnePlaceGate.IsCentred` that ties the bijection to the geometry of `W`: each affine point
`(x, y)` goes to a place at which `X - x` and `Y - y` have positive order, that is, to the place
centred at `(x, y)`.
-/

set_option autoImplicit false

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F]

variable (W : Affine F) in
/-- **Centred place gate.** The bijection of `GenusOnePlaceGate W` sends each affine point `(x, y)`
to a place centred at it: the images of `X - x` and `Y - y` in the function field are non-units of
the valuation subring of the place, so both functions have positive order there. -/
class GenusOnePlaceGate.IsCentred [GenusOnePlaceGate W] : Prop where
  XClass_mem_nonunits : ∀ (x y : F) (h : W.Nonsingular x y),
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits
  YClass_mem_nonunits : ∀ (x y : F) (h : W.Nonsingular x y),
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits

namespace GenusOnePlaceGate.IsCentred

variable {W : Affine F} [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]

theorem algebraMap_XClass_mem_nonunits {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  XClass_mem_nonunits x y h

theorem algebraMap_YClass_mem_nonunits {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  YClass_mem_nonunits x y h

end GenusOnePlaceGate.IsCentred

end WeierstrassCurve.Affine
