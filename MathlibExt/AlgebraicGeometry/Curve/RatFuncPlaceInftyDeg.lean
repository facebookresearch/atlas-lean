/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty.lean`
and
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_deg_placeInfty.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceClassification
import MathlibExt.AlgebraicGeometry.Curve.RatFuncNonFinitePlaceDeg

/-!
# The infinite place of `K(x)` has degree one

This file proves that the place at infinity of `RatFunc K` has degree one.

## Main statement

* `AlgebraicCurve.RationalFunctionField.deg_placeInfty`
-/

namespace CurveGenus.RatFuncPlaceInftyDeg

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

/-- The place at infinity of `RatFunc K` has degree one. -/
public theorem _root_.AlgebraicCurve.RationalFunctionField.deg_placeInfty (K : Type*) [Field K]
    [DecidableEq (RatFunc K)] : (placeInfty K).deg = 1 :=
  AlgebraicCurve.RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum (placeInfty K)
    (AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum K)

end RatFuncPlaceInftyDeg

end CurveGenus
