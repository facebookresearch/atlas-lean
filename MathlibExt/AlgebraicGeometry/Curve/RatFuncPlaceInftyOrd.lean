/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty.lean`
and
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_placeInfty.lean`
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
import MathlibExt.AlgebraicGeometry.Curve.RatFuncNonFinitePlaceOrd

/-!
# Order at the infinite place of `K(x)`

This file proves that the order of `f ≠ 0` at the place at infinity of `RatFunc K` is
`-f.intDegree`.

## Main statement

* `AlgebraicCurve.RationalFunctionField.ord_placeInfty`
-/

namespace CurveGenus.RatFuncPlaceInftyOrd

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

/-- The order of `f ≠ 0` at the place at infinity of `RatFunc K` is `-f.intDegree`. -/
public theorem _root_.AlgebraicCurve.RationalFunctionField.ord_placeInfty {K : Type*} [Field K]
    [DecidableEq (RatFunc K)] {f : RatFunc K} (hf : f ≠ 0) :
    (placeInfty K).ord f = -f.intDegree :=
  AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
      (placeInfty K)
    (AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum K) hf

end RatFuncPlaceInftyOrd

end CurveGenus
