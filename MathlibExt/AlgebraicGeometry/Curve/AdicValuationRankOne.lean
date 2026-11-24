/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.lean`
and
`P2M/Sol/S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.lean`
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

public import MathlibExt.AlgebraicGeometry.Curve.Place

/-!
# The valuation of a place is discrete of rank one

This file proves that the normalized valuation of a place is discrete of rank one.

## Main statement

* `AlgebraicCurve.Place.adicValuation_isRankOneDiscrete`
-/

namespace CurveGenus.AdicValuationRankOne

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem rowMain : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.CurveGenus.AdicValuationRankOne.AlgebraicCurve in
/-- The normalized valuation of a place is discrete of rank one. -/
public theorem _root_.AlgebraicCurve.Place.adicValuation_isRankOneDiscrete {K F : Type*}
    [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsRankOneDiscrete :=
  AlgebraicCurve.Place.rowMain v

end AdicValuationRankOne

end CurveGenus
