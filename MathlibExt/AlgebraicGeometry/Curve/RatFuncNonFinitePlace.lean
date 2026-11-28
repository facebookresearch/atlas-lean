/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_RationalFunctionField_
toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum.lean`
and
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_
toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum.lean`
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

public import Mathlib.NumberTheory.RatFunc.Ostrowski
public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaces
import MathlibExt.AlgebraicGeometry.Curve.AdicValuationRankOne
import MathlibExt.AlgebraicGeometry.Curve.AdicValuationTrivialOn

/-!
# Places of `K(x)` that are not finite

This file proves that a place of `RatFunc K` that is not attached to a prime of `K[X]` is the place
at infinity.

## Main statement

* `AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum`
-/

namespace AlgebraicCurve.RationalFunctionField

open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

/-- A place of `RatFunc K` that does not come from a prime of `K[X]` has the valuation ring of the
valuation at infinity. -/
public theorem toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
    {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K))
    (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w) :
    v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := by
  have := v.adicValuation_isRankOneDiscrete
  have := v.adicValuation_isTrivialOn
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)
  · obtain ⟨w, hw, -⟩ := h
    exact absurd (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))) (hv w)

end AlgebraicCurve.RationalFunctionField
