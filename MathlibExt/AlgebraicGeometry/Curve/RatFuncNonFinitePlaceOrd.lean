/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_RationalFunctionField_
ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum.lean`
and
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_
ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum.lean`
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

public import MathlibExt.AlgebraicGeometry.Curve.RatFuncNonFinitePlace
import MathlibExt.AlgebraicGeometry.Curve.OrdEqNegLog

/-!
# Order at a non-finite place of `K(x)`

This file proves that the order at a place of `RatFunc K` that is not attached to a prime of `K[X]`
is minus the degree.

## Main statement

* `AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum`
-/

namespace AlgebraicCurve.RationalFunctionField

open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

/-- At a place of `RatFunc K` that does not come from a prime of `K[X]`, the order of `f ≠ 0` is
`-f.intDegree`. -/
public theorem ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
    {K : Type*} [Field K] (v : Place K (RatFunc K))
    (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w)
    {f : RatFunc K} (hf : f ≠ 0) : v.ord f = -f.intDegree := by
  classical
  have hπ : RatFunc.inftyValuation K (RatFunc.X)⁻¹ = exp (-1 : ℤ) := by
    rw [map_inv₀, RatFunc.inftyValuation.X]
    exact (exp_neg (1 : ℤ)).symm
  rw [v.ord_eq_neg_log_of_valuationSubring_eq (RatFunc.inftyValuation K)
      (AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
        v hv).symm hπ hf,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, log_exp]

end AlgebraicCurve.RationalFunctionField
