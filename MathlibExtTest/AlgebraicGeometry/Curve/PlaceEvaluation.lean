/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluation

@[expose] public section

namespace AlgebraicCurve

-- `exactSource` consumer with the original binders.
example {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 :=
  v.ord_algebraMap c

-- Universe check: the base and function fields may live in different universes.
universe u w in
example {K : Type u} {F : Type w} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 :=
  v.ord_algebraMap c

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

-- Evaluation is the identity on constants and sends `1` to `1`.
example (a : K) : v.evalAt (algebraMap K F a) = a := v.evalAt_algebraMap a

example : v.evalAt (1 : F) = 1 := v.evalAt_one

-- Boundary: outside the valuation subring the evaluation is the junk value `0`.
example {f : F} (hf : f ∉ v.toValuationSubring) : v.evalAt f = 0 := by
  simp [Place.evalAt, hf]

end AlgebraicCurve
