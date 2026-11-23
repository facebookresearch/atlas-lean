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

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

-- `exactSource` consumer with the original binders.
example (hv : v.IsRational) (x : v.ResidueField) :
    algebraMap K v.ResidueField (v.residueInv x) = x :=
  v.algebraMap_residueInv hv x

example (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.evalAt f)
      = IsLocalRing.residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) :=
  v.algebraMap_evalAt hv hf

example (f : F) (D : Divisor K F) :
    Divisor.evalFun f D = ∏ w ∈ D.support, w.evalAt f ^ D w :=
  Divisor.evalFun_def f D

example (K F : Type*) [Field K] [Field F] [Algebra K F] :
    Prop :=
  WeilReciprocity K F

-- Boundary: evaluation at `1` is `1` with no rationality hypothesis, and an
-- element outside the valuation subring evaluates to `0` by definition.
example : v.evalAt (1 : F) = 1 := v.evalAt_one

example {f : F} (hf : f ∉ v.toValuationSubring) : v.evalAt f = 0 := by
  rw [Place.evalAt, dite_eq_right hf]

end AlgebraicCurve
