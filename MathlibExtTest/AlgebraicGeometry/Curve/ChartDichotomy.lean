/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.ChartDichotomy

@[expose] public section

universe u v

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

-- `exactSource` consumer with the original binders: a level, a valuation
-- subring of the (algebraically closed) base, and a place of the function
-- field; the conclusion is the two-chart alternative for the given element,
-- which for the modular function field is the `j`-invariant.
example [IsAlgClosed K] [Module.Finite K v.ResidueField]
    (A : ValuationSubring K) (j : F) :
    (∃ a : A, (j - algebraMap K F (a : K)) ∈ v.toValuationSubring.nonunits) ∨
      (∃ a : A, (j⁻¹ - algebraMap K F (a : K)) ∈ v.toValuationSubring.nonunits) :=
  v.chart_dichotomy A j

-- Higher-universe consumer.
example {K' F' : Type (max u v)} [Field K'] [Field F'] [Algebra K' F']
    (w : Place K' F') [IsAlgClosed K'] [Module.Finite K' w.ResidueField]
    (A : ValuationSubring K') (j : F') :
    (∃ a : A, (j - algebraMap K' F' (a : K')) ∈ w.toValuationSubring.nonunits) ∨
      (∃ a : A, (j⁻¹ - algebraMap K' F' (a : K')) ∈ w.toValuationSubring.nonunits) :=
  w.chart_dichotomy A j

-- Boundary: the inverse chart is needed when the element is outside the
-- valuation subring; then its inverse is a nonunit, witnessed by `0`.
example {j : F} (hj : j ∉ v.toValuationSubring) :
    (j⁻¹ - algebraMap K F (0 : K)) ∈ v.toValuationSubring.nonunits := by
  have hnu : j⁻¹ ∈ v.toValuationSubring.nonunits :=
    (ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by simpa using hj))
  simp only [map_zero, sub_zero]
  exact hnu

-- A constant element takes its own value in the left chart.
example (c : K) :
    v.HasValueAt (algebraMap K F c) c := by
  change algebraMap K F c - algebraMap K F c ∈ v.toValuationSubring.nonunits
  simp

end AlgebraicCurve
