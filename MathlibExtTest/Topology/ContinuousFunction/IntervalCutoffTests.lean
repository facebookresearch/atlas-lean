/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ContinuousFunction.IntervalCutoff

/-!
# Tests of the shared interval cutoff through its sole import

The cutoff can be used without either the `L^p` or Weyl development. Check
its bounds, continuity, endpoints, zero width, exterior and positive plateau.
-/

namespace MathlibExtTest.Topology.ContinuousFunction.IntervalCutoffTests

example (a b δ x : ℝ) : 0 ≤ Real.intervalCutoff a b δ x :=
  Real.intervalCutoff_nonneg a b δ x

example (a b δ x : ℝ) : Real.intervalCutoff a b δ x ≤ 1 :=
  Real.intervalCutoff_le_one a b δ x

example (a b δ : ℝ) : Continuous (Real.intervalCutoff a b δ) :=
  Real.intervalCutoff_continuous a b δ

example (a b δ : ℝ) : Real.intervalCutoff a b δ a = 0 :=
  Real.intervalCutoff_eq_zero_left a b δ

example (a b δ : ℝ) : Real.intervalCutoff a b δ b = 0 :=
  Real.intervalCutoff_eq_zero_right a b δ

example (a b x : ℝ) : Real.intervalCutoff a b 0 x = 0 :=
  Real.intervalCutoff_zero_width a b x

example (a b δ x : ℝ) (hδ : 0 < δ) (hx : x ≤ a) :
    Real.intervalCutoff a b δ x = 0 :=
  Real.intervalCutoff_eq_zero_of_le a b δ x hδ hx

example (a b δ x : ℝ) (hδ : 0 < δ) (hx : b ≤ x) :
    Real.intervalCutoff a b δ x = 0 :=
  Real.intervalCutoff_eq_zero_of_ge a b δ x hδ hx

example (a b δ x : ℝ) (hδ : 0 < δ) (hx1 : a + δ ≤ x) (hx2 : x ≤ b - δ) :
    Real.intervalCutoff a b δ x = 1 :=
  Real.intervalCutoff_eq_one a b δ x hδ hx1 hx2

-- The positive-width plateau remains valid when it consists of a single point.
example : Real.intervalCutoff (-1) 1 1 0 = 1 := by
  apply Real.intervalCutoff_eq_one (-1) 1 1 0 zero_lt_one
  · simpa only [neg_add_cancel] using (le_refl (0 : ℝ))
  · simpa only [sub_self] using (le_refl (0 : ℝ))

end MathlibExtTest.Topology.ContinuousFunction.IntervalCutoffTests
