/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianCdf
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Tests for continuity of the Gaussian cdf

Standard use at the standard normal, the degenerate zero-variance Gaussian
(a Dirac mass by `gaussianReal_zero_var`) showing the nonzero-variance
hypothesis cannot be dropped, and the singleton-null round trip through the
continuity iff.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.GaussianCdf

/-- Use: the standard normal cdf is continuous. -/
example : Continuous (cdf (gaussianReal 0 1)) := by
  exact continuous_cdf_gaussianReal 0 one_ne_zero

/-- Boundary: the zero-variance Gaussian cdf is not continuous, so `hv` cannot be dropped. -/
example : ¬ Continuous (cdf (gaussianReal 0 0)) := by
  rw [gaussianReal_zero_var]
  intro h
  have h0 : ContinuousAt (cdf (Measure.dirac (0 : ℝ))) 0 := h.continuousAt
  rw [MathlibExt.Probability.CdfContinuityPoints.continuousAt_cdf_iff_measure_singleton_eq_zero] at h0
  have h1 : Measure.dirac (0 : ℝ) {(0 : ℝ)} = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_singleton _)
  rw [h1] at h0
  exact one_ne_zero h0

/-- Use: a Gaussian with nonzero variance has no atoms (round trip through the iff). -/
example (μ : ℝ) {v : NNReal} (hv : v ≠ 0) (x : ℝ) :
    (gaussianReal μ v) {x} = 0 := by
  have h := continuous_cdf_gaussianReal μ hv
  have hx : ContinuousAt (cdf (gaussianReal μ v)) x := h.continuousAt
  rw [MathlibExt.Probability.CdfContinuityPoints.continuousAt_cdf_iff_measure_singleton_eq_zero] at hx
  exact hx

end MathlibExt.Probability.GaussianCdf
