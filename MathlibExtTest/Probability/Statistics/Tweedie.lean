/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Tweedie

/-!
# Tests for Tweedie's formula

A point-mass prior (posterior mean `0` and posterior variance `0`, so Tweedie's two formulas give
the first two derivatives of `log f`); the normal–normal prior `N(0, 1)` with unit noise
(posterior mean `x / 2`); and the conditional expectation form for the prior `N(0, 1)`, which has
a finite first moment, so that its hypotheses are jointly satisfiable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Statistics.Tweedie

/-- A point mass at `0` has posterior mean `0`. -/
example (x : ℝ) : gaussianPosteriorMean (Measure.dirac 0) 1 x = 0 := by
  simp [gaussianPosteriorMean]

/-- Tweedie's formula for a point mass at `0` gives `(log f)'(x) = -x` with unit variance. -/
example (x : ℝ) :
    deriv (fun y => Real.log (gaussianMixtureDensity (Measure.dirac 0) 1 y)) x = -x := by
  have h := gaussianPosteriorMean_eq_add_mul_deriv_log (Measure.dirac (0 : ℝ)) (v := 1) x
  have h0 : gaussianPosteriorMean (Measure.dirac 0) 1 x = 0 := by
    simp [gaussianPosteriorMean]
  rw [h0] at h
  simp only [NNReal.coe_one, one_mul] at h
  linarith

/-- For a point mass the posterior variance vanishes, so `(log f)''(x) = -1` with unit variance. -/
example (x : ℝ) :
    deriv (deriv fun y => Real.log (gaussianMixtureDensity (Measure.dirac 0) 1 y)) x = -1 := by
  have h := gaussianPosteriorSecondMoment_sub_sq_eq (Measure.dirac (0 : ℝ)) (v := 1) x
  have h0 : gaussianPosteriorSecondMoment (Measure.dirac 0) 1 x -
      gaussianPosteriorMean (Measure.dirac 0) 1 x ^ 2 = 0 := by
    simp [gaussianPosteriorSecondMoment, gaussianPosteriorMean]
  rw [h0] at h
  simp only [NNReal.coe_one, one_mul] at h
  linarith

/-- Normal–normal shrinkage: prior `N(0, 1)` and unit noise give `E[μ | x] = x / 2`. -/
example (x : ℝ) : gaussianPosteriorMean (gaussianReal 0 1) 1 x = x / 2 := by
  rw [gaussianPosteriorMean_gaussianReal 1 (v := 1) x]
  norm_num
  ring

/-- The joint law of the normal–normal model is a probability measure. -/
example : IsProbabilityMeasure (gaussianLocationJoint (gaussianReal 0 1) 1) := inferInstance

/-- The conditional expectation form applies to the prior `N(0, 1)`. -/
example : (fun q : ℝ × ℝ => gaussianPosteriorMean (gaussianReal 0 1) 1 q.2)
    =ᵐ[gaussianLocationJoint (gaussianReal 0 1) 1]
      (gaussianLocationJoint (gaussianReal 0 1) 1)[Prod.fst |
        MeasurableSpace.comap Prod.snd inferInstance] :=
  condExp_fst_gaussianLocationJoint (gaussianReal 0 1)
    ((memLp_id_gaussianReal 1).integrable le_rfl)

/-! The variance must be positive: for `v = 0`, for which the Gaussian density vanishes
identically and the posterior mean would be `0` instead of `x`, the posterior mean does not
elaborate. -/

/--
error: failed to synthesize instance of type class
  NeZero 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example : ℝ := gaussianPosteriorMean (Measure.dirac 1) 0 1

end MathlibExtTest.Probability.Statistics.Tweedie
