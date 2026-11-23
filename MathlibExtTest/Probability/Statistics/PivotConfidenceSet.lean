/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.PivotConfidenceSet
public import MathlibExt.Probability.FiniteProbability
public import MathlibExt.Probability.Distributions.GaussianCdf

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.FiniteProbability
open MathlibExt.Probability.Statistics.PivotConfidenceSet

namespace MathlibExtTest.Probability.Statistics.PivotConfidenceSet

/-! ### The Gaussian location model `P θ = N(θ, 1)` with pivot `T x θ = x - θ` -/

/-- Under `N(θ, 1)` the location pivot `x - θ` is standard normal, for every `θ`
(`hasLaw_pivot_of_hasLaw_gaussianReal` with scale `1`). -/
theorem hasLaw_locationPivot (θ : ℝ) :
    HasLaw (fun x : ℝ => x - θ) (gaussianReal 0 1) (gaussianReal θ 1) := by
  have h := hasLaw_pivot_of_hasLaw_gaussianReal (T := id) (θ := θ) (s := 1) (v := 1)
    one_ne_zero (by simp) HasLaw.id
  simpa using h

/-- Parameter inversion in the location model: the pivot confidence set at the observation `x`
is the interval `[x - q_{1-α/2}, x - q_{α/2}]`, the existing `pivotInterval` with scale `1`.
Membership depends on `θ`. -/
theorem pivotConfidenceSet_location (ν : Measure ℝ) (α x : ℝ) :
    pivotConfidenceSet (fun x θ => x - θ) ν α x =
      pivotInterval x 1 (cdfQuantile ν (α / 2)) (cdfQuantile ν (1 - α / 2)) := by
  ext θ
  simp only [pivotConfidenceSet, pivotInterval, Set.mem_ofPred_eq, Set.mem_Icc, mul_one]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Coverage in the Gaussian location model.** With `P θ = N(θ, 1)`, the pivot `x - θ` and the
standard normal quantiles, the confidence set covers every `θ` with probability at least
`1 - α`. -/
theorem pivotConfidenceSet_coverage_location {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) (θ : ℝ) :
    1 - α ≤ (gaussianReal θ 1).real
      {x | θ ∈ pivotConfidenceSet (fun x θ => x - θ) (gaussianReal 0 1) α x} :=
  pivotConfidenceSet_coverage (fun θ => gaussianReal θ 1) (fun x θ => x - θ) (gaussianReal 0 1)
    (continuous_cdf_gaussianReal 0 (by norm_num : (1 : NNReal) ≠ 0))
    hasLaw_locationPivot (fun _ => by fun_prop) hα θ

/-- The same coverage, stated for the explicit interval `[x - q_{1-α/2}, x - q_{α/2}]` of
standard normal quantiles. -/
example {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) (θ : ℝ) :
    1 - α ≤ (gaussianReal θ 1).real {x | θ ∈ pivotInterval x 1
      (cdfQuantile (gaussianReal 0 1) (α / 2)) (cdfQuantile (gaussianReal 0 1) (1 - α / 2))} := by
  simpa only [pivotConfidenceSet_location] using pivotConfidenceSet_coverage_location hα θ

end MathlibExtTest.Probability.Statistics.PivotConfidenceSet
