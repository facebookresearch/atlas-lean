/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Haldane

@[expose] public section

open MeasureTheory Filter Topology Real ProbabilityTheory MathlibExt.Probability
open MathlibExt.Biology.PopulationGenetics.Haldane
open scoped NNReal

namespace MathlibExtTest.Biology.PopulationGenetics.Haldane

/-- The Poisson(`2`) generating function at `0` is `P(ξ = 0) = exp (-2)`. -/
example : pgf id (poissonMeasure 2) 0 = exp (-2) := by
  rw [pgf_poissonMeasure]
  norm_num

/-- The Poisson(`3`) law has mean `3`. -/
example : GaltonWatson.mean (poissonMeasure 3) = 3 := by
  simpa using mean_poissonMeasure 3

/-- A neutral mutant (`s = 0`, critical Poisson(`1`) offspring) is lost almost surely. -/
example : survivalProb 0 = 0 := by
  have h1 : poissonMeasure 1 {1} ≠ 1 := by
    rw [poissonMeasure_singleton]
    refine (ENNReal.ofReal_lt_one.2 ?_).ne
    simp
  have hq := (GaltonWatson.extinctionProb_eq_one_iff _ h1).2 (by rw [mean_poissonMeasure]; simp)
  rw [survivalProb, show (1 + (0 : ℝ)).toNNReal = 1 by simp, hq, sub_self]

/-- A beneficial mutant with `s = 1/10` survives with positive probability, less than `1`. -/
example : 0 < survivalProb (1 / 10) ∧ survivalProb (1 / 10) < 1 :=
  ⟨survivalProb_pos (by norm_num), survivalProb_lt_one _⟩

/-- A deleterious mutant (`s = -1/2`) has non-negative survival probability. -/
example : 0 ≤ survivalProb (-1 / 2) :=
  survivalProb_nonneg _

/-- Haldane's equation at `s = 1/10`. -/
example : 1 - survivalProb (1 / 10) = exp (-(1 + 1 / 10) * survivalProb (1 / 10)) :=
  one_sub_survivalProb (by norm_num)

/-- Haldane's `2 s`. -/
example : Tendsto (fun s => survivalProb s / s) (𝓝[>] 0) (𝓝 2) :=
  tendsto_survivalProb_div

/-- Junk value outside the model (`s < -1`): the Poisson mean `1 + s` is truncated to `0`, the
mutant leaves no copies, and the survival probability is `0`. -/
example : survivalProb (-2) = 0 := by
  have hq : GaltonWatson.extinctionProb (poissonMeasure 0) = 1 := by
    have h := (GaltonWatson.isLeast_extinctionProb (poissonMeasure 0)).1.2
    rw [pgf_poissonMeasure] at h
    simpa using h.symm
  rw [survivalProb, show (1 + (-2 : ℝ)).toNNReal = 0 by norm_num, hq, sub_self]

end MathlibExtTest.Biology.PopulationGenetics.Haldane
