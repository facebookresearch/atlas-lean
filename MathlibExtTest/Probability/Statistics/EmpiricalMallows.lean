/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.EmpiricalMallows
import MathlibExt.Probability.SampleEmpiricalMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Tests for empirical Mallows convergence
-/

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
open MathlibExt.Probability.SampleEmpiricalMeasure
open MathlibExt.Probability.Statistics.BootstrapWanted

namespace MathlibExtTest.Probability.Statistics.EmpiricalMallows

private noncomputable def normalLaw : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

/-- At the endpoint `p = 1`, take actual empirical measures of standard normal coordinates. -/
example : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1),
    Tendsto (fun n => wasserstein 1 (sampleEmpiricalMeasure ω (n + 1)) normalLaw)
      atTop (𝓝 0) := by
  have hcoord (i : ℕ) := measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i
  apply tendsto_wasserstein_empirical (X := fun i ω => ω i) le_rfl
    measurable_pi_apply (iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id)
    (fun i => (hcoord i).hasLaw.identDistrib (hcoord 0).hasLaw) normalLaw (hcoord 0).map_eq
  · have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by simp)).integrable le_rfl
    simpa [normalLaw] using hasFiniteIntegral_iff_eNorm.mp h.hasFiniteIntegral
  · exact fun n ω => toMeasure_sampleEmpiricalMeasure ω (Nat.succ_ne_zero n)

end MathlibExtTest.Probability.Statistics.EmpiricalMallows
