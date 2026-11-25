/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.ConvexSubGaussianComparisonFiniteness

/-! # Tests for `MathlibExt.Probability.ConvexSubGaussianComparisonFiniteness` -/

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.ConvexSubGaussianComparison
open MathlibExt.Probability.ConvexSubGaussianComparisonWanted

namespace MathlibExtTest.Probability.ConvexSubGaussianComparisonFiniteness

-- The theorem, as stated.
example : comparisonConstant ≠ ⊤ :=
  historicalFinitenessUpperBound

/-- Finiteness means that some admissible variance factor exists. -/
private theorem exists_isAdmissibleConstant : ∃ C : ENNReal, IsAdmissibleConstant C :=
  not_forall_not.mp fun h => historicalFinitenessUpperBound (comparisonConstant_eq_top_iff.mpr h)

-- With the lower bound `1 ≤ comparisonConstant`, the constant is a real number at least `1`.
example : 1 ≤ comparisonConstant.toReal := by
  simpa using ENNReal.toReal_mono historicalFinitenessUpperBound one_le_comparisonConstant

/-- The standard Gaussian has a 1-sub-Gaussian tail. -/
private theorem standardGaussian_tail :
    IsOneSubGaussianTail (gaussianReal 0 1) (fun x : ℝ => x) := by
  have hmgf : HasSubgaussianMGF (fun x : ℝ => x) 1 (gaussianReal 0 1) := by
    refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
    simp [mgf_fun_id_gaussianReal]
  exact IsOneSubGaussianTail.of_hasSubgaussianMGF measurable_id hmgf (by simp)

-- A nondegenerate instance: the standard Gaussian is convexly dominated by some scaled Gaussian
-- `c G` with `c > 0`.
example : ∃ c : ℝ, 0 < c ∧
    ConvexDominated (gaussianReal 0 1) (fun x : ℝ => x) (gaussianReal 0 1)
      (fun g : ℝ => c * g) := by
  obtain ⟨C, hC⟩ := exists_isAdmissibleConstant
  refine ⟨Real.sqrt C.toReal, Real.sqrt_pos.mpr (ENNReal.toReal_pos hC.2.1.ne' hC.1), ?_⟩
  exact hC.elim (gaussianReal 0 1) (fun x : ℝ => x) standardGaussian_tail

-- A degenerate instance on a sample space in another universe: the zero variable.
example : ∃ c : ℝ, ConvexDominated (Measure.dirac (ULift.up 0 : ULift.{1} ℝ))
    (fun _ => (0 : ℝ)) (gaussianReal 0 1) (fun g : ℝ => c * g) := by
  obtain ⟨C, hC⟩ := exists_isAdmissibleConstant
  exact ⟨_, hC.elim _ _ (IsOneSubGaussianTail.zero _)⟩

end MathlibExtTest.Probability.ConvexSubGaussianComparisonFiniteness
