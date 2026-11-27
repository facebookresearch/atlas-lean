/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Diffusion.JKOStep
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Diffusion.JKOScheme
open MathlibExt.Probability.Diffusion.JKOSchemeWanted
open scoped ENNReal

namespace MathlibExtTest.Probability.Diffusion.JKOStep

-- The zero potential on the line has no normalizable Gibbs distribution.
example {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) :
    ∃! ν : ProbabilityMeasure ℝ,
      IsJKOStep (fun _ => 0) β h (gaussianReal 0 1).toProbabilityMeasure ν := by
  have hμ : IsAdmissible (gaussianReal 0 1).toProbabilityMeasure := by
    refine ⟨gaussianReal_absolutelyContinuous 0 one_ne_zero, ?_⟩
    have hi := (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).integrable_sq
    have hf := hi.hasFiniteIntegral
    have hs (x : ℝ) : ENNReal.ofReal (x ^ 2) = ‖x‖ₑ ^ 2 := by
      rw [← sq_abs x, ENNReal.ofReal_pow (abs_nonneg x), ← Real.eNorm_eq_ofReal_abs]
    simpa only [hasFiniteIntegral_iff_eNorm, id_eq, Real.eNorm_eq_ofReal (sq_nonneg _), hs]
      using! hf
  exact existsUnique_isJKOStep contDiff_const (fun _ => le_rfl)
    ⟨0, fun _ => by simp⟩ hβ hh _ hμ

-- Uniqueness concerns the resulting law, even when the two proposed steps have different proofs.
example {ρ₀ μ ν : ProbabilityMeasure ℝ} (h₀ : IsAdmissible ρ₀)
    (hμ : IsJKOStep (fun _ => 0) 1 1 ρ₀ μ) (hν : IsJKOStep (fun _ => 0) 1 1 ρ₀ ν) :
    μ = ν :=
  (existsUnique_isJKOStep contDiff_const (fun _ => le_rfl) ⟨0, fun _ => by simp⟩
    zero_lt_one zero_lt_one ρ₀ h₀).unique hμ hν

end MathlibExtTest.Probability.Diffusion.JKOStep
