/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.NyquistShannon
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Tests for the Nyquist–Shannon sampling theorem

The hypothesis is satisfiable by a nonzero Schwartz function: the inverse Fourier transform of a
smooth bump supported in `(-1/2, 1/2)`.
-/

open scoped FourierTransform SchwartzMap ContDiff
open Set MathlibExt.Analysis.Fourier.NyquistShannon

namespace MathlibExtTest.Analysis.Fourier.NyquistShannon

/-- A smooth bump equal to `1` on `[-1/4, 1/4]` and supported in `(-1/2, 1/2)`. -/
noncomputable def bump : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The bump as a complex Schwartz function. -/
noncomputable def bumpSchwartz : 𝓢(ℝ, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x : ℝ => ((bump x : ℝ) : ℂ))
    (bump.hasCompactSupport.comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp bump.contDiff)

/-- A nonzero band-limited Schwartz function exists, so the sampling theorem is not vacuous. -/
theorem exists_bandLimited :
    ∃ f : 𝓢(ℝ, ℂ), f ≠ 0 ∧ ∀ ξ : ℝ, ξ ∉ Icc (-(1 / 2 : ℝ)) (1 / 2) → 𝓕 f ξ = 0 := by
  have h1 : 𝓕 (𝓕⁻ bumpSchwartz) = bumpSchwartz :=
    FourierTransform.fourier_fourierInv_eq bumpSchwartz
  refine ⟨𝓕⁻ bumpSchwartz, fun h => ?_, fun ξ hξ => ?_⟩
  · have h2 := congrArg (fun g : 𝓢(ℝ, ℂ) => g 0) h1
    simp only [h] at h2
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq] at h2
    change _ = ((bump 0 : ℝ) : ℂ) at h2
    rw [bump.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [bump]))] at h2
    simp at h2
  · rw [h1]
    change ((bump ξ : ℝ) : ℂ) = 0
    rw [Complex.ofReal_eq_zero]
    apply bump.zero_of_le_dist
    simp only [Real.dist_eq, sub_zero, bump]
    simp only [mem_Icc, not_and_or, not_le] at hξ
    rcases hξ with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

/-- The sampling theorem applied to that function at `t = 1/3`. -/
example : ∃ f : 𝓢(ℝ, ℂ), f ≠ 0 ∧
    f (1 / 3) = ∑' n : ℤ, f (n : ℝ) * (Real.sinc (Real.pi * ((n : ℝ) - 1 / 3)) : ℂ) := by
  obtain ⟨f, hf0, hf⟩ := exists_bandLimited
  exact ⟨f, hf0, (nyquist_shannon_sampling f hf (1 / 3)).2⟩

/-- Applying the Fourier transform twice reflects. -/
example (f : 𝓢(ℝ, ℂ)) : 𝓕 (𝓕 f) 2 = f (-2) := fourier_fourier_apply f 2

end MathlibExtTest.Analysis.Fourier.NyquistShannon
