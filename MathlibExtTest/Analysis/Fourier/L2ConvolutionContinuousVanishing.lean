/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.L2ConvolutionContinuousVanishing
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-! # Tests for `MathlibExt.Analysis.Fourier.L2ConvolutionContinuousVanishing` -/

namespace MathlibExtTest.Analysis.Fourier.L2ConvolutionContinuousVanishing

open MeasureTheory Filter Topology ZeroAtInfty
open MathlibExt.Analysis.Fourier.L2ConvolutionContinuousVanishingWanted

-- The zero function is square-integrable, so the theorem applies to it.
example (n : ℕ) (g : (Fin n → ℝ) → ℂ) (hg : MemLp g 2 volume) :
    Continuous (fun x : Fin n → ℝ ↦ ∫ y, (0 : (Fin n → ℝ) → ℂ) (x - y) * g y) ∧
      Tendsto (fun x : Fin n → ℝ ↦ ∫ y, (0 : (Fin n → ℝ) → ℂ) (x - y) * g y)
        (cocompact (Fin n → ℝ)) (𝓝 0) :=
  continuous_and_tendsto_cocompact_convolution_of_memLp_two n 0 g MemLp.zero hg

-- Consistently, the convolution of the zero function with any `g` vanishes identically.
example (n : ℕ) (g : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    ∫ y, (0 : (Fin n → ℝ) → ℂ) (x - y) * g y = 0 := by
  simp

-- The self-convolution of the indicator of the unit cube `[0, 1]ⁿ`, which has finite measure, is
-- continuous and vanishes at infinity.
example (n : ℕ) :
    Continuous (fun x : Fin n → ℝ ↦ ∫ y, (Set.Icc 0 1).indicator (fun _ ↦ (1 : ℂ)) (x - y) *
        (Set.Icc 0 1).indicator (fun _ ↦ (1 : ℂ)) y) ∧
      Tendsto (fun x : Fin n → ℝ ↦ ∫ y, (Set.Icc 0 1).indicator (fun _ ↦ (1 : ℂ)) (x - y) *
          (Set.Icc 0 1).indicator (fun _ ↦ (1 : ℂ)) y)
        (cocompact (Fin n → ℝ)) (𝓝 0) := by
  have h : MemLp ((Set.Icc (0 : Fin n → ℝ) 1).indicator fun _ ↦ (1 : ℂ)) 2 volume :=
    memLp_indicator_const 2 measurableSet_Icc.nullMeasurableSet 1
      (Or.inr isCompact_Icc.measure_lt_top.ne)
  exact continuous_and_tendsto_cocompact_convolution_of_memLp_two n _ _ h h

-- In dimension `0` the space is a point: `cocompact` is `⊥` there, so the limit is trivial, and
-- the theorem still gives continuity.
example : cocompact (Fin 0 → ℝ) = ⊥ :=
  cocompact_eq_bot

example (f g : (Fin 0 → ℝ) → ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Continuous (fun x : Fin 0 → ℝ ↦ ∫ y, f (x - y) * g y) :=
  (continuous_and_tendsto_cocompact_convolution_of_memLp_two 0 f g hf hg).1

-- The convolution is a continuous function vanishing at infinity, hence bounded.
example (n : ℕ) (f g : (Fin n → ℝ) → ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∃ C, ∀ x : Fin n → ℝ, ‖∫ y, f (x - y) * g y‖ ≤ C := by
  obtain ⟨hc, ht⟩ := continuous_and_tendsto_cocompact_convolution_of_memLp_two n f g hf hg
  let F : C₀(Fin n → ℝ, ℂ) := ⟨⟨_, hc⟩, ht⟩
  obtain ⟨C, hC⟩ := F.isBounded_range.exists_norm_le
  exact ⟨C, fun x ↦ hC _ ⟨x, rfl⟩⟩

-- Along the points `k • v`, `k : ℕ`, for a nonzero `v`, the convolution tends to `0`.
example (n : ℕ) (f g : (Fin n → ℝ) → ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (v : Fin n → ℝ) (hv : v ≠ 0) :
    Tendsto (fun k : ℕ ↦ ∫ y, f ((k : ℝ) • v - y) * g y) atTop (𝓝 0) := by
  refine (continuous_and_tendsto_cocompact_convolution_of_memLp_two n f g hf hg).2.comp ?_
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  simp only [norm_smul, Real.norm_natCast]
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (norm_pos_iff.2 hv)

end MathlibExtTest.Analysis.Fourier.L2ConvolutionContinuousVanishing
