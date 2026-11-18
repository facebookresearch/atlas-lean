/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Instrumentation.ApertureJitterBudget

@[expose] public section

open MeasureTheory Set
open scoped Convolution NNReal
open MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp
open PhyslibExt.Instrumentation.ApertureJitterBudget

namespace PhyslibExtTest.Instrumentation.ApertureJitterBudget

/-- The width-one box kernel (supported on `[-1/2, 1/2]`) is an aperture kernel. -/
example : IsApertureKernel (1 : ℝ) (boxKernel (1 : ℝ)) :=
  boxKernel_isApertureKernel (by norm_num)

/-- The width-one box kernel acquires a constant signal exactly. -/
private lemma box_const (a t : ℝ) :
    (boxKernel 1 ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun _ => a) t = a :=
  convolution_const_of_isApertureKernel (boxKernel_isApertureKernel one_pos) a t

/-- Clipping boundary for step `1` and codes `0..7`: `29 / 4` lies above the full-scale
interval `[0, 7]` but still rounds to code `7`, while `15 / 2` rounds to `8` and is
clipped. -/
example : ¬ IsClipped 1 0 7 (29 / 4) ∧ IsClipped 1 0 7 (15 / 2) := by
  refine ⟨?_, ?_⟩ <;> norm_num [IsClipped, round_eq, Int.floor_eq_iff]

/-- Headline budget at the clipping boundary: the constant signal `29 / 4` (Lipschitz
constant `0`), sample period `1`, jitter `1 / 20` within `J = 1 / 10`, the width-one box
aperture, and a step-`1` ADC with codes `0..7`. The input is outside the full-scale interval,
so only the no-clipping form applies; every sample meets the `Δ / 2` budget. -/
example (k : ℤ) :
    |quantize 1 0 7 ((boxKernel 1 ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun _ => (29 / 4 : ℝ)) ((k : ℝ) * 1 + 1 / 20)) - 29 / 4| ≤
      ((0 : ℝ≥0) : ℝ) * (1 / 10) + ((0 : ℝ≥0) : ℝ) * (1 / 2) + 1 / 2 := by
  refine abs_quantize_sampled_sub_le (x := fun _ => (29 / 4 : ℝ)) (fun _ => 1 / 20) one_pos
    (boxKernel_isApertureKernel one_pos) (fun _ => ?_)
    (fun _ => (LipschitzWith.const _).lipschitzOnWith) (fun _ => ?_) k
  · rw [abs_of_pos (by norm_num)]
    norm_num
  · rw [box_const]
    norm_num [IsClipped, round_eq, Int.floor_eq_iff]

/-- Full-scale budget at the top endpoint: the constant signal `7 = Δ * kmax` with the same
sampling, aperture and ADC lies in the full-scale interval `[0, 7]`. -/
example (k : ℤ) :
    |quantize 1 0 7 ((boxKernel 1 ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun _ => (7 : ℝ)) ((k : ℝ) * 1 + 1 / 20)) - 7| ≤
      ((0 : ℝ≥0) : ℝ) * (1 / 10) + ((0 : ℝ≥0) : ℝ) * (1 / 2) + 1 / 2 := by
  refine abs_quantize_sampled_sub_le_of_mem_Icc (x := fun _ => (7 : ℝ)) (fun _ => 1 / 20)
    one_pos (boxKernel_isApertureKernel one_pos) (fun _ => ?_)
    (fun _ => (LipschitzWith.const _).lipschitzOnWith) (fun _ => ?_) k
  · rw [abs_of_pos (by norm_num)]
    norm_num
  · rw [box_const]
    norm_num

/-- Calibrated budget: the physical signal `3 / 2` seen through the scale `c = 2` (the ADC
input is `3`), jitter `1 / 20` within `J = 1 / 10`, the width-one box aperture, and a step-`1`
ADC with codes `0..7`; dividing by `c` recovers `3 / 2` within `Δ / (2 |c|) = 1 / 4`. -/
example (t₀ : ℝ) :
    |quantize 1 0 7 ((boxKernel 1 ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun _ => (2 : ℝ) * (3 / 2)) (t₀ + 1 / 20)) / 2 - 3 / 2| ≤
      ((0 : ℝ≥0) : ℝ) * (1 / 10 + 1 / 2) + 1 / (2 * |(2 : ℝ)|) := by
  refine abs_quantize_div_calibration_sub_le (s := fun _ => (3 / 2 : ℝ)) (J := 1 / 10)
    two_ne_zero one_pos (boxKernel_isApertureKernel one_pos) ?_
    (LipschitzWith.const _).lipschitzOnWith ?_
  · rw [abs_of_pos (by norm_num)]
    norm_num
  · show ¬ IsClipped 1 0 7 ((boxKernel 1 ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun _ => (2 : ℝ) * (3 / 2)) (t₀ + 1 / 20))
    rw [box_const]
    norm_num [IsClipped, round_eq, Int.floor_eq_iff]

end PhyslibExtTest.Instrumentation.ApertureJitterBudget
