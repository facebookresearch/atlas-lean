/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.YoungConvolutionSharp
import Mathlib.Tactic.NormNum

/-! # Endpoint tests for sharpness of Young's convolution inequality -/

open MeasureTheory Convolution
open MathlibExt.Analysis.FunctionalAnalysis.YoungConvolutionSharpWanted

-- The bound is strict at the smallest allowed exponent.
example :
    ∃ f g : ℝ → ℝ, MemLp f 1 ∧ MemLp g 1 ∧
      (eLpNorm (f ⋆ g) 1).toReal >
        (9 / 10 : ℝ) * (eLpNorm f 1).toReal * (eLpNorm g 1).toReal := by
  simpa only [show (1 : ℝ) - 1 / 10 = 9 / 10 by norm_num] using
    exists_eLpNorm_convolution_gt_one_sub_mul 1 le_rfl (1 / 10) (by norm_num)

-- The same factor holds for the essential supremum norm.
example :
    ∃ f g : ℝ → ℝ, MemLp f 1 ∧ MemLp g ⊤ ∧
      (eLpNorm (f ⋆ g) ⊤).toReal >
        (9 / 10 : ℝ) * (eLpNorm f 1).toReal * (eLpNorm g ⊤).toReal := by
  simpa only [show (1 : ℝ) - 1 / 10 = 9 / 10 by norm_num] using
    exists_eLpNorm_convolution_gt_one_sub_mul ⊤ le_top (1 / 10) (by norm_num)

-- At tolerance one, the conclusion still demands a positive convolution norm.
example :
    ∃ f g : ℝ → ℝ, MemLp f 1 ∧ MemLp g 2 ∧ 0 < (eLpNorm (f ⋆ g) 2).toReal := by
  simpa only [sub_self, zero_mul] using
    exists_eLpNorm_convolution_gt_one_sub_mul 2 (by norm_num) 1 zero_lt_one
