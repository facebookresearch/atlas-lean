/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.UniformlyContinuousIntegrableTendstoZero
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq

/-! # Tests for uniform decay of integrable functions on the real line -/

open Filter Topology Real MeasureTheory
open MathlibExt.Analysis.Calculus.UniformlyContinuousIntegrableTendstoZeroWanted

-- The function x exp(-a x²) is nonzero on both tails, with opposite signs.
example {a : ℝ} (ha : 0 < a) :
    Tendsto (mulExpNegMulSq a) atBot (𝓝 0) ∧ Tendsto (mulExpNegMulSq a) atTop (𝓝 0) := by
  have hint : Integrable (fun x ↦ mulExpNegMulSq a x) := by
    simpa only [mulExpNegMulSq, pow_two, mul_assoc, neg_mul] using
      integrable_mul_exp_neg_mul_sq ha
  have h := UniformContinuous.tendsto_cocompact_zero_of_integrable (mulExpNegMulSq a)
    (lipschitzWith_one_mulExpNegMulSq ha).uniformContinuous hint
  exact ⟨h.mono_left tendsto_abs_atBot_atTop.le_comap,
    h.mono_left tendsto_abs_atTop_atTop.le_comap⟩
