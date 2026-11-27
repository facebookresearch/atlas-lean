/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.RandomTranspositionUpper

open MathlibExt.Probability.MarkovMixing (tvDist)
open MathlibExt.Probability.RandomWalkFiniteGroup (randomTransposition uniform)
open MathlibExt.Probability.RandomWalkFiniteGroupWanted (diaconis_shahshahani_upper)
open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup (convPow)

-- A prescribed positive window of w*n extra steps suffices for the corresponding TV error,
-- without requiring that n*log(n)/2 + w*n be an integer.
example : ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) [NeZero n], 10 ≤ n → ∀ w : ℝ, 0 < w →
    n * Real.log n / 2 + w * n ≤ k →
    tvDist (convPow (randomTransposition n) k) (uniform _) ≤ C * Real.exp (-2 * w) := by
  obtain ⟨b, hb, h⟩ := diaconis_shahshahani_upper
  refine ⟨b / 2, by positivity, ?_⟩
  intro n k _ hn w hw hk
  have hn' : 0 < (n : ℝ) := by exact_mod_cast NeZero.pos n
  have htime : w ≤ ((k : ℝ) - n * Real.log n / 2) / n := (le_div_iff₀ hn').mpr (by linarith)
  have ht := h n k hn (hw.trans_le htime)
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left htime (by norm_num : (-2 : ℝ) ≤ 0))
  linarith [mul_le_mul_of_nonneg_left he hb.le]
