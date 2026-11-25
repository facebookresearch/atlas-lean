/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.SchwarzPickDerivBound

/-!
# Tests for the Schwarz–Pick derivative bound
-/

open Metric MathlibExt.Analysis.Complex.SchwarzPickDerivBoundWanted

-- At the origin the derivative bound still depends on the image of the origin.
example (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hm : Set.MapsTo f (ball 0 1) (ball 0 1)) :
    ‖deriv f 0‖ ≤ 1 - ‖f 0‖ ^ 2 := by
  have h₀ : (0 : ℂ) ∈ ball 0 1 := by simp
  have hpos : 0 < 1 - ‖f 0‖ ^ 2 :=
    sub_pos.mpr (pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp (hm h₀)) two_ne_zero)
  have h := norm_deriv_div_one_sub_sq_le_of_mapsTo_unitBall f hf hm 0 h₀
  simpa [div_le_iff₀ hpos] using h

-- A single holomorphic self-map attains equality at every point of the disc.
example : ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) ∧ Set.MapsTo f (ball 0 1) (ball 0 1) ∧
    ∀ z ∈ ball 0 1, ‖deriv f z‖ / (1 - ‖f z‖ ^ 2) = 1 / (1 - ‖z‖ ^ 2) := by
  exact ⟨id, differentiableOn_id, Set.mapsTo_id _, fun z _ => by simp⟩
