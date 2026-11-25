/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Control.FeedbackCapability
import Mathlib.Tactic.NormNum

open Set MeasureTheory

-- At the critical radius, even feedback cancelling the latest output fails for some
-- admissible plant and noise, here with a nonzero initial value and a small noise bound.
example :
    ∃ f : ℝ → ℝ, (∀ L' > 3 / 2 + √2, ∃ a : ℝ,
      ∀ x x', |f x - f x'| ≤ L' * (|x - x'| + a)) ∧
      ∃ w : ℕ → ℝ, (∀ t, |w t| ≤ 1 / 100) ∧
      ∃ y : ℕ → ℝ, y 0 = -3 ∧
        (∀ t, y (t + 1) = f (y t) - y t + w (t + 1)) ∧
        ¬ BddAbove (range fun t => |y t|) := by
  let h (t : ℕ) (x : Fin (t + 1) → ℝ) := -x (Fin.last t)
  have hh (t : ℕ) : NullMeasurable (h t) volume :=
    (measurable_pi_apply (Fin.last t)).neg.nullMeasurable
  obtain ⟨f, hf, w, hw, y, u, h₀, hu, hstep, hunbounded⟩ :=
    MathlibExt.Analysis.Control.FeedbackCapabilityWanted.exists_unbounded_of_le
      (3 / 2 + √2) le_rfl (1 / 100) (by norm_num) h hh (-3)
  refine ⟨f, hf, w, hw, y, h₀, fun t => ?_, hunbounded⟩
  simpa only [hu t, h, Fin.val_last, sub_eq_add_neg] using hstep t
