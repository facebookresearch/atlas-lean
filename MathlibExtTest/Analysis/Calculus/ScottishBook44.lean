/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.ScottishBook44
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Planar and nonplanar examples of doubly ruled graphs -/

namespace MathlibExt.Analysis.Calculus.ScottishBook44Wanted.Tests

-- The two coordinate directions rule every constant plane.
example (z : ℝ) : DoublyRuledGraph (fun _ _ ↦ z) := by
  intro x y
  refine ⟨1, 0, 0, 0, 1, 0, ⟨by simp, fun t ↦ by simp⟩, ⟨by simp, fun t ↦ by simp⟩, ?_⟩
  simp

-- For x² - y² the two rulings have slopes +1 and -1 in the horizontal plane.
private theorem saddle_ruled : DoublyRuledGraph (fun x y ↦ x ^ 2 - y ^ 2) := by
  intro x y
  refine ⟨1, 1, 2 * (x - y), 1, -1, 2 * (x + y),
    ⟨by simp, fun t ↦ by dsimp; ring⟩, ⟨by simp, fun t ↦ by dsimp; ring⟩, ?_⟩
  rintro ⟨m, hm, hm'⟩
  linarith

-- Evaluating on the x-axis rules out the planar alternative for this saddle.
example : ∃ a b c d e g : ℝ,
    (∀ x y : ℝ, x ^ 2 - y ^ 2 = a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + g) ∧
    b ^ 2 - 4 * a * c > 0 := by
  obtain ⟨a, b, c, d, e, g, h, hd⟩ := doubly_ruled_graph_is_quadric _ saddle_ruled
  refine ⟨a, b, c, d, e, g, h, hd.resolve_left fun ha ↦ ?_⟩
  linarith [h 1 0, h (-1) 0, h 0 0, ha.1]

end MathlibExt.Analysis.Calculus.ScottishBook44Wanted.Tests
