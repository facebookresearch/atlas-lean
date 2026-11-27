/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.DegenerateSecondOrder
import Mathlib.Tactic.Ring

/-! # Tests for the closed forms of degenerate second-order recurrences -/

namespace MetaMathlibExt.degenerate_secondOrder_closedForms

private def sixCycle : ℕ → ℤ
  | 0 => 3
  | 1 => -2
  | n + 2 => sixCycle (n + 1) - sixCycle n

-- The terms on either side of each period boundary are 5 and 3.
example (n : ℕ) : sixCycle (6 * n + 5) = 5 ∧ sixCycle (6 * (n + 1)) = 3 := by
  have cycle := period_six sixCycle (fun _ => rfl)
  obtain ⟨_, _, _, _, _, hlast⟩ := cycle n
  exact ⟨hlast, (cycle (n + 1)).1⟩

-- The signed affine expression has intercept 3 even at index zero.
example (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = -2 * w (k + 1) - w k)
    (h₀ : w 0 = 3) (h₁ : w 1 = -2) (n : ℕ) : w n = (-1) ^ n * (3 - (n : ℤ)) := by
  rw [alternating_affine w hw n, h₀, h₁, pow_succ]
  ring

-- The alternating tail starts at index one, with arbitrary zeroth term.
example (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = -w (k + 1)) (n : ℕ) :
    w (n + 1) = (-1) ^ n * w 1 := by
  simpa [pow_succ] using alternating_tail w hw (n + 1) (Nat.succ_pos n)

end MetaMathlibExt.degenerate_secondOrder_closedForms
