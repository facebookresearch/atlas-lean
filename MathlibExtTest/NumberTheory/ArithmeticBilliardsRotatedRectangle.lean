/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticBilliardsRotatedRectangle

-- At `p = 5`, `l = 2` the tilted rectangle has `m = 2`, and the billiard path
-- starts at `(0, 2)` and ends at `(2, 0)`.
example : ∃ P : ℕ → ℤ × ℤ, P 0 = (0, 2) ∧ P 4 = (2, 0) := by
  have h := MetaMathlibExt.arithmetic_billiards_rotated_rectangle 5 2 (by decide) rfl
    ⟨1, rfl⟩ (by decide)
  obtain ⟨P, hP⟩ := h.1
  exact ⟨P, hP.1, (h.2 P hP).2.1⟩

-- At `p = 5`, `l = 2` the billiard path is symmetric: the point at index `3` is
-- the swap of the point at index `1`.
example : ∃ P : ℕ → ℤ × ℤ, P 0 = (0, 2) ∧ P 3 = (P 1).swap := by
  have h := MetaMathlibExt.arithmetic_billiards_rotated_rectangle 5 2 (by decide) rfl
    ⟨1, rfl⟩ (by decide)
  obtain ⟨P, hP⟩ := h.1
  exact ⟨P, hP.1, (h.2 P hP).2.2 1 (by decide)⟩
