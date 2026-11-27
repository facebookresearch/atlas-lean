/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Nat.ProgressionIntersection
import Mathlib.Order.Interval.Finset.Nat

/-! # Tests for intersections of natural arithmetic progressions -/

open MetaMathlibExt

-- The first two progressions meet at 22, which misses the progression through 16 and 2.
-- Its first common term is 142, and there are common terms beyond every bound.
example (N : ℕ) : ∃ x > N, (∃ i : ℕ, x = 4 + 6 * i) ∧ (∃ j : ℕ, x = 2 + 10 * j) ∧
    ∃ k : ℕ, x = 2 + 14 * k := by
  have h := natProgression_inter_infinite 4 2 6 10 16 2 (by decide) (by decide)
    ⟨2, rfl⟩ ⟨0, rfl⟩ ⟨22, ⟨3, rfl⟩, ⟨2, rfl⟩⟩ (by decide)
  obtain ⟨x, ⟨⟨hx₁, hx₂⟩, hx₃⟩, hx⟩ := h.exists_gt N
  exact ⟨x, hx, hx₁, hx₂, hx₃⟩

-- Starting at zero with a unit gap makes the third progression all of ℕ.
example : {x : ℕ | 3 ∣ x ∧ x % 4 = 1}.Infinite := by
  have h := natProgression_inter_infinite 0 1 3 4 0 1 (by decide) (by decide)
    ⟨0, rfl⟩ ⟨0, rfl⟩ ⟨9, ⟨3, rfl⟩, ⟨2, rfl⟩⟩ (by decide)
  refine h.mono ?_
  rintro x ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, _⟩
  exact ⟨⟨i, by simpa only [Nat.zero_add] using hi⟩, by simp [hj, Nat.add_mul_mod_self_left]⟩
