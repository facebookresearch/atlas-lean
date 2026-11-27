/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ConsecutiveSquaresSoCSNotFinitePlanes

/-!
# Tests for finite-plane avoidance

These tests specialize finite-plane avoidance to the empty collection and to three
coordinate planes.
-/

namespace MathlibExtTest.NumberTheory.ConsecutiveSquaresSoCSNotFinitePlanes

open MetaMathlibExt

example : ∃ a b c : ℤ, IsSoCSSolution a b c := by
  obtain ⟨a, b, c, h, _⟩ := soCS_not_finite_planes ∅ (by simp)
  exact ⟨a, b, c, h⟩

open scoped Classical in
example (x y z : ℝ) :
    ∃ a b c : ℤ, IsSoCSSolution a b c ∧
      (a : ℝ) ≠ x ∧ (b : ℝ) ≠ y ∧ (c : ℝ) ≠ z := by
  obtain ⟨a, b, c, hsol, h⟩ := soCS_not_finite_planes
    {(1, 0, 0, x), (0, 1, 0, y), (0, 0, 1, z)} (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> norm_num)
  refine ⟨a, b, c, hsol, ?_, ?_, ?_⟩
  · simpa using h (1, 0, 0, x) (by simp)
  · simpa using h (0, 1, 0, y) (by simp)
  · simpa using h (0, 0, 1, z) (by simp)

end MathlibExtTest.NumberTheory.ConsecutiveSquaresSoCSNotFinitePlanes
