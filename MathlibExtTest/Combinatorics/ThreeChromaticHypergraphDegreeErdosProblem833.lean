/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ThreeChromaticHypergraphDegreeErdosProblem833
import Mathlib.Data.Fintype.Pi

/-! # The triangle at the minimum uniformity in Erdős Problem 833 -/

namespace MathlibExtTest.ThreeChromaticHypergraphDegreeErdosProblem833

open MathlibExt.Combinatorics.HypergraphColoringShared
open MathlibExt.Combinatorics.ThreeChromaticHypergraphDegreeErdosProblem833Wanted

private def triangle : Finset (Finset (Fin 3)) := {{0, 1}, {1, 2}, {2, 0}}

-- Every vertex of the triangle has degree two, giving a constraint on any universal constant.
example : ∃ c : ℝ, 0 < c ∧ (1 + c) ^ 2 ≤ 2 := by
  have h₃ : HypergraphColorable triangle 3 := by unfold HypergraphColorable; decide
  have h₂ : ¬ HypergraphColorable triangle 2 := by unfold HypergraphColorable; decide
  obtain ⟨c, hc, h⟩ := threeChromaticHighDegreeVertex_holds
  obtain ⟨v, hv⟩ := h 2 le_rfl 3 triangle (by decide) h₃ h₂
  have deg : ∀ u : Fin 3, (triangle.filter fun e => u ∈ e).card = 2 := by decide
  exact ⟨c, hc, by simpa only [deg v, Nat.cast_ofNat] using hv⟩

end MathlibExtTest.ThreeChromaticHypergraphDegreeErdosProblem833
