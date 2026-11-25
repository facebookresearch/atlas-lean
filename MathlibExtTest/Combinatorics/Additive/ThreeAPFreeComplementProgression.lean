/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ThreeAPFreeComplementProgression
import Mathlib.Tactic.Push

open MathlibExt.Combinatorics.ThreeAPFreeComplementProgressionErdosProblem199Wanted

-- One witness meets every tail, including tails of progressions with negative step.
example : ∃ A : Set ℝ, ThreeAPFree A ∧
    ∀ a d : ℝ, d ≠ 0 → ∀ N : ℕ, ∃ n > N, a + n * d ∈ A := by
  have h := threeAPFreeComplementContainsProgression_refuted
  unfold threeAPFreeComplementContainsProgression at h
  push Not at h
  obtain ⟨A, hA, hhit⟩ := h
  refine ⟨A, hA, fun a d hd N ↦ ?_⟩
  obtain ⟨k, hk⟩ := hhit (a + (N + 1) * d) d hd
  refine ⟨N + 1 + k, by omega, ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one, add_mul, add_assoc] using hk
