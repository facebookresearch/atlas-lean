/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SidonComplementProgression
import Mathlib.Tactic.Push

open MathlibExt.Combinatorics.SidonSetComplementProgressionErdosProblem198Wanted

-- The same Sidon set meets each progression after any prescribed number of steps.
example : ∃ A : Set ℕ, A.IsSidon ∧
    ∀ a d : ℕ, 0 < d → ∀ N : ℕ, ∃ k > N, a + k * d ∈ A := by
  have h := sidonComplementContainsProgression_refuted
  unfold sidonComplementContainsProgression at h
  push Not at h
  obtain ⟨A, hA, hhit⟩ := h
  refine ⟨A, hA, fun a d hd N ↦ ?_⟩
  obtain ⟨k, hk⟩ := hhit (a + (N + 1) * d) d hd
  exact ⟨N + 1 + k, by omega, by simpa only [Nat.add_mul, Nat.add_assoc] using hk⟩
