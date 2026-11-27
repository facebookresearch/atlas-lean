/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ProgressionDifferenceSetErdosProblem1185
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Push

namespace MathlibExtTest.Combinatorics.ProgressionDifferenceSetErdosProblem1185

open MathlibExt.Combinatorics.ProgressionDifferenceSetErdosProblem1185Wanted

-- A caller can extract counterexamples beyond any cutoff, with the density and length fixed.
example :
    ∃ δ : ℝ, 0 < δ ∧ ∃ k : ℕ, 3 ≤ k ∧ ∀ m N₀ : ℕ, 1 ≤ m →
      ∃ N : ℕ, N₀ ≤ N ∧ ∃ A B : Finset ℕ,
        A ⊆ Finset.Icc 1 N ∧ B ⊆ Finset.Icc 1 N ∧ δ * N ≤ A.card ∧ m ≤ B.card ∧
          ¬ ∃ a d : ℕ, 0 < d ∧ (∃ b₁ ∈ B, ∃ b₂ ∈ B, b₂ + d = b₁) ∧
            ∀ i < k, a + i * d ∈ A := by
  have h := progressionWithDifferenceInDifferenceSet_refuted
  unfold progressionWithDifferenceInDifferenceSet at h
  simp only [Filter.eventually_atTop] at h
  push +distrib Not at h ⊢
  obtain ⟨δ, hδ, k, hk, h⟩ := h
  refine ⟨δ, hδ, k, hk, ?_⟩
  intro m N₀ hm
  exact ((h m).resolve_left (not_lt_of_ge hm)) N₀

end MathlibExtTest.Combinatorics.ProgressionDifferenceSetErdosProblem1185
