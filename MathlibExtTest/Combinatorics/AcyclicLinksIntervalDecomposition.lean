/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.AcyclicLinksIntervalDecomposition

open MathlibExt.Combinatorics.AcyclicLinksIntervalDecompositionAMR156Problem0004Wanted

-- A simplex itself is one interval whose rank is its number of vertices.
example (s : Finset ℕ) : HasRankIntervalDecomposition s.powerset s.card := by
  refine ⟨{∅}, fun _ => s, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro σ hσ
    exact ⟨∅, ⟨by simp, Finset.empty_subset _, Finset.mem_powerset.mp hσ⟩,
      fun _ h => Finset.mem_singleton.mp h.1⟩

-- The complex consisting only of the empty face has no interval of positive rank.
example : ¬ HasRankIntervalDecomposition {∅} 1 := by
  rintro ⟨B, top, _, htop, hcover⟩
  obtain ⟨F, ⟨hF, hsub, _⟩, _⟩ := hcover ∅ (by simp)
  obtain rfl := Finset.subset_empty.mp hsub
  obtain ⟨_, hcard, hmem⟩ := htop ∅ hF
  simp [Finset.mem_singleton.mp hmem] at hcard

example : ¬ acyclicLinksIntervalDecomposition := acyclicLinksIntervalDecomposition_refuted
