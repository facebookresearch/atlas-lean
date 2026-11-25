/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.DensePartitionExpansiveSequenceKourovka15Problem80
import Mathlib.Topology.Order

/-! # Tests for expansive sequences and Kourovka Problem 15.80 -/

open MathlibExt.GroupTheory.DensePartitionExpansiveSequenceKourovka15Problem80Wanted

-- The singleton sequence is expansive when the only nonempty open set is the whole space.
example : @IsExpansiveSequence ℕ ⊤ (fun n ↦ {n}) := by
  constructor
  · intro i j hij
    simpa using hij
  · intro U hU hne
    rcases (TopologicalSpace.isOpen_top_iff U).1 hU with h | rfl
    · simp [h] at hne
    · exact ⟨0, fun n _ ↦ ⟨n, Finset.mem_singleton_self n, Set.mem_univ n⟩⟩

-- A discrete singleton neighborhood cannot meet two disjoint terms in the tail.
example (F : ℕ → Finset ℕ) : ¬ @IsExpansiveSequence ℕ ⊥ F := by
  rintro ⟨hdisj, hmeet⟩
  obtain ⟨m, hm⟩ := hmeet {0} (by trivial) ⟨0, rfl⟩
  have hmem (n : ℕ) (hn : m < n) : 0 ∈ F n := by
    obtain ⟨x, hx, hx0⟩ := hm n hn
    simpa only [Set.mem_singleton_iff.mp hx0] using hx
  have hlt : m + 1 < m + 2 := Nat.lt_succ_self (m + 1)
  exact Finset.disjoint_left.mp (hdisj hlt.ne)
    (hmem (m + 1) (Nat.lt_succ_self m)) (hmem (m + 2) ((Nat.lt_succ_self m).trans hlt))

-- Importing the proved module exposes the original counterexample statement.
example : ¬ ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∃ P : ℕ → Set G, Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (⋃ i, P i) = Set.univ ∧
      ∀ i, Dense (P i)) → ∃ F : ℕ → Finset G, IsExpansiveSequence F :=
  countableDensePartitionHasExpansiveSequence_refuted
