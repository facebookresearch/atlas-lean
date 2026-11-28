/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Bioinformatics.IntronClusters

/-! # Regressions for intron clustering -/

set_option autoImplicit false

namespace Cslib.Bioinformatics.IntronClusters.Tests

private def observed : Set (ℕ × ℕ) := {(1, 3), (1, 7), (5, 7), (2, 4)}

private def left : observed := ⟨(1, 3), by simp [observed]⟩
private def bridge : observed := ⟨(1, 7), by simp [observed]⟩
private def right : observed := ⟨(5, 7), by simp [observed]⟩
private def isolated : observed := ⟨(2, 4), by simp [observed]⟩

private theorem left_bridge : (junctionGraph observed).Adj left bridge := by
  refine ⟨?_, Or.inl rfl⟩
  intro h
  have he : (3 : ℕ) = 7 := congrArg (fun v : observed => v.val.2) h
  cases he

private theorem bridge_right : (junctionGraph observed).Adj bridge right := by
  refine ⟨?_, Or.inr rfl⟩
  intro h
  have he : (1 : ℕ) = 5 := congrArg (fun v : observed => v.val.1) h
  cases he

-- The endpoints do not share a splice site, but the two edges put them in one retained cluster.
example : ¬ (junctionGraph observed).Adj left right ∧
    (junctionGraph observed).connectedComponentMk left =
      (junctionGraph observed).connectedComponentMk right ∧
    (junctionGraph observed).connectedComponentMk left ∈ clusters observed := by
  refine ⟨?_, SimpleGraph.ConnectedComponent.sound
    (left_bridge.reachable.trans bridge_right.reachable), ?_⟩
  · rintro ⟨_, h | h⟩ <;> cases h
  · exact (mem_clusters_iff_has_neighbor left).mpr ⟨bridge, left_bridge⟩

-- The isolated intron is not retained even though its connected component exists.
example : (junctionGraph observed).connectedComponentMk isolated ∉ clusters observed := by
  rw [mem_clusters_iff_has_neighbor]
  rintro ⟨⟨p, hp⟩, hne, h⟩
  simp only [observed, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rcases h with h | h <;> cases h
  · rcases h with h | h <;> cases h
  · rcases h with h | h <;> cases h
  · exact hne rfl

private def withoutBridge : Set (ℕ × ℕ) := observed \ {(1, 7)}

-- Recompute components on the remaining vertices: with the bridge deleted, no cluster survives.
example : clusters withoutBridge = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro C
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h u =>
      rw [mem_clusters_iff_has_neighbor]
      rintro ⟨v, hne, h⟩
      obtain ⟨u, hu⟩ := u
      obtain ⟨v, hv⟩ := v
      simp only [withoutBridge, observed, Set.mem_sdiff, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hu hv
      obtain ⟨hu, hbu⟩ := hu
      obtain ⟨hv, hbv⟩ := hv
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
      all_goals
        first
        | exact hbu rfl
        | exact hbv rfl
        | exact hne rfl
        | rcases h with h | h <;> cases h

private def crossOnly : Set (ℕ × ℕ) := {(1, 3), (3, 7)}

-- A donor coinciding with the other acceptor is not enough.
example : ¬ (junctionGraph crossOnly).Adj ⟨(1, 3), by simp [crossOnly]⟩
    ⟨(3, 7), by simp [crossOnly]⟩ := by
  rintro ⟨_, h | h⟩ <;> cases h

end Cslib.Bioinformatics.IntronClusters.Tests
