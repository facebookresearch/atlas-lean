/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Foundations.Semantics.LTS.InductiveInvariant

/-! # Regressions for safety by inductive invariants -/

set_option autoImplicit false

namespace CSLibExtTest.Foundations.Semantics.LTS.InductiveInvariant

open Cslib

-- One component is reachable from 0. Another contains an edge into the bad set;
-- taking the complement of the bad set alone does not give a step-closed invariant.
private def graph : LTS ℕ Bool where
  Tr s a t := (s = 0 ∧ a = false ∧ t = 1) ∨ (s = 1 ∧ a = true ∧ t = 2) ∨
    (s = 10 ∧ a = true ∧ t = 11)

private def initial : Set ℕ := {0, 4}
private def keep : Set ℕ := {0, 1, 2, 4}

private theorem hkeep : graph.InductiveFrom initial keep := by
  constructor
  · intro s hs
    simp [initial] at hs
    rcases hs with rfl | rfl <;> simp [keep]
  · intro s a t hst hs
    rcases hst with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ <;> simp [keep] at hs ⊢

-- Exact least set: neither the isolated initial state nor the two-step deadlock is lost.
example : graph.reachableFrom initial = keep := by
  apply Set.Subset.antisymm ((graph.isLeast_reachableFrom initial).2 hkeep)
  intro s hs
  simp [keep] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact ⟨0, by simp [initial], LTS.CanReach.refl graph 0⟩
  · exact ⟨0, by simp [initial], [false], .stepL (Or.inl ⟨rfl, rfl, rfl⟩) .refl⟩
  · exact ⟨0, by simp [initial], [false, true], .stepL (Or.inl ⟨rfl, rfl, rfl⟩)
      (.stepL (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) .refl)⟩
  · exact ⟨4, by simp [initial], LTS.CanReach.refl graph 4⟩

example : Disjoint (graph.reachableFrom initial) ({11} : Set ℕ) ∧
    ¬ graph.InductiveFrom initial ({11} : Set ℕ)ᶜ := by
  constructor
  · apply (graph.disjoint_reachableFrom_iff_exists_inductive initial {11}).mpr
    refine ⟨keep, hkeep, Set.disjoint_left.mpr ?_⟩
    intro s h₁ h₂
    have : s = 11 := by simpa using h₂
    subst s
    simp [keep] at h₁
  · intro h
    have hn := h.2 10 true 11 (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (by simp)
    simp at hn

-- A bad initial state defeats safety even before taking any transition.
example : ¬ ∃ J, graph.InductiveFrom initial J ∧ Disjoint J ({4} : Set ℕ) := by
  rintro ⟨J, hJ, hbad⟩
  exact Set.disjoint_left.mp hbad (hJ.1 (by simp [initial] : 4 ∈ initial)) (by simp)

end CSLibExtTest.Foundations.Semantics.LTS.InductiveInvariant
