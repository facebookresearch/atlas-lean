/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.MinimumCycleMean
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

/-! # Tests for Karp's minimum cycle mean theorem -/

namespace Cslib.Algorithms.Lean.BellmanFord.karp_minCycleMean

private def forward : Edge 2 := ⟨0, 1, -1⟩
private def backward : Edge 2 := ⟨1, 0, 0⟩
private def alternating : List (Edge 2) := [forward, backward]

private lemma alternating_strong (u v : Fin 2) :
    (toDirectedAdjacency alternating).Reachable u v := by
  apply reachable_iff_exists_isWeightedPath.mpr
  fin_cases u <;> fin_cases v
  · exact ⟨[], by simp [IsWeightedPath]⟩
  · exact ⟨[forward], by simp [alternating, forward, IsWeightedPath]⟩
  · exact ⟨[backward], by simp [alternating, backward, IsWeightedPath]⟩
  · exact ⟨[], by simp [IsWeightedPath]⟩

private lemma alternating_mean : IsMinCycleMean alternating (-1 / 2) := by
  refine ⟨⟨0, [forward, backward], ⟨?_, by simp, ?_⟩, ?_⟩, ?_⟩
  · simp [alternating, forward, backward, IsWeightedPath]
  · decide
  · rfl
  · intro v cycle hc
    have hpos := List.length_pos_iff.mpr hc.2.1
    have hle := hc.2.2.length_le_card
    simp only [pathVertices, List.tail_cons, List.length_map, Fintype.card_fin] at hle
    have hpath := hc.1
    rcases show cycle.length = 1 ∨ cycle.length = 2 by omega with h | h
    · obtain ⟨e, rfl⟩ := List.length_eq_one_iff.mp h
      have he : e = forward ∨ e = backward := by simpa [alternating] using hpath.1 e (by simp)
      rcases he with rfl | rfl <;> fin_cases v <;>
        simp [alternating, forward, backward, IsWeightedPath] at hpath
    · obtain ⟨e, f, rfl⟩ := List.length_eq_two.mp h
      have he : e = forward ∨ e = backward := by simpa [alternating] using hpath.1 e (by simp)
      have hf : f = forward ∨ f = backward := by simpa [alternating] using hpath.1 f (by simp)
      rcases he with rfl | rfl <;> rcases hf with rfl | rfl
      · simp [alternating, forward, IsWeightedPath] at hpath
      · exact le_rfl
      · exact le_rfl
      · simp [alternating, backward, IsWeightedPath] at hpath

private lemma two_step_walk {v : Fin 2} {p : List (Edge 2)}
    (hp : IsWeightedPath alternating 0 v p) (hlen : p.length = 2) :
    v = 0 ∧ p = [forward, backward] := by
  obtain ⟨e, f, rfl⟩ := List.length_eq_two.mp hlen
  have he : e = forward ∨ e = backward := by simpa [alternating] using hp.1 e (by simp)
  have hf : f = forward ∨ f = backward := by simpa [alternating] using hp.1 f (by simp)
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    simp_all [alternating, forward, backward, IsWeightedPath, eq_comm]

-- Length zero is available at the source, while length one is absent there.
example : IsMinWalkWeight alternating 0 0 0 0 := by
  refine ⟨⟨[], by simp [IsWeightedPath], rfl, rfl⟩, ?_⟩
  intro p _ hlen
  simp [List.length_eq_zero_iff.mp hlen, pathWeight]

example (x : ℤ) : ¬ IsMinWalkWeight alternating 0 0 1 x := by
  rintro ⟨⟨p, hp, hlen, _⟩, _⟩
  obtain ⟨e, rfl⟩ := List.length_eq_one_iff.mp hlen
  have he : e = forward ∨ e = backward := by simpa [alternating] using hp.1 e (by simp)
  rcases he with rfl | rfl <;> simp [alternating, forward, backward, IsWeightedPath] at hp

-- A length-two witness has returned to the source and attained the fractional mean.
example : IsMinWalkWeight alternating 0 0 2 (-1) ∧
    ∀ k < 2, ∀ y, IsMinWalkWeight alternating 0 0 k y →
      (((-1 : ℤ) - y : ℤ) : ℚ) / ((2 - k : ℕ) : ℚ) ≤ -1 / 2 := by
  obtain ⟨v, x, hx, hupper⟩ :=
    (karp_minCycleMean alternating alternating_strong 0 (-1 / 2) alternating_mean).2
  obtain ⟨p, hp, hlen, hweight⟩ := hx.1
  obtain ⟨rfl, rfl⟩ := two_step_walk hp hlen
  have hxval : x = -1 := hweight.symm
  subst x
  exact ⟨hx, hupper⟩

end Cslib.Algorithms.Lean.BellmanFord.karp_minCycleMean
