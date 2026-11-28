/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.WeightedDiameterAtLeastDefs

namespace MetaMathlibExt.Complexity.NPComplete.WeightedDiameterAtLeast

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : WeightedDiameterInstance) :
    weightedDiameterAtLeastDec (bitEncode i) = true ↔
      WellFormed i ∧ WeightedDiameterFeasible i := by
  simp [weightedDiameterAtLeastDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : weightedDiameterAtLeastDec [true] = false := by
  have h : bitDecode (α := WeightedDiameterInstance) [true] = none := rfl
  simp [weightedDiameterAtLeastDec, h]

/-- The path `0 - 1 - 2` with edge lengths `{1, 5}` and bound `k`. -/
private abbrev path3 (k : ℕ) : WeightedDiameterInstance := (3, [(0, 1), (1, 2)], [1, 5], k)

private theorem a01 (k : ℕ) : (Graph (path3 k)).Adj 0 1 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

private theorem a10 (k : ℕ) : (Graph (path3 k)).Adj 1 0 := (a01 k).symm

private theorem a12 (k : ℕ) : (Graph (path3 k)).Adj 1 2 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

private theorem a21 (k : ℕ) : (Graph (path3 k)).Adj 2 1 := (a12 k).symm

/-- Giving the edge `01` length `5` puts `0` and `1` at distance `5`: the only path between them
is that edge. -/
example : weightedDiameterAtLeastDec (bitEncode (path3 5)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, [5, 1], List.Perm.swap _ _ _, 0, 1, ?_⟩
  intro p hp
  cases p with
  | cons h p' =>
    rename_i x
    have key : ∀ y : Fin 3, (Graph (path3 5)).Adj 0 y → y = 1 := by
      simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj]
      decide
    obtain rfl := key x h
    obtain rfl := SimpleGraph.Walk.eq_nil_iff_nil.2
      (SimpleGraph.Walk.isPath_iff_nil.1 ((SimpleGraph.Walk.cons_isPath_iff h p').1 hp).1)
    simp [walkLength, edgeLength]

/-- Bound `7` is rejected: whichever edge gets which length, every pair is joined by a path of
length at most `1 + 5 = 6`. -/
example : weightedDiameterAtLeastDec (bitEncode (path3 7)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, w, hw, u, v, h⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, w = [a, b] := by
    match w, hw.length_eq with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have hsum : a + b = 6 := by simpa using hw.sum_eq
  have hv : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hnil : ∀ x : Fin 3, ¬ 7 ≤ walkLength (path3 7) [a, b]
      (SimpleGraph.Walk.nil : (Graph (path3 7)).Walk x x) := by
    intro x
    simp [walkLength]
  rcases hv u with rfl | rfl | rfl <;> rcases hv v with rfl | rfl | rfl
  · exact hnil 0 (h _ .nil)
  · have := h (.cons (a01 7) .nil) (by rw [SimpleGraph.Walk.isPath_def]; decide)
    simp [walkLength, edgeLength] at this
    omega
  · have := h (.cons (a01 7) (.cons (a12 7) .nil)) (by rw [SimpleGraph.Walk.isPath_def]; decide)
    simp [walkLength, edgeLength] at this
    omega
  · have := h (.cons (a10 7) .nil) (by rw [SimpleGraph.Walk.isPath_def]; decide)
    simp [walkLength, edgeLength] at this
    omega
  · exact hnil 1 (h _ .nil)
  · have := h (.cons (a12 7) .nil) (by rw [SimpleGraph.Walk.isPath_def]; decide)
    simp [walkLength, edgeLength] at this
    omega
  · have := h (.cons (a21 7) (.cons (a10 7) .nil)) (by rw [SimpleGraph.Walk.isPath_def]; decide)
    simp [walkLength, edgeLength] at this
    omega
  · have := h (.cons (a21 7) .nil) (by rw [SimpleGraph.Walk.isPath_def]; decide)
    simp [walkLength, edgeLength] at this
    omega
  · exact hnil 2 (h _ .nil)

/-- The rejected instance is well formed, so the rejection comes from the bound. -/
example : WellFormed (path3 7) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.WeightedDiameterAtLeast
