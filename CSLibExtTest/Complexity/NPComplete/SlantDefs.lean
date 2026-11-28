/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SlantDefs

namespace MetaMathlibExt.Complexity.NPComplete.Slant

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SlantInstance) :
    slantDec (bitEncode i) = true ↔ WellFormed i ∧ SlantFeasible i := by
  simp [slantDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : slantDec [true] = false := by
  have h : bitDecode (α := SlantInstance) [true] = none := rfl
  simp [slantDec, h]

/-- The neighbors of the top corners of a single square: the diagonal touches `(0, 0)` exactly
when it runs from `(0, 0)` to `(1, 1)`, and `(0, 1)` otherwise. -/
private theorem neighborSet_00 (d : ℕ → ℕ → Bool) :
    (diagGraph 1 1 d).neighborSet (0, 0) = if d 0 0 then {(1, 1)} else ∅ := by
  ext ⟨a, b⟩
  simp only [SimpleGraph.mem_neighborSet, diagGraph, SimpleGraph.fromRel_adj]
  cases h : d 0 0
  · simp [h]
  · simp [h]; omega

private theorem neighborSet_01 (d : ℕ → ℕ → Bool) :
    (diagGraph 1 1 d).neighborSet (0, 1) = if d 0 0 then ∅ else {(1, 0)} := by
  ext ⟨a, b⟩
  simp only [SimpleGraph.mem_neighborSet, diagGraph, SimpleGraph.fromRel_adj]
  cases h : d 0 0
  · simp [h]; omega
  · simp [h]

/-- A graph whose only edge is `s(a, b)` is acyclic: that edge is a bridge. -/
private theorem isAcyclic_of_single_edge {V : Type} (G : SimpleGraph V) (a b : V)
    (h : ∀ u v, G.Adj u v → s(u, v) = s(a, b)) : G.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  rw [SimpleGraph.isBridge_iff]
  intro hr
  have hbot : G.deleteEdges {s(u, v)} = ⊥ := by
    ext x y
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, SimpleGraph.bot_adj,
      iff_false, not_and, not_not]
    intro hxy
    exact (h x y hxy).trans (h u v huv).symm
  rw [hbot, SimpleGraph.reachable_bot] at hr
  exact huv.ne hr

/-- One square with clues `1` at `(0, 0)` and `0` at `(0, 1)`: the diagonal from `(0, 0)` to
`(1, 1)` solves it. -/
example : slantDec (bitEncode ([[(true, 1), (true, 0)], [(false, 0), (false, 0)]] :
    SlantInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, fun _ _ => true, ?_, ?_⟩
  · refine isAcyclic_of_single_edge _ (0, 0) (1, 1) fun u v huv => ?_
    simp only [diagGraph, SimpleGraph.fromRel_adj, height, width] at huv
    obtain ⟨-, ⟨r, hr, c, hc, ⟨-, rfl, rfl⟩ | ⟨h, -⟩⟩ | ⟨r, hr, c, hc, ⟨-, rfl, rfl⟩ | ⟨h, -⟩⟩⟩ :=
      huv
    · simp at hr hc; subst hr hc; rfl
    · simp at h
    · simp at hr hc; subst hr hc; exact Sym2.eq_swap
    · simp at h
  · intro r hr c hc hnum
    simp only [height, width, List.length_cons, List.length_nil, List.headD_cons] at hr hc
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl <;>
      rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
    · simp [height, width, neighborSet_00, clue]
    · simp [height, width, neighborSet_01, clue]
    · simp [clue] at hnum
    · simp [clue] at hnum

/-- One square with clues `1` at both `(0, 0)` and `(0, 1)` has no solution: its single diagonal
touches exactly one of the two top corners. -/
example : slantDec (bitEncode ([[(true, 1), (true, 1)], [(false, 0), (false, 0)]] :
    SlantInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, d, -, hclue⟩ := (accepts_encoding _).1 h
  have h0 : ((diagGraph 1 1 d).neighborSet (0, 0)).ncard = 1 :=
    hclue 0 (by decide) 0 (by decide) rfl
  have h1 : ((diagGraph 1 1 d).neighborSet (0, 1)).ncard = 1 :=
    hclue 0 (by decide) 1 (by decide) rfl
  rw [neighborSet_00] at h0
  rw [neighborSet_01] at h1
  cases hd : d 0 0 <;> simp [hd] at h0 h1

/-- A clue above `4` makes the board malformed. -/
example : slantDec (bitEncode ([[(true, 5), (false, 0)], [(false, 0), (false, 0)]] :
    SlantInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1.2.2.2 [(true, 5), (false, 0)] (by simp) (true, 5)
    (by simp)).1 (by decide)

end MetaMathlibExt.Complexity.NPComplete.Slant
