/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.OddHoleThroughVertexDefs

namespace MetaMathlibExt.Complexity.NPComplete.OddHoleThroughVertex

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : OddHoleThroughVertexInstance) :
    oddHoleThroughVertexDec (bitEncode i) = true ↔
      WellFormed i ∧ OddHoleThroughVertexFeasible i := by
  simp [oddHoleThroughVertexDec, bitDecode_bitEncode]

/-- The edges of the five-cycle `0 - 1 - 2 - 3 - 4 - 0`. -/
private abbrev c5 : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

/-- The identity map is an induced embedding of `cycleGraph 5` onto the five-cycle. -/
private def c5Embedding : SimpleGraph.cycleGraph 5 ↪g Graph (5, c5, 0) where
  toFun x := x
  inj' _ _ h := h
  map_rel_iff' := by
    intro a b
    simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj,
      SimpleGraph.cycleGraph_adj, List.mem_cons,
      Prod.mk.injEq, List.not_mem_nil, or_false]
    revert a b
    decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : oddHoleThroughVertexDec [true] = false := by
  have h : bitDecode (α := OddHoleThroughVertexInstance) [true] = none := rfl
  simp [oddHoleThroughVertexDec, h]

/-- The five-cycle is itself an odd hole through vertex `0`: the identity is an induced
embedding of `cycleGraph 5`. -/
example : oddHoleThroughVertexDec (bitEncode ((5, c5, 0) : OddHoleThroughVertexInstance)) =
    true := by
  apply (accepts_encoding _).2
  exact ⟨by unfold WellFormed; decide, 5, by decide, ⟨2, rfl⟩, c5Embedding, 0, rfl⟩

/-- The same five-cycle with an extra isolated vertex `5`: the graph has an odd hole, but none
passes through `5`, since every vertex of a cycle has a neighbor. -/
example : oddHoleThroughVertexDec (bitEncode ((6, c5, 5) : OddHoleThroughVertexInstance)) =
    false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, k, hk, -, f, x, hx⟩ := (accepts_encoding _).1 hacc
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hadj : (SimpleGraph.cycleGraph (m + 2)).Adj x (x + 1) :=
    SimpleGraph.cycleGraph_adj.2 (Or.inr (by simp))
  have hx' : (f x : ℕ) = 5 := hx
  have h := f.map_rel_iff.2 hadj
  simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed ((6, c5, 5) : OddHoleThroughVertexInstance) :=
  by unfold WellFormed; decide

end MetaMathlibExt.Complexity.NPComplete.OddHoleThroughVertex
