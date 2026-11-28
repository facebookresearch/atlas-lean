/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.EvenHoleThroughVertexDefs

namespace MetaMathlibExt.Complexity.NPComplete.EvenHoleThroughVertex

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open OddHoleThroughVertex (Graph WellFormed)

private theorem accepts_encoding (i : EvenHoleThroughVertexInstance) :
    evenHoleThroughVertexDec (bitEncode i) = true ↔
      WellFormed i ∧ EvenHoleThroughVertexFeasible i := by
  simp [evenHoleThroughVertexDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : evenHoleThroughVertexDec [true] = false := by
  have h : bitDecode (α := EvenHoleThroughVertexInstance) [true] = none := rfl
  simp [evenHoleThroughVertexDec, h]

private instance (i : EvenHoleThroughVertexInstance) : DecidableRel (Graph i).Adj :=
  fun a b =>
    decidable_of_iff (a ≠ b ∧ (((a : ℕ), (b : ℕ)) ∈ i.2.1 ∨ ((b : ℕ), (a : ℕ)) ∈ i.2.1))
      (by simp [Graph, Cslib.Complexity.Karp.edgeGraph])

/-- The 4-cycle `0 - 1 - 2 - 3 - 0` with given vertex `0`. -/
private abbrev square : EvenHoleThroughVertexInstance :=
  (4, [(0, 1), (1, 2), (2, 3), (3, 0)], 0)

/-- The 4-cycle is itself an even hole through `0`: the identity is an induced embedding of
`cycleGraph 4`. -/
example : evenHoleThroughVertexDec (bitEncode square) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, 4, le_refl _, ⟨2, rfl⟩,
    ⟨⟨id, fun _ _ h => h⟩, ?_⟩, 0, rfl⟩
  intro a b
  revert a b
  decide

/-- A 4-cycle on `1, 2, 3, 4` plus the isolated vertex `0`: the graph has an even hole, but
none through `0`, since every vertex of a hole has a neighbor. -/
example : evenHoleThroughVertexDec
    (bitEncode ((5, [(1, 2), (2, 3), (3, 4), (4, 1)], 0) : EvenHoleThroughVertexInstance)) =
      false := by
  cases h : evenHoleThroughVertexDec
      (bitEncode ((5, [(1, 2), (2, 3), (3, 4), (4, 1)], 0) : EvenHoleThroughVertexInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, k, hk, -, f, x, hx⟩ := (accepts_encoding _).1 h
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    have hadj : (SimpleGraph.cycleGraph (n + 2)).Adj x (x + 1) :=
      SimpleGraph.cycleGraph_adj.2 (Or.inr (add_sub_cancel_left x 1))
    have := f.map_rel_iff.2 hadj
    simp only at hx
    simp [Graph, Cslib.Complexity.Karp.edgeGraph] at this
    omega

end MetaMathlibExt.Complexity.NPComplete.EvenHoleThroughVertex
