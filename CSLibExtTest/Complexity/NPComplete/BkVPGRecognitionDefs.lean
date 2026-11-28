/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BkVPGRecognitionDefs

namespace MetaMathlibExt.Complexity.NPComplete.BkVPGRecognition

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (k : ℕ) (i : BkVPGInstance) :
    bkVPGRecognitionDec k (bitEncode i) = true ↔ WellFormed i ∧ IsBkVPG k (Graph i) := by
  simp [bkVPGRecognitionDec, bitDecode_bitEncode]

private theorem adj_iff (i : BkVPGInstance) (u v : Fin i.1) :
    (Graph i).Adj u v ↔ u ≠ v ∧ ((u.val, v.val) ∈ i.2 ∨ (v.val, u.val) ∈ i.2) := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- A lone continuation bit is a truncated instance encoding, for every `k`. -/
example (k : ℕ) : bkVPGRecognitionDec k [true] = false := by
  have h : bitDecode (α := BkVPGInstance) [true] = none := rfl
  simp [bkVPGRecognitionDec, h]

/-- The path `0 - 1 - 2`. -/
private abbrev path : BkVPGInstance := (3, [(0, 1), (1, 2)])

/-- Vertex `v` gets the horizontal unit segment from `(v, 0)` to `(v + 1, 0)`. -/
private def seg (v : Fin 3) : List (ℕ × ℕ) := [(v.val, 0), (v.val + 1, 0)]

set_option synthInstance.maxSize 1024 in
private theorem seg_touch : ∀ u v : Fin 3, u ≠ v →
    ((u ≠ v ∧ ((u.val, v.val) ∈ path.2 ∨ (v.val, u.val) ∈ path.2)) ↔
      ∃ p, p ∈ seg u ∧ p ∈ seg v) := by
  decide

/-- Consecutive unit segments on a line share an endpoint, so the path is a `B_k`-VPG graph with
straight (bend-free) segments; this holds at `k = 0` and hence at `k = 1`. -/
private theorem path_isBkVPG (k : ℕ) : IsBkVPG k (Graph path) := by
  refine ⟨seg, fun v => ⟨?_, ?_⟩, fun u v huv => (adj_iff _ _ _).trans (seg_touch u v huv)⟩
  · simp [seg, IsGridPath, GridAdj]
  · simp [seg, bends]

example : bkVPGRecognitionDec 0 (bitEncode path) = true :=
  (accepts_encoding 0 _).2 ⟨by unfold WellFormed; decide, path_isBkVPG 0⟩

example : bkVPGRecognitionDec 1 (bitEncode path) = true :=
  (accepts_encoding 1 _).2 ⟨by unfold WellFormed; decide, path_isBkVPG 1⟩

/-- Listing the edge `{0, 1}` in both orientations is not a simple edge list, so the input is
rejected at every `k`, although its graph, a single edge, is representable. -/
example (k : ℕ) : bkVPGRecognitionDec k (bitEncode ((2, [(0, 1), (1, 0)]) : BkVPGInstance)) =
    false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨hw, -⟩
  exact absurd hw (by unfold WellFormed; decide)

end MetaMathlibExt.Complexity.NPComplete.BkVPGRecognition
