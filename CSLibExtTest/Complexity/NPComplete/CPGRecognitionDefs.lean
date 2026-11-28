/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CPGRecognitionDefs

namespace MetaMathlibExt.Complexity.NPComplete.CPGRecognition

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : CPGRecognitionInstance) :
    cpgRecognitionDec (bitEncode i) = true ↔
      WellFormed i ∧ CPGRecognitionFeasible i := by
  simp [cpgRecognitionDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : cpgRecognitionDec [true] = false := by
  have h : bitDecode (α := CPGRecognitionInstance) [true] = none := rfl
  simp [cpgRecognitionDec, h]

open SimpleGraph

private theorem adj_iff (i : CPGRecognitionInstance) (u v : Fin i.1) :
    (Graph i).Adj u v ↔ u ≠ v ∧ ((u.val, v.val) ∈ i.2 ∨ (v.val, u.val) ∈ i.2) := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- The path `0 - 1 - 2`. -/
private abbrev path : CPGRecognitionInstance := (3, [(0, 1), (1, 2)])

/-- Vertex `v` gets the unit grid segment from `(v, 0)` to `(v + 1, 0)` of the `4 × 4` grid. -/
private def a (v : Fin 3) : Fin 4 × Fin 4 := (⟨v.val, by omega⟩, 0)
private def b (v : Fin 3) : Fin 4 × Fin 4 := (⟨v.val + 1, by omega⟩, 0)

private theorem hab (v : Fin 3) : (grid 4).Adj (a v) (b v) := by
  simp [boxProd_adj, pathGraph_adj, a, b]

private def P (v : Fin 3) : (grid 4).Walk (a v) (b v) := .cons (hab v) .nil

set_option synthInstance.maxSize 1024 in
private theorem disjoint_touch : ∀ u v : Fin 3, u ≠ v →
    (∀ e, e ∈ (P u).edges → e ∉ (P v).edges) ∧
      ∀ x, x ∈ (P u).support → x ∈ (P v).support → x = a u ∨ x = b u ∨ x = a v ∨ x = b v := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
private theorem adj_touch : ∀ u v : Fin 3, u ≠ v →
    ((u ≠ v ∧ ((u.val, v.val) ∈ path.2 ∨ (v.val, u.val) ∈ path.2)) ↔
      ∃ x, x ∈ (P u).support ∧ x ∈ (P v).support) := by
  decide +kernel

/-- Consecutive unit segments on a line touch at a common endpoint without sharing a grid edge,
and the segments of `0` and `2` are disjoint, so the path `0 - 1 - 2` is a CPG graph. -/
example : cpgRecognitionDec (bitEncode path) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, 4, a, b, P,
    fun v => ⟨(Walk.cons_isPath_iff _ _).2 ⟨Walk.IsPath.nil, ?_⟩, Nat.zero_lt_one⟩,
    disjoint_touch, fun u v huv => (adj_iff _ _ _).trans (adj_touch u v huv)⟩
  simp [a, b]

/-- An edge endpoint outside the vertex range is not well formed. -/
example : cpgRecognitionDec (bitEncode ((2, [(0, 5)]) : CPGRecognitionInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨hw, -⟩
  exact absurd hw (by unfold WellFormed; decide)

end MetaMathlibExt.Complexity.NPComplete.CPGRecognition
