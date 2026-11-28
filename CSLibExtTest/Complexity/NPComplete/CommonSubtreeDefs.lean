/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CommonSubtreeDefs
-- The star graph and the proof that it is a tree.
import Mathlib.Combinatorics.SimpleGraph.Star

namespace MetaMathlibExt.Complexity.NPComplete.CommonSubtree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : CommonSubtreeInstance) :
    commonSubtreeDec (bitEncode i) = true ↔
      WellFormed i ∧ CommonSubtreeFeasible i := by
  simp [commonSubtreeDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : commonSubtreeDec [true] = false := by
  have h : bitDecode (α := CommonSubtreeInstance) [true] = none := rfl
  simp [commonSubtreeDec, h]

open SimpleGraph

private theorem adj_iff (t : ℕ × List (ℕ × ℕ)) (u v : Fin t.1) :
    (Graph t).Adj u v ↔ u ≠ v ∧ ((u.val, v.val) ∈ t.2 ∨ (v.val, u.val) ∈ t.2) := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- The path `0 - 1 - 2`. -/
private abbrev path3 : ℕ × List (ℕ × ℕ) := (3, [(0, 1), (1, 2)])

/-- The star with centre `0` and leaves `1`, `2`, `3`. -/
private abbrev star4 : ℕ × List (ℕ × ℕ) := (4, [(0, 1), (0, 2), (0, 3)])

set_option synthInstance.maxSize 1024 in
private theorem graph_path3 : Graph path3 = pathGraph 3 := by
  ext u v
  rw [adj_iff, pathGraph_adj]
  revert u v
  decide

set_option synthInstance.maxSize 1024 in
private theorem graph_star4 : Graph star4 = starGraph 0 := by
  ext u v
  rw [adj_iff, starGraph_adj]
  revert u v
  decide

private theorem wellFormed (K : ℕ) (hK : 0 < K) : WellFormed ([path3, star4], K) := by
  refine ⟨by simp, ?_, hK⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro t (rfl | rfl)
  · exact ⟨by decide, by decide, graph_path3 ▸ isTree_pathGraph_add_one 2⟩
  · exact ⟨by decide, by decide, graph_star4 ▸ isTree_starGraph 0⟩

/-- The path `1 - 0 - 2` through the centre of the star, as `0 ↦ 1`, `1 ↦ 0`, `2 ↦ 2`. -/
private def intoStar : Fin 3 → Fin 4 := fun v => [1, 0, 2].getD v.val 0

set_option synthInstance.maxSize 1024 in
private theorem intoStar_adj : ∀ a b : Fin 3,
    ((intoStar a ≠ intoStar b ∧ (((intoStar a).val, (intoStar b).val) ∈ star4.2 ∨
        ((intoStar b).val, (intoStar a).val) ∈ star4.2)) ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val)) := by
  decide

/-- The three-vertex path is an induced subtree of the path `0 - 1 - 2` (as itself) and of the
star (through its centre), so `K = 3` is attained. -/
example : commonSubtreeDec (bitEncode (([path3, star4], 3) : CommonSubtreeInstance)) = true := by
  refine (accepts_encoding _).2 ⟨wellFormed 3 (by decide), 3, le_rfl, pathGraph 3,
    isTree_pathGraph_add_one 2, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro t (rfl | rfl)
  · exact ⟨graph_path3 ▸ Embedding.refl⟩
  · refine ⟨⟨⟨intoStar, by decide⟩, fun {a b} => ?_⟩⟩
    rw [pathGraph_adj, ← intoStar_adj]
    exact adj_iff _ _ _

/-- A tree with at least four vertices cannot embed into the three-vertex path, so `K = 4` is
unattainable for the same trees. -/
example : commonSubtreeDec (bitEncode (([path3, star4], 4) : CommonSubtreeInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, m, hm, T', -, h⟩
  obtain ⟨f⟩ := h path3 (by simp)
  have := Fintype.card_le_of_injective f f.injective
  simp at this
  omega

end MetaMathlibExt.Complexity.NPComplete.CommonSubtree
