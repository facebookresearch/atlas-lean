/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverParentCells

/-!
# Exact original cover-parent cell rank preimage

The old rank stage pulls back along the SAME actual native parent cell
to precisely its original parent endpoint face. Every coefficient and
original vertex is retained, in both original arrow orientations.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver for the native endpoint readbacks. -/
private local instance coverQuiverForPreimage : Quiver.{v} (CoverVertex V z) := coverQuiver V z

private lemma fin_two_cases (i : Fin 2) : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

private lemma parent_source_rank_iff (k : ℕ) (a : CoverCellLabel V z k) :
    CoverVertex.rank V z (parentEdgeSource V z a.val (coverCellLabel_pos V z k a)) ≤ k ↔
      parentEdgeEndpoint V z a.val (coverCellLabel_pos V z k a) = 0 := by
  unfold parentEdgeSource parentEdgeEndpoint
  cases parentEdge V z a.val (coverCellLabel_pos V z k a) with
  | inl _ =>
    change CoverVertex.rank V z (coverParent V z a.val (coverCellLabel_pos V z k a)) ≤ k ↔
      (0 : Fin 2) = 0
    have hr := coverParent_rank V z a.val (coverCellLabel_pos V z k a)
    have ha := a.property
    constructor
    · intro _; rfl
    · intro _; omega
  | inr _ =>
    change CoverVertex.rank V z a.val ≤ k ↔ (1 : Fin 2) = 0
    rw [a.property]
    constructor
    · intro h; omega
    · intro h; have hv := congrArg Fin.val h; change 1 = 0 at hv; omega

private lemma parent_target_rank_iff (k : ℕ) (a : CoverCellLabel V z k) :
    CoverVertex.rank V z (parentEdgeTarget V z a.val (coverCellLabel_pos V z k a)) ≤ k ↔
      parentEdgeEndpoint V z a.val (coverCellLabel_pos V z k a) = 1 := by
  unfold parentEdgeTarget parentEdgeEndpoint
  cases parentEdge V z a.val (coverCellLabel_pos V z k a) with
  | inl _ =>
    change CoverVertex.rank V z a.val ≤ k ↔ (0 : Fin 2) = 1
    rw [a.property]
    constructor
    · intro h; omega
    · intro h; have hv := congrArg Fin.val h; change 0 = 1 at hv; omega
  | inr _ =>
    change CoverVertex.rank V z (coverParent V z a.val (coverCellLabel_pos V z k a)) ≤ k ↔
      (1 : Fin 2) = 1
    have hr := coverParent_rank V z a.val (coverCellLabel_pos V z k a)
    have ha := a.property
    constructor
    · intro _; rfl
    · intro _; omega

/-- EVERY original parent-cell coefficient is in the old rank stage precisely at its SAME native parent endpoint. -/
lemma coverParentCell_vertex_rank_iff (k : ℕ) (a : CoverCellLabel V z k) (n : ℕ)
    (c : (Δ[1] : SSet.{max u v}) _⦋n⦌) (i : Fin (n + 1)) :
    CoverVertex.rank V z (((coverParentCell V z k a).app (op ⦋n⦌) c).obj i) ≤ k ↔
      c i = parentEdgeEndpoint V z a.val (coverCellLabel_pos V z k a) := by
  rcases fin_two_cases (c i) with hi | hi
  · rw [coverParentCell_obj_zero V z k a n c i hi]
    exact (parent_source_rank_iff V z k a).trans (by rw [hi]; exact eq_comm)
  · rw [coverParentCell_obj_one V z k a n c i hi]
    exact (parent_target_rank_iff V z k a).trans (by rw [hi]; exact eq_comm)

/-- Every full original parent cell lands in the SAME actual next rank stage. -/
lemma coverParentCell_range_le_next (k : ℕ) (a : CoverCellLabel V z k) :
    SSet.Subcomplex.range (coverParentCell V z k a) ≤ coverRankStage V z (k + 1) := by
  intro q w hw
  obtain ⟨c, rfl⟩ := hw
  rcases q with ⟨⟨n⟩⟩
  apply (mem_coverRankStage V z (k + 1) (op ⦋n⦌) _).mpr
  constructor
  · exact coverParentCell_range_le_graph V z k a (op ⦋n⦌) ⟨c, rfl⟩
  · intro i
    rcases fin_two_cases (c i) with hi | hi
    · rw [coverParentCell_obj_zero V z k a n c i hi]
      exact (parentEdgeSource_rank V z a.val (coverCellLabel_pos V z k a)).trans a.property.le
    · rw [coverParentCell_obj_one V z k a n c i hi]
      exact (parentEdgeTarget_rank V z a.val (coverCellLabel_pos V z k a)).trans a.property.le

/-- The SAME entire actual native old-stage preimage is precisely the original parent endpoint face. -/
theorem coverParentCell_preimage_old (k : ℕ) (a : CoverCellLabel V z k) :
    (coverRankStage V z k).preimage (coverParentCell V z k a) =
      SSet.stdSimplex.face {parentEdgeEndpoint V z a.val (coverCellLabel_pos V z k a)} := by
  ext q c
  rcases q with ⟨⟨n⟩⟩
  change ((coverParentCell V z k a).app (op ⦋n⦌) c) ∈ (coverRankStage V z k).obj (op ⦋n⦌) ↔ _
  rw [mem_coverRankStage]
  simp only [SSet.stdSimplex.mem_face_iff, Finset.mem_singleton]
  constructor
  · intro hc i
    exact (coverParentCell_vertex_rank_iff V z k a n c i).mp (hc.2 i)
  · intro hc
    exact ⟨coverParentCell_range_le_graph V z k a (op ⦋n⦌) ⟨c, rfl⟩,
      fun i => (coverParentCell_vertex_rank_iff V z k a n c i).mpr (hc i)⟩

end Quiver.FreeGroupoid.OriginalWords
