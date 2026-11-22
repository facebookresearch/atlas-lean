/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverParentCellPreimage

/-!
# Every full original parent-cell high vertex is read back

Every original coefficient is the actual parent or the SAME individual
high vertex. The original rank detects precisely the latter, retaining
the full generator orientation and every ordinal coefficient.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original cover quiver for all native high-vertex readbacks. -/
private local instance coverQuiverForHighVertex : Quiver.{v} (CoverVertex V z) := coverQuiver V z

private lemma fin_two_cases (i : Fin 2) : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- Every original coefficient retains either the SAME actual original parent or the individual high vertex. -/
lemma coverParentCell_vertex_cases (k : ℕ) (a : CoverCellLabel V z k) (n : ℕ)
    (c : (Δ[1] : SSet.{max u v}) _⦋n⦌) (i : Fin (n + 1)) :
    ((coverParentCell V z k a).app (op ⦋n⦌) c).obj i =
      coverParent V z a.val (coverCellLabel_pos V z k a) ∨
    ((coverParentCell V z k a).app (op ⦋n⦌) c).obj i = a.val := by
  rcases fin_two_cases (c i) with hi | hi
  · rw [coverParentCell_obj_zero V z k a n c i hi]
    unfold parentEdgeSource
    cases parentEdge V z a.val (coverCellLabel_pos V z k a) with
    | inl _ => exact Or.inl rfl
    | inr _ => exact Or.inr rfl
  · rw [coverParentCell_obj_one V z k a n c i hi]
    unfold parentEdgeTarget
    cases parentEdge V z a.val (coverCellLabel_pos V z k a) with
    | inl _ => exact Or.inr rfl
    | inr _ => exact Or.inl rfl

/-- Original native rank above the old stage identifies the SAME individual full high vertex. -/
lemma coverParentCell_vertex_eq_high (k : ℕ) (a : CoverCellLabel V z k) (n : ℕ)
    (c : (Δ[1] : SSet.{max u v}) _⦋n⦌) (i : Fin (n + 1))
    (h : ¬ CoverVertex.rank V z (((coverParentCell V z k a).app (op ⦋n⦌) c).obj i) ≤ k) :
    ((coverParentCell V z k a).app (op ⦋n⦌) c).obj i = a.val := by
  rcases coverParentCell_vertex_cases V z k a n c i with hp | ha
  · rw [hp] at h
    have hr := coverParent_rank V z a.val (coverCellLabel_pos V z k a)
    have he := a.property
    omega
  · exact ha

/-- A full original coefficient outside the actual old-stage preimage includes a SAME original high vertex. -/
lemma coverParentCell_high_vertex_exists (k : ℕ) (a : CoverCellLabel V z k) (n : ℕ)
    (c : (Δ[1] : SSet.{max u v}) _⦋n⦌)
    (h : c ∉ ((coverRankStage V z k).preimage (coverParentCell V z k a)).obj (op ⦋n⦌)) :
    ∃ i : Fin (n + 1),
      ((coverParentCell V z k a).app (op ⦋n⦌) c).obj i = a.val ∧
        ¬ CoverVertex.rank V z (((coverParentCell V z k a).app (op ⦋n⦌) c).obj i) ≤ k := by
  classical
  have hn : ¬ ∀ i : Fin (n + 1),
      CoverVertex.rank V z (((coverParentCell V z k a).app (op ⦋n⦌) c).obj i) ≤ k := by
    intro hc
    apply h
    exact (mem_coverRankStage V z k (op ⦋n⦌) _).mpr
      ⟨coverParentCell_range_le_graph V z k a (op ⦋n⦌) ⟨c, rfl⟩, hc⟩
  obtain ⟨i, hi⟩ := not_forall.mp hn
  exact ⟨i, coverParentCell_vertex_eq_high V z k a n c i hi, hi⟩

end Quiver.FreeGroupoid.OriginalWords
