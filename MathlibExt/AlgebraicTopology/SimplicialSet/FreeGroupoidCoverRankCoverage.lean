/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverAllCellInjection
import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverGeneratorParentCell
import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveGraphClassifier
import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveGeneratorConstantFaces

/-!
# Full original all-parent-cell rank-stage coverage

Every original graph word is either already in the old rank stage or
is a constant or original generator coefficient of its SAME actual
high-vertex parent cell. All individual original vertices, arrows,
orientations and ordinal coefficients remain in the native range.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver for full native stage coverage. -/
private local instance coverQuiverForCoverage : Quiver.{v} (CoverVertex V z) := coverQuiver V z

private lemma constant_high_mem_range (k n : ℕ) (a : CoverCellLabel V z k) :
    (Functor.const (Fin (n + 1)) (C := Paths (CoverVertex V z))).obj (a.val : Paths (CoverVertex V z)) ∈
      (SSet.Subcomplex.range (coverAllCellMap V z k)).obj (op ⦋n⦌) := by
  let ha := coverCellLabel_pos V z k a
  rcases coverParent_arrow V z a.val ha with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · let c : (Δ[1] : SSet.{max u v}) _⦋n⦌ :=
      SSet.stdSimplex.objMk (OrderHom.const (Fin (n + 1)) (1 : Fin 2))
    have he := coverGeneratorCell_eq_target_parent V z k (coverParent V z a.val ha) a.val f
      a.property (coverParent_rank V z a.val ha)
    refine ⟨⟨a, c⟩, ?_⟩
    have hc := CategoryTheory.FreePathNerveCoordinates.generatorCell_constant_one (CoverVertex V z) f n
    exact (congrArg (fun F => F.app (op ⦋n⦌) c) he).symm.trans hc
  · let c : (Δ[1] : SSet.{max u v}) _⦋n⦌ :=
      SSet.stdSimplex.objMk (OrderHom.const (Fin (n + 1)) (0 : Fin 2))
    have he := coverGeneratorCell_eq_source_parent V z k a.val (coverParent V z a.val ha) f
      a.property (coverParent_rank V z a.val ha)
    refine ⟨⟨a, c⟩, ?_⟩
    have hc := CategoryTheory.FreePathNerveCoordinates.generatorCell_constant_zero (CoverVertex V z) f n
    exact (congrArg (fun F => F.app (op ⦋n⦌) c) he).symm.trans hc

/-- Every SAME original next-stage full word occurs in the old stage or its actual native high-vertex cell. -/
theorem coverRankStage_sup_range (k : ℕ) :
    coverRankStage V z k ⊔ SSet.Subcomplex.range (coverAllCellMap V z k) = coverRankStage V z (k + 1) := by
  apply le_antisymm
  · exact sup_le (coverRankStage_mono V z (Nat.le_succ k)) (coverAllCellMap_range_le_next V z k)
  · intro q w hw
    rcases q with ⟨⟨n⟩⟩
    change Fin (n + 1) ⥤ Paths (CoverVertex V z) at w
    have hstage := (mem_coverRankStage V z (k + 1) (op ⦋n⦌) w).mp hw
    by_cases h_old : ∀ i : Fin (n + 1), CoverVertex.rank V z (w.obj i) ≤ k
    · exact Or.inl ((mem_coverRankStage V z k (op ⦋n⦌) w).mpr ⟨hstage.1, h_old⟩)
    · classical
      obtain ⟨i, hi⟩ := not_forall.mp h_old
      have hhigh : CoverVertex.rank V z (w.obj i) = k + 1 := by have h := hstage.2 i; omega
      have hlen : (CategoryTheory.FreePathNerveCoordinates.totalPath (CoverVertex V z) n w).length ≤ 1 := hstage.1
      have hcases : (CategoryTheory.FreePathNerveCoordinates.totalPath (CoverVertex V z) n w).length = 0 ∨
          (CategoryTheory.FreePathNerveCoordinates.totalPath (CoverVertex V z) n w).length = 1 := by omega
      right
      rcases hcases with hzero | hone
      · have hconst := CategoryTheory.FreePathNerveCoordinates.original_graph_word_constant (CoverVertex V z) n w hzero
        have hv : w.obj i = w.obj 0 := congrArg (fun F => F.obj i) hconst
        have hr0 : CoverVertex.rank V z (w.obj 0) = k + 1 := (congrArg (CoverVertex.rank V z) hv).symm.trans hhigh
        have hm := constant_high_mem_range V z k n ⟨w.obj 0, hr0⟩
        exact hconst.symm ▸ hm
      · obtain ⟨f, c, hc⟩ := CategoryTheory.FreePathNerveCoordinates.original_graph_word_generator (CoverVertex V z)
          n w hone
        have hsource : CoverVertex.rank V z (w.obj 0) ≤ k + 1 := hstage.2 0
        have htarget : CoverVertex.rank V z (w.obj (Fin.last n)) ≤ k + 1 := hstage.2 (Fin.last n)
        have hv := congrArg (fun F => F.obj i) hc
        have hi_cases : c i = (0 : Fin 2) ∨ c i = (1 : Fin 2) := by
          let t : Fin 2 := c i
          have ht : t = (0 : Fin 2) ∨ t = (1 : Fin 2) := by
            rcases t with ⟨j, hj⟩
            have hj_cases : j = 0 ∨ j = 1 := by omega
            rcases hj_cases with hj0 | hj1
            · exact Or.inl (Fin.ext hj0)
            · exact Or.inr (Fin.ext hj1)
          exact ht
        rcases hi_cases with hi0 | hi1
        · have hvi := CategoryTheory.FreePathNerveCoordinates.generatorCell_obj_zero (CoverVertex V z) f n c i hi0
          have hs : w.obj 0 = w.obj i := hvi.symm.trans hv
          have hsa : CoverVertex.rank V z (w.obj 0) = k + 1 := (congrArg (CoverVertex.rank V z) hs).trans hhigh
          have hr : CoverVertex.rank V z (w.obj (Fin.last n)) + 1 = CoverVertex.rank V z (w.obj 0) := by
            rcases coverArrow_rank_step V z f with hr | hr
            · exact hr
            · omega
          have he := coverGeneratorCell_eq_source_parent V z k (w.obj 0) (w.obj (Fin.last n)) f hsa hr
          exact ⟨⟨⟨w.obj 0, hsa⟩, c⟩, (congrArg (fun F => F.app (op ⦋n⦌) c) he).symm.trans hc⟩
        · have hvi := CategoryTheory.FreePathNerveCoordinates.generatorCell_obj_one (CoverVertex V z) f n c i hi1
          have hs : w.obj (Fin.last n) = w.obj i := hvi.symm.trans hv
          have hsa : CoverVertex.rank V z (w.obj (Fin.last n)) = k + 1 := (congrArg (CoverVertex.rank V z) hs).trans
            hhigh
          have hr : CoverVertex.rank V z (w.obj 0) + 1 = CoverVertex.rank V z (w.obj (Fin.last n)) := by
            rcases coverArrow_rank_step V z f with hr | hr
            · omega
            · exact hr
          have he := coverGeneratorCell_eq_target_parent V z k (w.obj 0) (w.obj (Fin.last n)) f hsa hr
          exact ⟨⟨⟨w.obj (Fin.last n), hsa⟩, c⟩, (congrArg (fun F => F.app (op ⦋n⦌) c) he).symm.trans hc⟩

end Quiver.FreeGroupoid.OriginalWords
