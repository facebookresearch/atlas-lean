/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusWindingSubgroup
import Code.FrontierD.FKRectEulerDefectLocalCriterion

open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem fkRectClosedWindingSubgroup_mono_configurationOfEdges
    (R : FKRectTorus) {F A : Finset R.EdgeIndex} (hFA : F ⊆ A)
    (x : R.Vertex) :
    fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F) x ≤
      fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R A) x := by
  rintro u ⟨p, rfl⟩
  have hgraph : fkRectOpenGraph R (fkRectConfigurationOfEdges R F) ≤
      fkRectOpenGraph R (fkRectConfigurationOfEdges R A) := by
    apply fkRectOpenGraph_mono R
    intro e he
    rw [fkRectConfigurationOfEdges_apply] at he ⊢
    exact hFA he
  exact ⟨p.mapLe hgraph, fkRectWalkWinding_mapLe R hgraph p⟩


theorem fkRectOpenGraph_le_insert
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    fkRectOpenGraph R (fkRectConfigurationOfEdges R F) ≤
      fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e F)) := by
  apply fkRectOpenGraph_mono R
  intro a ha
  rw [fkRectConfigurationOfEdges_apply] at ha ⊢
  exact Finset.mem_insert_of_mem ha



theorem fkRectOpenGraph_insert_adj_medialPrimals
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R (insert e F))).Adj
        (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e) := by
  rw [fkRectOpenGraph_configurationOfEdges_insert R F e
    (fkRectTorusIndexedEdge_eq_medialPrimals R e)]
  right
  rw [SimpleGraph.edge_adj]
  have hne : fkRectMedialWestPrimal R e ≠
      fkRectMedialEastPrimal R e := by
    intro h
    apply fkRectTorusIndexedEdge_ne_diag R e
      (fkRectMedialWestPrimal R e)
    simpa [h] using fkRectTorusIndexedEdge_eq_medialPrimals R e
  exact ⟨Or.inr ⟨rfl, rfl⟩, hne.symm⟩



noncomputable def fkRectInsertedFundamentalWalk
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (p : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)) :
    (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R (insert e F))).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e) :=
  (p.mapLe (fkRectOpenGraph_le_insert R F e)).concat
    (fkRectOpenGraph_insert_adj_medialPrimals R F e)


theorem fkRectInsertedFundamentalWalk_winding
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (p : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)) :
    fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e p) =
      ((fkRectWalkWinding R p).1 +
          fkRectHorizontalSeamIncrement R
            (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e),
        (fkRectWalkWinding R p).2 +
          fkRectVerticalSeamIncrement R
            (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e)) := by
  unfold fkRectInsertedFundamentalWalk
  rw [SimpleGraph.Walk.concat_eq_append, fkRectWalkWinding_append,
    fkRectWalkWinding_mapLe]
  simp [fkRectWalkWinding]



theorem FKRectHasNet_insert_of_independent_fundamentalWalk
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (p : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (q : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e))
    (hind : FKRectWindingIndependent (fkRectWalkWinding R q)
      ((fkRectWalkWinding R p).1 +
          fkRectHorizontalSeamIncrement R
            (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e),
        (fkRectWalkWinding R p).2 +
          fkRectVerticalSeamIncrement R
            (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e))) :
    FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) := by
  let hgraph := fkRectOpenGraph_le_insert R F e
  refine ⟨fkRectMedialWestPrimal R e, q.mapLe hgraph,
    fkRectInsertedFundamentalWalk R F e p, ?_⟩
  rw [fkRectWalkWinding_mapLe,
    fkRectInsertedFundamentalWalk_winding]
  exact hind

end

end StatMech.FrontierD
