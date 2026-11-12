/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectWiredDualBoundarySplice



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section




theorem exists_first_fkRectInsertEdgeList_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (es : List R.EdgeIndex) (x y : R.Vertex)
    (hstart : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable x y)
    (hfinal : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R
        (fkRectInsertEdgeList R F es))).Reachable x y) :
    ∃ pre : List R.EdgeIndex, ∃ e : R.EdgeIndex,
      ∃ post : List R.EdgeIndex,
        es = pre ++ e :: post ∧
        ¬ (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R
            (fkRectInsertEdgeList R F pre))).Reachable x y ∧
        (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R
            (insert e (fkRectInsertEdgeList R F pre)))).Reachable x y := by
  induction es generalizing F with
  | nil =>
      simp only [fkRectInsertEdgeList] at hfinal
      exact False.elim (hstart hfinal)
  | cons e es ih =>
      by_cases hstep : (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R (insert e F))).Reachable x y
      · exact ⟨[], e, es, by simp, by simpa [fkRectInsertEdgeList] using hstart,
          by simpa [fkRectInsertEdgeList] using hstep⟩
      · have hfinal' : (fkRectOpenGraph R
            (fkRectConfigurationOfEdges R
              (fkRectInsertEdgeList R (insert e F) es))).Reachable x y := by
          simpa only [fkRectInsertEdgeList] using hfinal
        obtain ⟨pre, a, post, hlist, hbefore, hafter⟩ :=
          ih (insert e F) hstep hfinal'
        refine ⟨e :: pre, a, post, ?_, ?_, ?_⟩
        · simp only [List.cons_append]
          rw [hlist]
        · simpa only [fkRectInsertEdgeList] using hbefore
        · simpa only [fkRectInsertEdgeList] using hafter




theorem fkRect_firstConnection_fresh_and_medial_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (x y : R.Vertex)
    (hbefore : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable x y)
    (hafter : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R (insert e F))).Reachable x y) :
    e ∉ F ∧
      ¬ (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))).Reachable
            (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
            (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) := by
  let a := fkRectMedialWestPrimal R e
  let b := fkRectMedialEastPrimal R e
  let G := fkRectOpenGraph R (fkRectConfigurationOfEdges R F)
  have hgraph : fkRectOpenGraph R
      (fkRectConfigurationOfEdges R (insert e F)) =
        G ⊔ SimpleGraph.edge a b := by
    exact fkRectOpenGraph_configurationOfEdges_insert R F e
      (fkRectTorusIndexedEdge_eq_medialPrimals R e)
  have hab : ¬ G.Reachable a b := by
    intro hab
    rw [hgraph, StatMech.Lattice.reachable_sup_edge] at hafter
    apply hbefore
    rcases hafter with hxy | hxy | hxy
    · exact hxy
    · exact hxy.1.trans (hab.trans hxy.2)
    · exact hxy.1.trans (hab.symm.trans hxy.2)
  have heF : e ∉ F := by
    intro heF
    apply hab
    exact ((fkRectOpenGraph_configurationOfEdges_adj R F a b).2
      ⟨e, heF, fkRectTorusIndexedEdge_eq_medialPrimals R e⟩).reachable
  refine ⟨heF, ?_⟩
  exact fkRectMedial_west_east_not_reachable_of_endpoints
    R (fkRectConfigurationOfEdges R F) e
      (fkRectTorusIndexedEdge_eq_medialPrimals R e) hab

end

end StatMech.FrontierD
