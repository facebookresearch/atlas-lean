/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectTorusDisjointWinding
import Code.FrontierD.FKRectTorusWindingRankTwoInsertion









open SimpleGraph

namespace StatMech.FrontierD

noncomputable section

theorem fkRectWalkWinding_concat_eq_add_step
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y z : R.Vertex} (p : G.Walk x y) (h : G.Adj y z) :
    fkRectWalkWinding R (p.concat h) =
      fkRectWalkWinding R p + fkRectStepWinding R y z := by
  rw [fkRectWalkWinding_concat]
  rfl


def fkRectGraphClosedWindingSubgroup (R : FKRectTorus)
    (G : SimpleGraph R.Vertex) (x : R.Vertex) :
    AddSubgroup (Int × Int) where
  carrier := {u | ∃ p : G.Walk x x, fkRectWalkWinding R p = u}
  zero_mem' := ⟨.nil, rfl⟩
  add_mem' := by
    rintro u v ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p.append q, fkRectWalkWinding_append R p q⟩
  neg_mem' := by
    rintro u ⟨p, rfl⟩
    exact ⟨p.reverse, fkRectWalkWinding_reverse R p⟩




theorem fkRectWalkWinding_sup_edge_decomposition
    (R : FKRectTorus) (G : SimpleGraph R.Vertex)
    (a b : R.Vertex) (hab : ¬ G.Reachable a b)
    {y : R.Vertex} (p : (G ⊔ SimpleGraph.edge a b).Walk a y) :
    (∃ q : G.Walk a y,
      fkRectWalkWinding R p - fkRectWalkWinding R q ∈
        fkRectGraphClosedWindingSubgroup R G a ⊔
          fkRectGraphClosedWindingSubgroup R G b) ∨
    (∃ q : G.Walk b y,
      fkRectWalkWinding R p - fkRectStepWinding R a b -
          fkRectWalkWinding R q ∈
        fkRectGraphClosedWindingSubgroup R G a ⊔
          fkRectGraphClosedWindingSubgroup R G b) := by
  let S := fkRectGraphClosedWindingSubgroup R G a ⊔
    fkRectGraphClosedWindingSubgroup R G b
  refine SimpleGraph.Walk.concatRec (motive := fun x y p => x = a →
    ((∃ q : G.Walk a y,
      fkRectWalkWinding R p - fkRectWalkWinding R q ∈ S) ∨
    (∃ q : G.Walk b y,
      fkRectWalkWinding R p - fkRectStepWinding R a b -
        fkRectWalkWinding R q ∈ S))) ?_ ?_ p rfl
  · intro x hx
    subst x
    left
    refine ⟨.nil, ?_⟩
    exact AddSubgroup.zero_mem S
  · intro x v w p h ih hx
    have ih := ih hx
    rw [SimpleGraph.sup_adj] at h
    rcases h with hold | hnew
    · rcases ih with ⟨q, hq⟩ | ⟨q, hq⟩
      · left
        refine ⟨q.concat hold, ?_⟩
        rw [fkRectWalkWinding_concat_eq_add_step,
          fkRectWalkWinding_concat_eq_add_step]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hq
      · right
        refine ⟨q.concat hold, ?_⟩
        rw [fkRectWalkWinding_concat_eq_add_step,
          fkRectWalkWinding_concat_eq_add_step]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hq
    · rw [SimpleGraph.edge_adj] at hnew
      rcases hnew.1 with hforward | hreverse
      · rcases hforward with ⟨rfl, rfl⟩
        rcases ih with ⟨q, hq⟩ | ⟨q, hq⟩
        · right
          refine ⟨.nil, ?_⟩
          have hqmem : fkRectWalkWinding R q ∈ S :=
            AddSubgroup.mem_sup_left ⟨q, rfl⟩
          have hsum := AddSubgroup.add_mem S hq hqmem
          rw [fkRectWalkWinding_concat_eq_add_step]
          simpa [sub_eq_add_neg, add_comm, add_left_comm,
            fkRectWalkWinding, Prod.mk_zero_zero] using hsum
        · exact False.elim (hab q.reachable.symm)
      · rcases hreverse with ⟨rfl, rfl⟩
        rcases ih with ⟨q, hq⟩ | ⟨q, hq⟩
        · exact False.elim (hab q.reachable)
        · left
          refine ⟨.nil, ?_⟩
          have hqmem : fkRectWalkWinding R q ∈ S :=
            AddSubgroup.mem_sup_right ⟨q, rfl⟩
          have hsum := AddSubgroup.add_mem S hq hqmem
          rw [fkRectWalkWinding_concat_eq_add_step,
            fkRectStepWinding_swap]
          simpa [sub_eq_add_neg, add_comm, add_left_comm,
            fkRectWalkWinding, Prod.mk_zero_zero] using hsum



theorem fkRectGraphClosedWindingSubgroup_sup_edge_eq
    (R : FKRectTorus) (G : SimpleGraph R.Vertex)
    (a b : R.Vertex) (hab : ¬ G.Reachable a b) :
    fkRectGraphClosedWindingSubgroup R
        (G ⊔ SimpleGraph.edge a b) a =
      fkRectGraphClosedWindingSubgroup R G a ⊔
        fkRectGraphClosedWindingSubgroup R G b := by
  let S := fkRectGraphClosedWindingSubgroup R G a ⊔
    fkRectGraphClosedWindingSubgroup R G b
  apply le_antisymm
  · rintro u ⟨p, rfl⟩
    rcases fkRectWalkWinding_sup_edge_decomposition R G a b hab p with
      ⟨q, hq⟩ | ⟨q, hq⟩
    · have hqmem : fkRectWalkWinding R q ∈ S :=
        AddSubgroup.mem_sup_left ⟨q, rfl⟩
      have hsum := AddSubgroup.add_mem S hq hqmem
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
    · exact False.elim (hab q.reachable.symm)
  · apply sup_le
    · rintro u ⟨p, rfl⟩
      exact ⟨p.mapLe le_sup_left, fkRectWalkWinding_mapLe R le_sup_left p⟩
    · rintro u ⟨p, rfl⟩
      have hne : a ≠ b := by
        intro h
        subst b
        exact hab (SimpleGraph.Reachable.refl a)
      have hedge : (G ⊔ SimpleGraph.edge a b).Adj a b := by
        rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
        exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
      let q := ((SimpleGraph.Walk.cons hedge
        (p.mapLe le_sup_left)).concat hedge.symm)
      refine ⟨q, ?_⟩
      dsimp [q]
      change fkRectStepWinding R a b +
        fkRectWalkWinding R ((p.mapLe le_sup_left).concat hedge.symm) =
          fkRectWalkWinding R p
      rw [fkRectWalkWinding_concat_eq_add_step,
        fkRectWalkWinding_mapLe]
      rw [fkRectStepWinding_swap]
      apply Prod.ext <;> simp

@[simp] theorem fkRectGraphClosedWindingSubgroup_openGraph
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    fkRectGraphClosedWindingSubgroup R (fkRectOpenGraph R omega) x =
      fkRectClosedWindingSubgroup R omega x := by
  rfl



theorem fkRectClosedWindingSubgroup_insert_eq_sup_of_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (hdisc : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)) :
    fkRectClosedWindingSubgroup R
        (fkRectConfigurationOfEdges R (insert e F))
        (fkRectMedialWestPrimal R e) =
      fkRectClosedWindingSubgroup R
          (fkRectConfigurationOfEdges R F)
          (fkRectMedialWestPrimal R e) ⊔
        fkRectClosedWindingSubgroup R
          (fkRectConfigurationOfEdges R F)
          (fkRectMedialEastPrimal R e) := by
  let G := fkRectOpenGraph R (fkRectConfigurationOfEdges R F)
  let a := fkRectMedialWestPrimal R e
  let b := fkRectMedialEastPrimal R e
  have hgraph : fkRectOpenGraph R
      (fkRectConfigurationOfEdges R (insert e F)) =
        G ⊔ SimpleGraph.edge a b :=
    fkRectOpenGraph_configurationOfEdges_insert R F e
      (fkRectTorusIndexedEdge_eq_medialPrimals R e)
  change fkRectGraphClosedWindingSubgroup R
      (fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e F))) a =
    fkRectGraphClosedWindingSubgroup R G a ⊔
      fkRectGraphClosedWindingSubgroup R G b
  rw [hgraph]
  exact fkRectGraphClosedWindingSubgroup_sup_edge_eq R G a b hdisc



theorem fkRectWalkWinding_sup_edge_eq_old_of_not_reachable
    (R : FKRectTorus) (G : SimpleGraph R.Vertex) (a b : R.Vertex)
    {x y : R.Vertex} (hxa : ¬ G.Reachable x a)
    (hxb : ¬ G.Reachable x b)
    (p : (G ⊔ SimpleGraph.edge a b).Walk x y) :
    ∃ q : G.Walk x y, fkRectWalkWinding R p = fkRectWalkWinding R q := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons u v w huv p ih =>
      rw [SimpleGraph.sup_adj] at huv
      rcases huv with hold | hnew
      · have hva : ¬ G.Reachable v a := by
          intro h
          exact hxa (hold.reachable.trans h)
        have hvb : ¬ G.Reachable v b := by
          intro h
          exact hxb (hold.reachable.trans h)
        obtain ⟨q, hq⟩ := ih hva hvb
        refine ⟨.cons hold q, ?_⟩
        simp only [fkRectWalkWinding]
        rw [hq]
      · rw [SimpleGraph.edge_adj] at hnew
        rcases hnew.1 with hforward | hreverse
        · rcases hforward with ⟨rfl, rfl⟩
          exact False.elim (hxa (SimpleGraph.Reachable.refl _))
        · rcases hreverse with ⟨rfl, rfl⟩
          exact False.elim (hxb (SimpleGraph.Reachable.refl _))



theorem fkRectGraphClosedWindingSubgroup_sup_edge_eq_of_away
    (R : FKRectTorus) (G : SimpleGraph R.Vertex) (a b x : R.Vertex)
    (hxa : ¬ G.Reachable x a) (hxb : ¬ G.Reachable x b) :
    fkRectGraphClosedWindingSubgroup R
        (G ⊔ SimpleGraph.edge a b) x =
      fkRectGraphClosedWindingSubgroup R G x := by
  apply le_antisymm
  · rintro u ⟨p, rfl⟩
    obtain ⟨q, hq⟩ :=
      fkRectWalkWinding_sup_edge_eq_old_of_not_reachable
        R G a b hxa hxb p
    exact ⟨q, hq.symm⟩
  · rintro u ⟨p, rfl⟩
    exact ⟨p.mapLe le_sup_left, fkRectWalkWinding_mapLe R le_sup_left p⟩



theorem fkRectClosedWindingSubgroup_insert_eq_of_away
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (x : R.Vertex)
    (hxa : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable x
        (fkRectMedialWestPrimal R e))
    (hxb : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable x
        (fkRectMedialEastPrimal R e)) :
    fkRectClosedWindingSubgroup R
        (fkRectConfigurationOfEdges R (insert e F)) x =
      fkRectClosedWindingSubgroup R
        (fkRectConfigurationOfEdges R F) x := by
  let G := fkRectOpenGraph R (fkRectConfigurationOfEdges R F)
  let a := fkRectMedialWestPrimal R e
  let b := fkRectMedialEastPrimal R e
  have hgraph : fkRectOpenGraph R
      (fkRectConfigurationOfEdges R (insert e F)) =
        G ⊔ SimpleGraph.edge a b :=
    fkRectOpenGraph_configurationOfEdges_insert R F e
      (fkRectTorusIndexedEdge_eq_medialPrimals R e)
  change fkRectGraphClosedWindingSubgroup R
      (fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e F))) x =
    fkRectGraphClosedWindingSubgroup R G x
  rw [hgraph]
  exact fkRectGraphClosedWindingSubgroup_sup_edge_eq_of_away
    R G a b x hxa hxb



theorem not_fkRectHasNet_insert_of_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
    (hdisc : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)) :
    ¬ FKRectHasNet R
      (fkRectConfigurationOfEdges R (insert e F)) := by
  let omega := fkRectConfigurationOfEdges R F
  let tau := fkRectConfigurationOfEdges R (insert e F)
  let a := fkRectMedialWestPrimal R e
  let b := fkRectMedialEastPrimal R e
  have hOldNoRank (x : R.Vertex) :
      ¬ FKRectWindingSubgroupRankTwo R omega x := by
    intro hx
    exact hold <| (fkRectHasNet_iff_exists_windingSubgroup_rankTwo R omega).2
      ⟨x, hx⟩
  have hcross : ∀ u ∈ fkRectClosedWindingSubgroup R omega a,
      ∀ v ∈ fkRectClosedWindingSubgroup R omega b,
        ¬ FKRectWindingIndependent u v :=
    fkRectClosedWindingSubgroup_cross_dependent R omega hdisc
  have hsup : ¬ ∃ u ∈
      fkRectClosedWindingSubgroup R omega a ⊔
        fkRectClosedWindingSubgroup R omega b,
      ∃ v ∈ fkRectClosedWindingSubgroup R omega a ⊔
        fkRectClosedWindingSubgroup R omega b,
        FKRectWindingIndependent u v := by
    apply windingSubgroup_sup_not_rankTwo_of_pairwise_dependent
    · simpa [FKRectWindingSubgroupRankTwo] using hOldNoRank a
    · simpa [FKRectWindingSubgroupRankTwo] using hOldNoRank b
    · exact hcross
  have hsubgroup : fkRectClosedWindingSubgroup R tau a =
      fkRectClosedWindingSubgroup R omega a ⊔
        fkRectClosedWindingSubgroup R omega b := by
    exact fkRectClosedWindingSubgroup_insert_eq_sup_of_not_reachable
      R F e hdisc
  have hNewNoRankA : ¬ FKRectWindingSubgroupRankTwo R tau a := by
    unfold FKRectWindingSubgroupRankTwo
    rw [hsubgroup]
    exact hsup
  intro hnet
  obtain ⟨x, hx⟩ :=
    (fkRectHasNet_iff_exists_windingSubgroup_rankTwo R tau).1 hnet
  by_cases hxa : (fkRectOpenGraph R omega).Reachable x a
  · have hxa' := hxa.mono (fkRectOpenGraph_le_insert R F e)
    exact hNewNoRankA
      ((fkRectWindingSubgroupRankTwo_iff_of_reachable R tau hxa').mp hx)
  · by_cases hxb : (fkRectOpenGraph R omega).Reachable x b
    · have hxb' := hxb.mono (fkRectOpenGraph_le_insert R F e)
      have hba : (fkRectOpenGraph R tau).Reachable b a :=
        (fkRectOpenGraph_insert_adj_medialPrimals R F e).reachable
      have hxa' := hxb'.trans hba
      exact hNewNoRankA
        ((fkRectWindingSubgroupRankTwo_iff_of_reachable R tau hxa').mp hx)
    · have haway := fkRectClosedWindingSubgroup_insert_eq_of_away
        R F e x hxa hxb
      have hxold : FKRectWindingSubgroupRankTwo R omega x := by
        unfold FKRectWindingSubgroupRankTwo at hx ⊢
        rwa [haway] at hx
      exact hOldNoRank x hxold



theorem fkRectHasNet_insert_iff_of_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (hdisc : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)) :
    FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) ↔
      FKRectHasNet R (fkRectConfigurationOfEdges R F) := by
  constructor
  · intro hnew
    by_contra hold
    exact (not_fkRectHasNet_insert_of_not_reachable R F e hold hdisc) hnew
  · exact FKRectHasNet.insert R F e

end

end StatMech.FrontierD
