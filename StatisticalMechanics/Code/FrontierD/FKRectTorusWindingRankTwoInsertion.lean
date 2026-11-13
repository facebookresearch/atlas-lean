/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectTorusWindingGeneration









open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section




theorem fkRectClosedWindingSubgroup_insert_eq_sup_zmultiples
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)) :
    fkRectClosedWindingSubgroup R
        (fkRectConfigurationOfEdges R (insert e F))
        (fkRectMedialWestPrimal R e) =
      fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F)
          (fkRectMedialWestPrimal R e) ⊔
        AddSubgroup.zmultiples (fkRectWalkWinding R
          (fkRectInsertedFundamentalWalk R F e r)) := by
  apply le_antisymm
  · exact fkRectClosedWindingSubgroup_insert_le_sup_zmultiples R F e r
  · apply sup_le
    · exact fkRectClosedWindingSubgroup_mono_configurationOfEdges R
        (Finset.subset_insert e F) (fkRectMedialWestPrimal R e)
    · rw [AddSubgroup.zmultiples_le]
      exact ⟨fkRectInsertedFundamentalWalk R F e r, rfl⟩



theorem windingRankTwo_sup_zmultiples_iff_of_not_rankTwo
    (H : AddSubgroup (Int × Int)) (v : Int × Int)
    (hH : ¬ ∃ x ∈ H, ∃ y ∈ H, FKRectWindingIndependent x y) :
    (∃ a ∈ H ⊔ AddSubgroup.zmultiples v,
        ∃ b ∈ H ⊔ AddSubgroup.zmultiples v,
          FKRectWindingIndependent a b) ↔
      ∃ x ∈ H, FKRectWindingIndependent x v := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [AddSubgroup.mem_sup] at ha hb
    obtain ⟨x, hx, av, hav, rfl⟩ := ha
    obtain ⟨y, hy, bv, hbv, rfl⟩ := hb
    rw [AddSubgroup.mem_zmultiples_iff] at hav hbv
    obtain ⟨n, rfl⟩ := hav
    obtain ⟨m, rfl⟩ := hbv
    by_contra hind
    push Not at hind
    have hxy : ¬ FKRectWindingIndependent x y := by
      intro h
      exact hH ⟨x, hx, y, hy, h⟩
    have hxv := hind x hx
    have hyv := hind y hy
    unfold FKRectWindingIndependent at hab hxy hxv hyv
    simp only [Prod.fst_add, Prod.snd_add, zsmul_eq_mul,
      Prod.fst_mul, Prod.snd_mul,
      Prod.fst_intCast, Prod.snd_intCast, Int.cast_id] at hab
    simp only [not_ne_iff] at hxy hxv hyv
    apply hab
    linear_combination hxy + m * hxv - n * hyv
  · rintro ⟨x, hx, hxv⟩
    refine ⟨x, AddSubgroup.mem_sup.mpr ⟨x, hx, 0,
      AddSubgroup.zero_mem _, add_zero x⟩, v, ?_, hxv⟩
    exact AddSubgroup.mem_sup.mpr ⟨0, AddSubgroup.zero_mem _, v,
      AddSubgroup.mem_zmultiples v, zero_add v⟩




theorem fkRectWindingSubgroupRankTwo_insert_iff
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (hold : ¬ FKRectWindingSubgroupRankTwo R
      (fkRectConfigurationOfEdges R F) (fkRectMedialWestPrimal R e)) :
    FKRectWindingSubgroupRankTwo R
        (fkRectConfigurationOfEdges R (insert e F))
        (fkRectMedialWestPrimal R e) ↔
      ∃ q : (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R F)).Walk
            (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e),
        FKRectWindingIndependent (fkRectWalkWinding R q)
          (fkRectWalkWinding R
            (fkRectInsertedFundamentalWalk R F e r)) := by
  let H := fkRectClosedWindingSubgroup R
    (fkRectConfigurationOfEdges R F) (fkRectMedialWestPrimal R e)
  let v := fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)
  have hH : ¬ ∃ x ∈ H, ∃ y ∈ H,
      FKRectWindingIndependent x y := by
    simpa only [H, FKRectWindingSubgroupRankTwo] using hold
  rw [FKRectWindingSubgroupRankTwo,
    fkRectClosedWindingSubgroup_insert_eq_sup_zmultiples R F e r]
  rw [windingRankTwo_sup_zmultiples_iff_of_not_rankTwo H v hH]
  constructor
  · rintro ⟨x, ⟨q, rfl⟩, hxv⟩
    exact ⟨q, hxv⟩
  · rintro ⟨q, hq⟩
    exact ⟨fkRectWalkWinding R q, ⟨q, rfl⟩, hq⟩




theorem fkRectWalkWinding_insert_eq_old_of_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    {x y : R.Vertex}
    (hxa : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable x
        (fkRectMedialWestPrimal R e))
    (p : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R (insert e F))).Walk x y) :
    ∃ q : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Walk x y,
      fkRectWalkWinding R p = fkRectWalkWinding R q := by
  let G := fkRectOpenGraph R (fkRectConfigurationOfEdges R F)
  let H := fkRectOpenGraph R
    (fkRectConfigurationOfEdges R (insert e F))
  let a := fkRectMedialWestPrimal R e
  let b := fkRectMedialEastPrimal R e
  have hab : fkRectTorusIndexedEdge R e = s(a, b) :=
    fkRectTorusIndexedEdge_eq_medialPrimals R e
  have hgraph : H = G ⊔ SimpleGraph.edge a b :=
    fkRectOpenGraph_configurationOfEdges_insert R F e hab
  have habReach : G.Reachable a b := ⟨r⟩
  change ¬ G.Reachable x a at hxa
  change H.Walk x y at p
  induction p with
  | nil =>
      exact ⟨.nil, rfl⟩
  | @cons u v w huv p ih =>
      have huv' : (G ⊔ SimpleGraph.edge a b).Adj u v := by
        rw [← hgraph]
        exact huv
      rw [SimpleGraph.sup_adj] at huv'
      rcases huv' with hold | hnew
      · have hva : ¬ G.Reachable v a := by
          intro h
          exact hxa (hold.reachable.trans h)
        obtain ⟨q, hq⟩ := ih hva
        refine ⟨.cons hold q, ?_⟩
        simp only [fkRectWalkWinding]
        rw [hq]
      · rw [SimpleGraph.edge_adj] at hnew
        rcases hnew.1 with hforward | hreverse
        · rcases hforward with ⟨rfl, rfl⟩
          exact False.elim (hxa
            (show G.Reachable a a from SimpleGraph.Reachable.refl a))
        · rcases hreverse with ⟨rfl, rfl⟩
          exact False.elim (hxa habReach.symm)



theorem fkRectClosedWindingSubgroup_insert_eq_of_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (x : R.Vertex)
    (hxa : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable x
        (fkRectMedialWestPrimal R e)) :
    fkRectClosedWindingSubgroup R
        (fkRectConfigurationOfEdges R (insert e F)) x =
      fkRectClosedWindingSubgroup R
        (fkRectConfigurationOfEdges R F) x := by
  apply le_antisymm
  · rintro w ⟨p, rfl⟩
    obtain ⟨q, hq⟩ :=
      fkRectWalkWinding_insert_eq_old_of_not_reachable R F e r hxa p
    exact ⟨q, hq.symm⟩
  · exact fkRectClosedWindingSubgroup_mono_configurationOfEdges R
      (Finset.subset_insert e F) x



theorem fkRectHasNet_insert_iff_rankTwo_at_endpoint
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
    FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) ↔
      FKRectWindingSubgroupRankTwo R
        (fkRectConfigurationOfEdges R (insert e F))
        (fkRectMedialWestPrimal R e) := by
  constructor
  · intro hnet
    obtain ⟨x, hx⟩ :=
      (fkRectHasNet_iff_exists_windingSubgroup_rankTwo R _).1 hnet
    by_cases hxa : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Reachable x
          (fkRectMedialWestPrimal R e)
    · have hxa' := hxa.mono (fkRectOpenGraph_le_insert R F e)
      exact (fkRectWindingSubgroupRankTwo_iff_of_reachable R _ hxa').1 hx
    · have hsubgroup :=
        fkRectClosedWindingSubgroup_insert_eq_of_not_reachable
          R F e r x hxa
      have hxold : FKRectWindingSubgroupRankTwo R
          (fkRectConfigurationOfEdges R F) x := by
        unfold FKRectWindingSubgroupRankTwo at hx ⊢
        rwa [hsubgroup] at hx
      exact False.elim <| hold <|
        (fkRectHasNet_iff_exists_windingSubgroup_rankTwo R _).2 ⟨x, hxold⟩
  · intro h
    exact (fkRectHasNet_iff_exists_windingSubgroup_rankTwo R _).2
      ⟨fkRectMedialWestPrimal R e, h⟩



theorem fkRectHasNet_insert_iff_exists_independent_fundamentalWalk
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
    FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) ↔
      ∃ q : (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R F)).Walk
            (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e),
        FKRectWindingIndependent (fkRectWalkWinding R q)
          (fkRectWalkWinding R
            (fkRectInsertedFundamentalWalk R F e r)) := by
  rw [fkRectHasNet_insert_iff_rankTwo_at_endpoint R F e r hold]
  apply fkRectWindingSubgroupRankTwo_insert_iff R F e r
  intro h
  exact hold <| (fkRectHasNet_iff_exists_windingSubgroup_rankTwo R _).2
    ⟨fkRectMedialWestPrimal R e, h⟩

end

end StatMech.FrontierD
