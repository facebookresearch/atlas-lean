/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryWindingPersistence
import Code.FrontierD.FKRectFirstEssentialInsertion
import Code.FrontierD.FKRectTorusDisconnectedInsertion



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section






theorem exists_nonzero_blackBoundaryWinding_of_closedWalk_of_not_hasNet
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (x : R.Vertex)
    (q : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk x x)
    (hnoNet : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
    (hqne : fkRectWalkWinding R q ≠ (0, 0)) :
    ∃ d : FKMedialBlackDart R.medialTorus,
      fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F)) d ≠ 0 := by
  classical
  induction F using Finset.induction_on generalizing x with
  | empty =>
      exact (hqne (fkRectWalkWinding_empty R q)).elim
  | @insert e F heF ih =>
      let old := fkRectConfigurationOfEdges R F
      let new := fkRectConfigurationOfEdges R (insert e F)
      have holdNoNet : ¬ FKRectHasNet R old := by
        intro hnet
        exact hnoNet (FKRectHasNet.insert R F e hnet)
      by_cases holdEssential : ∃ (y : R.Vertex)
          (p : (fkRectOpenGraph R old).Walk y y),
          fkRectWalkWinding R p ≠ (0, 0)
      · obtain ⟨y, p, hpne⟩ := holdEssential
        obtain ⟨d, hdne⟩ := ih y p holdNoNet hpne
        exact fkRectNonzeroBlackBoundaryWinding_persists_insert
          R F e heF hnoNet d hdne
      · push Not at holdEssential
        have htrivial : ∀ (y : R.Vertex)
            (p : (fkRectOpenGraph R old).Walk y y),
            fkRectWalkWinding R p = (0, 0) := holdEssential
        have hconnected : (fkRectOpenGraph R old).Reachable
            (fkRectMedialWestPrimal R e)
            (fkRectMedialEastPrimal R e) := by
          by_contra hdisc
          have hzero_of_reachable
              (hwx : (fkRectOpenGraph R new).Reachable
                (fkRectMedialWestPrimal R e) x) :
              fkRectWalkWinding R q = (0, 0) := by
            have hsub := fkRectClosedWindingSubgroup_eq_of_reachable
              R new hwx
            have hmem : fkRectWalkWinding R q ∈
                fkRectClosedWindingSubgroup R new x := ⟨q, rfl⟩
            rw [← hsub,
              fkRectClosedWindingSubgroup_insert_eq_sup_of_not_reachable
                R F e hdisc,
              AddSubgroup.mem_sup] at hmem
            obtain ⟨u, ⟨pu, hpu⟩, z, ⟨pz, hpz⟩, huz⟩ := hmem
            have hu : u = (0, 0) := by
              rw [← hpu]
              exact htrivial _ pu
            have hz : z = (0, 0) := by
              rw [← hpz]
              exact htrivial _ pz
            rw [hu, hz] at huz
            apply Prod.ext
            · have h := congrArg Prod.fst huz
              simpa using h.symm
            · have h := congrArg Prod.snd huz
              simpa using h.symm
          by_cases hxw : (fkRectOpenGraph R old).Reachable x
              (fkRectMedialWestPrimal R e)
          · apply hqne
            apply hzero_of_reachable
            exact hxw.symm.mono (fkRectOpenGraph_le_insert R F e)
          · by_cases hxe : (fkRectOpenGraph R old).Reachable x
                (fkRectMedialEastPrimal R e)
            · apply hqne
              apply hzero_of_reachable
              exact (fkRectOpenGraph_insert_adj_medialPrimals R F e).symm.reachable.trans
                (hxe.symm.mono (fkRectOpenGraph_le_insert R F e))
            · have hsub := fkRectClosedWindingSubgroup_insert_eq_of_away
                R F e x hxw hxe
              have hmem : fkRectWalkWinding R q ∈
                  fkRectClosedWindingSubgroup R new x := ⟨q, rfl⟩
              rw [hsub] at hmem
              obtain ⟨p, hp⟩ := hmem
              apply hqne
              exact hp.symm.trans (htrivial _ p)
        let r := hconnected.some
        have hfund : fkRectWalkWinding R
            (fkRectInsertedFundamentalWalk R F e r) ≠ (0, 0) := by
          obtain ⟨p, hp⟩ :=
            fkRectWalkWinding_insert_eq_old_add_charge R F e r heF q
          intro hzero
          apply hqne
          rw [htrivial _ p, hzero] at hp
          simpa using hp
        let d := fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)
        have horbit :=
          fkRectFirstEssentialInsertion_newBoundaryOrbit_ne_zero
            R F e r heF holdNoNet htrivial hfund
        refine ⟨d, ?_⟩
        intro hdzero
        apply horbit
        rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_visitCount_nsmul,
          fkRectBoundaryCycleClassWinding_eq_black, hdzero,
          nsmul_zero]
        rfl

end

end StatMech.FrontierD
