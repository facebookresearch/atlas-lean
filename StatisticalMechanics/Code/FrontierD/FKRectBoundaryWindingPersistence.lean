/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryCycleCompanion
import Code.FrontierD.FKRectBoundaryToggleMergeWinding
import Code.FrontierD.FKRectConnectedInsertionCharge



open Equiv SimpleGraph

namespace StatMech.FrontierD

noncomputable section

private theorem reachable_medialPrimals_of_blackDartLabels
    (R : FKRectTorus) (G : SimpleGraph R.Vertex) (e : R.EdgeIndex)
    (h : G.Reachable
      (fkRectMedialDartPrimalLabel R
        (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1)
      (fkRectMedialDartPrimalLabel R
        (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)).1)) :
    G.Reachable (fkRectMedialWestPrimal R e)
      (fkRectMedialEastPrimal R e) := by
  have hedge :
      s(fkRectMedialDartPrimalLabel R
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1,
        fkRectMedialDartPrimalLabel R
          (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)).1) =
      s(fkRectMedialWestPrimal R e, fkRectMedialEastPrimal R e) := by
    rw [fkRectBlackDart01_primalLabels,
      fkRectTorusMedialEdgeEquiv_vertexOfEdge,
      fkRectTorusIndexedEdge_eq_medialPrimals]
  rcases Sym2.eq_iff.mp hedge with hsame | hswap
  · rw [← hsame.1, ← hsame.2]
    exact h
  · rw [← hswap.2, ← hswap.1]
    exact h.symm



theorem fkRectNonzeroBlackBoundaryWinding_persists_insert
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hnewNoNet : ¬ FKRectHasNet R
      (fkRectConfigurationOfEdges R (insert e F)))
    (d : FKMedialBlackDart R.medialTorus)
    (hdne : fkRectBlackBoundaryCycleClassWinding R
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F)) d ≠ 0) :
    ∃ d' : FKMedialBlackDart R.medialTorus,
      fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R (insert e F))) d' ≠ 0 := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let pairing := fkRectConfigurationToMedialPairing R omega
  let v := fkRectMedialVertexOfEdge R e
  let a := fkMedialBlackDart0 v
  let b := fkMedialBlackDart1 v
  have hold : ¬ FKRectHasNet R omega := by
    intro hnet
    exact hnewNoNet (FKRectHasNet.insert R F e hnet)
  by_cases hmedial : (fkMedialLoopGraph R.medialTorus pairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v)
  · by_cases had : (fkMedialBlackBoundaryPerm pairing).SameCycle a d
    · have hadWeight : fkRectBlackBoundaryCycleClassWinding R pairing a =
          fkRectBlackBoundaryCycleClassWinding R pairing d := by
        exact permCycleClassWeightSum_eq_of_sameCycle
          (fkMedialBlackBoundaryPerm pairing) a d
          (fkRectBlackBoundaryWeight R pairing) had
      have hane : fkRectBlackBoundaryCycleClassWinding R pairing a ≠ 0 := by
        rwa [hadWeight]
      have hsplit :=
        fkRectBlackBoundaryCycleClassWinding_split_of_reachable
          R F e heF hmedial
      by_cases hnewa : fkRectBlackBoundaryCycleClassWinding R
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R (insert e F))) a = 0
      · refine ⟨b, ?_⟩
        intro hnewb
        apply hane
        rw [hsplit, hnewa, hnewb, zero_add]
      · exact ⟨a, hnewa⟩
    · refine ⟨d, ?_⟩
      intro hnewd
      apply hdne
      exact (fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_sameCycle
        R F e heF hmedial d had).trans hnewd
  · by_cases hprimal : (fkRectOpenGraph R omega).Reachable
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)
    · let r := hprimal.some
      have hsurface := fkRectConnectedInsertionSurfaceBridge_unconditional
        R F e r heF hold
      obtain ⟨q, hq⟩ := hsurface.mp hmedial
      exfalso
      apply hnewNoNet
      apply FKRectHasNet_insert_of_independent_fundamentalWalk R F e r q
      simpa only [fkRectInsertedFundamentalWalk_winding] using hq
    · by_cases hd0 : (fkMedialBlackBoundaryPerm pairing).SameCycle a d
      · have haLabel : (fkRectOpenGraph R omega).Reachable
            (fkRectMedialDartPrimalLabel R a.1)
            (fkRectMedialDartPrimalLabel R d.1) :=
          fkRectMedial_reachable_primalLabel_reachable R omega
            ((fkMedial_blackBoundary_sameCycle_iff_reachable
              pairing a d).mp hd0)
        let C : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ d
        have hCcluster :
            fkRectBlackBoundaryCycleInPrimalCluster R omega
              (fkRectMedialDartPrimalLabel R d.1) C := by
          change (fkRectOpenGraph R omega).Reachable
            (fkRectMedialDartPrimalLabel R d.1)
            (fkRectMedialDartPrimalLabel R d.1)
          exact .refl _
        have hCne : fkRectBlackBoundaryCycleWinding R omega C ≠ 0 := by
          simpa [C, omega, pairing] using hdne
        obtain ⟨D, hDC, hDcluster, hDne⟩ :=
          exists_other_nonzero_blackBoundaryCycle_in_primalCluster
            R omega (fkRectMedialDartPrimalLabel R d.1) C
              hCcluster hCne
        induction D using Quot.ind with
        | _ d' =>
          have hdd' : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle d d' := by
            intro hsame
            apply hDC
            apply Quotient.sound
            exact hsame.symm
          have hd'cluster : (fkRectOpenGraph R omega).Reachable
              (fkRectMedialDartPrimalLabel R d.1)
              (fkRectMedialDartPrimalLabel R d'.1) := by
            simpa [omega] using hDcluster
          have hd'ne : fkRectBlackBoundaryCycleClassWinding R pairing d' ≠ 0 := by
            simpa [omega, pairing] using hDne
          have hd'0 : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle a d' := by
            intro ha'
            exact hdd' (hd0.symm.trans ha')
          have hd'1 : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle b d' := by
            intro hb'
            have hbLabel : (fkRectOpenGraph R omega).Reachable
                (fkRectMedialDartPrimalLabel R d'.1)
                (fkRectMedialDartPrimalLabel R b.1) :=
              fkRectMedial_reachable_primalLabel_reachable R omega
                ((fkMedial_blackBoundary_sameCycle_iff_reachable
                  pairing d' b).mp hb'.symm)
            apply hprimal
            apply reachable_medialPrimals_of_blackDartLabels R
              (fkRectOpenGraph R omega) e
            exact haLabel.trans (hd'cluster.trans hbLabel)
          refine ⟨d', ?_⟩
          intro hnew
          apply hd'ne
          exact
            (fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_reachable_away
              R F e heF hmedial d' hd'0 hd'1).trans hnew
      · by_cases hd1 : (fkMedialBlackBoundaryPerm pairing).SameCycle b d
        · have hbLabel : (fkRectOpenGraph R omega).Reachable
              (fkRectMedialDartPrimalLabel R b.1)
              (fkRectMedialDartPrimalLabel R d.1) :=
            fkRectMedial_reachable_primalLabel_reachable R omega
              ((fkMedial_blackBoundary_sameCycle_iff_reachable
                pairing b d).mp hd1)
          let C : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ d
          have hCcluster :
              fkRectBlackBoundaryCycleInPrimalCluster R omega
                (fkRectMedialDartPrimalLabel R d.1) C := by
            change (fkRectOpenGraph R omega).Reachable
              (fkRectMedialDartPrimalLabel R d.1)
              (fkRectMedialDartPrimalLabel R d.1)
            exact .refl _
          have hCne : fkRectBlackBoundaryCycleWinding R omega C ≠ 0 := by
            simpa [C, omega, pairing] using hdne
          obtain ⟨D, hDC, hDcluster, hDne⟩ :=
            exists_other_nonzero_blackBoundaryCycle_in_primalCluster
              R omega (fkRectMedialDartPrimalLabel R d.1) C
                hCcluster hCne
          induction D using Quot.ind with
          | _ d' =>
            have hdd' : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle d d' := by
              intro hsame
              apply hDC
              apply Quotient.sound
              exact hsame.symm
            have hd'cluster : (fkRectOpenGraph R omega).Reachable
                (fkRectMedialDartPrimalLabel R d.1)
                (fkRectMedialDartPrimalLabel R d'.1) := by
              simpa [omega] using hDcluster
            have hd'ne : fkRectBlackBoundaryCycleClassWinding R pairing d' ≠ 0 := by
              simpa [omega, pairing] using hDne
            have hd'1 : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle b d' := by
              intro hb'
              exact hdd' (hd1.symm.trans hb')
            have hd'0 : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle a d' := by
              intro ha'
              have haLabel : (fkRectOpenGraph R omega).Reachable
                  (fkRectMedialDartPrimalLabel R a.1)
                  (fkRectMedialDartPrimalLabel R d'.1) :=
                fkRectMedial_reachable_primalLabel_reachable R omega
                  ((fkMedial_blackBoundary_sameCycle_iff_reachable
                    pairing a d').mp ha')
              apply hprimal
              apply reachable_medialPrimals_of_blackDartLabels R
                (fkRectOpenGraph R omega) e
              exact haLabel.trans (hd'cluster.symm.trans hbLabel.symm)
            refine ⟨d', ?_⟩
            intro hnew
            apply hd'ne
            exact
              (fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_reachable_away
                R F e heF hmedial d' hd'0 hd'1).trans hnew
        · refine ⟨d, ?_⟩
          intro hnewd
          apply hdne
          exact
            (fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_reachable_away
              R F e heF hmedial d hd0 hd1).trans hnewd

end

end StatMech.FrontierD
