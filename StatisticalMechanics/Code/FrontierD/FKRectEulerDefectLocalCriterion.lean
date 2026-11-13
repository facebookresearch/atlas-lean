/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectEulerDefectTransitions
import Code.FrontierD.FKMedialToggleExact

open Finset

namespace StatMech.FrontierD

noncomputable section



theorem fkRectMedialLoopCount_insert_of_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hconn : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
    fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) + 1 =
      fkRectMedialLoopCount R
        (fkRectConfigurationOfEdges R (insert e F)) := by
  have hpair := fkRectConfigurationToMedialPairing_insert R F e heF
  have hcount := fkMedialLoopCount_toggle_of_reachable R.medialTorus
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F))
    (fkRectMedialVertexOfEdge R e) hconn
  unfold fkRectMedialLoopCount
  rwa [hpair]



theorem fkRectMedialLoopCount_insert_of_medial_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hdisc : ¬(fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
    fkRectMedialLoopCount R
        (fkRectConfigurationOfEdges R (insert e F)) + 1 =
      fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) := by
  have hpair := fkRectConfigurationToMedialPairing_insert R F e heF
  have hcount := fkMedialLoopCount_toggle_of_not_reachable R.medialTorus
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F))
    (fkRectMedialVertexOfEdge R e) hdisc
  unfold fkRectMedialLoopCount
  rwa [hpair]




theorem fkRectEulerHomologyDefect_insert_eq_add_two_iff
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) :
    fkRectEulerHomologyDefect R
        (fkRectConfigurationOfEdges R (insert e F)) =
        fkRectEulerHomologyDefect R
          (fkRectConfigurationOfEdges R F) + 2 <->
      (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Reachable
          (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) ∧
      ¬(fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))).Reachable
            (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
            (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) := by
  let omega := fkRectConfigurationOfEdges R F
  have hedge := fkRectTorusIndexedEdge_eq_medialPrimals R e
  constructor
  · intro hjump
    have hpq : (fkRectOpenGraph R omega).Reachable
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) := by
      by_contra hdisc
      have hzero := fkRectEulerHomologyDefect_insert_of_not_reachable
        R F e heF hedge hdisc
      rw [hzero] at hjump
      omega
    refine ⟨hpq, ?_⟩
    intro hmedial
    have hk := fkRectFinsetClusterCount_insert_of_reachable
      R F e hedge hpq
    have hl := fkRectMedialLoopCount_insert_of_reachable
      R F e heF hmedial
    rw [fkRectEulerHomologyDefect_configurationOfEdges,
      fkRectEulerHomologyDefect_configurationOfEdges,
      Finset.card_insert_of_notMem heF, hk] at hjump
    push_cast at hjump
    omega
  · rintro ⟨hpq, hmedial⟩
    have hk := fkRectFinsetClusterCount_insert_of_reachable
      R F e hedge hpq
    have hl := fkRectMedialLoopCount_insert_of_medial_not_reachable
      R F e heF hmedial
    rw [fkRectEulerHomologyDefect_configurationOfEdges,
      fkRectEulerHomologyDefect_configurationOfEdges,
      Finset.card_insert_of_notMem heF, hk]
    push_cast
    omega

end

end StatMech.FrontierD
