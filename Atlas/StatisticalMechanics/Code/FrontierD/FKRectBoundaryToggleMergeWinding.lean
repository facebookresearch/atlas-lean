/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKMedialToggleMerge
import Code.FrontierD.FKRectBoundaryToggleWinding



open Equiv Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 800000 in




theorem fkRectBlackBoundaryCycleClassWinding_insert_of_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hdisc : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
    fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R (insert e F)))
        (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) =
      fkRectBlackBoundaryCycleClassWinding R
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R F))
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) +
        fkRectBlackBoundaryCycleClassWinding R
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R F))
          (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) := by
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let v := fkRectMedialVertexOfEdge R e
  let a := fkMedialBlackDart0 v
  let b := fkMedialBlackDart1 v
  let newPairing := fkMedialTogglePairingAt pairing v
  let sigma := fkMedialBlackBoundaryPerm newPairing
  have habne : a ≠ b := fkMedialBlackDart0_ne_dart1 v
  have hnewReach : (fkMedialLoopGraph R.medialTorus newPairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v) :=
    fkMedialLoopGraph_toggle_reachable_of_not_reachable pairing v hdisc
  have hab : sigma.SameCycle a b := by
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable newPairing a b).2
    exact (fkMedialBlackDarts_reachable_iff_west_east newPairing v).2
      hnewReach
  have hsigma : sigma * Equiv.swap a b =
      fkMedialBlackBoundaryPerm pairing := by
    change fkMedialBlackBoundaryPerm newPairing *
        fkMedialBlackDartSwap v = fkMedialBlackBoundaryPerm pairing
    rw [← fkMedialBlackBoundaryPerm_toggle newPairing v]
    simp only [newPairing, fkMedialTogglePairingAt_toggle]
  have hcount : StatMech.FrontierA.permCycleCount
        (sigma * Equiv.swap a b) =
      StatMech.FrontierA.permCycleCount sigma + 1 := by
    rw [hsigma]
    change StatMech.FrontierA.permCycleCount
        (fkMedialBlackBoundaryPerm pairing) =
      StatMech.FrontierA.permCycleCount
        (fkMedialBlackBoundaryPerm newPairing) + 1
    rw [permCycleCount_fkMedialBlackBoundaryPerm,
      permCycleCount_fkMedialBlackBoundaryPerm]
    exact (fkMedialLoopCount_toggle_of_not_reachable
      R.medialTorus pairing v hdisc).symm
  have hweights := permCycleClassWeightSum_split sigma a b habne hab hcount
    (fkRectBlackBoundaryWeight R newPairing)
    (fkRectBlackBoundaryWeight R pairing)
    (fun d hd0 hd1 =>
      (fkRectBlackBoundaryWeight_toggle_of_ne
        R pairing v d hd0 hd1).symm)
    (by
      rw [fkRectBlackBoundaryWeight_toggle_pair_eq_zero R F e heF,
        fkRectBlackBoundaryWeight_closed_dart0_eq_zero R F e heF,
        fkRectBlackBoundaryWeight_closed_dart1_eq_zero R F e heF,
        zero_add])
  rw [hsigma] at hweights
  simpa [fkRectBlackBoundaryCycleClassWinding, pairing, v, a, b,
    newPairing, sigma,
    fkRectConfigurationToMedialPairing_insert R F e heF] using hweights



theorem fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_reachable_away
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hdisc : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (d : FKMedialBlackDart R.medialTorus)
    (hd0 : ¬ (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).SameCycle
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) d)
    (hd1 : ¬ (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).SameCycle
          (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) d) :
    fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F)) d =
      fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R (insert e F))) d := by
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let v := fkRectMedialVertexOfEdge R e
  let a := fkMedialBlackDart0 v
  let b := fkMedialBlackDart1 v
  let newPairing := fkMedialTogglePairingAt pairing v
  let sigma := fkMedialBlackBoundaryPerm newPairing
  have habne : a ≠ b := fkMedialBlackDart0_ne_dart1 v
  have hnewReach : (fkMedialLoopGraph R.medialTorus newPairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v) :=
    fkMedialLoopGraph_toggle_reachable_of_not_reachable pairing v hdisc
  have hab : sigma.SameCycle a b := by
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable
      newPairing a b).2
    exact (fkMedialBlackDarts_reachable_iff_west_east
      newPairing v).2 hnewReach
  have hsigma : sigma * Equiv.swap a b =
      fkMedialBlackBoundaryPerm pairing := by
    change fkMedialBlackBoundaryPerm newPairing *
        fkMedialBlackDartSwap v = fkMedialBlackBoundaryPerm pairing
    rw [← fkMedialBlackBoundaryPerm_toggle newPairing v]
    simp only [newPairing, fkMedialTogglePairingAt_toggle]
  have hcount : StatMech.FrontierA.permCycleCount
        (sigma * Equiv.swap a b) =
      StatMech.FrontierA.permCycleCount sigma + 1 := by
    rw [hsigma]
    change StatMech.FrontierA.permCycleCount
        (fkMedialBlackBoundaryPerm pairing) =
      StatMech.FrontierA.permCycleCount
        (fkMedialBlackBoundaryPerm newPairing) + 1
    rw [permCycleCount_fkMedialBlackBoundaryPerm,
      permCycleCount_fkMedialBlackBoundaryPerm]
    exact (fkMedialLoopCount_toggle_of_not_reachable
      R.medialTorus pairing v hdisc).symm
  have hdnew : ¬ sigma.SameCycle a d := by
    rw [fkMedialBlackBoundaryPerm_toggle_merge_partition pairing v hdisc d]
    exact not_or_intro hd0 hd1
  have hweights := permCycleClassWeightSum_eq_of_not_sameCycle
    sigma a b d habne hab hcount hdnew
    (fkRectBlackBoundaryWeight R newPairing)
    (fkRectBlackBoundaryWeight R pairing)
    (fun x hx0 hx1 => (fkRectBlackBoundaryWeight_toggle_of_ne
      R pairing v x hx0 hx1).symm)
  rw [hsigma] at hweights
  simpa [fkRectBlackBoundaryCycleClassWinding, pairing, v, a, b,
    newPairing, sigma,
    fkRectConfigurationToMedialPairing_insert R F e heF] using hweights.symm

end

end StatMech.FrontierD
