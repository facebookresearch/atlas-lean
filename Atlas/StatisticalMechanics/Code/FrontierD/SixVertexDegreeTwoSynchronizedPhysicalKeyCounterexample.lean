/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey
import Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample










namespace StatMech.FrontierD

theorem sixVertexFourByTwo_locallyDegreeTwo :
    SixVertexLocallyDegreeTwo sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows := by
  intro v
  right
  rw [card_sixVertexLocalDisagreementSides]
  exact sixVertexFourByTwo_localDisagreementDegree_two v

def sixVertexFourByTwoOrientedSeed :
    SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows :=
  ⟨⟨(sixVertexFourByTwoVertex 0 0, (1 : Fin 4)), by
      change sixVertexTorusEdgeDisagrees _ _
        (sixVertexTorusIncidentEdge sixVertexFourByTwoTorus
          (sixVertexFourByTwoVertex 0 0) (1 : Fin 4))
      rw [← sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
      decide +revert⟩,
    by decide +revert⟩

noncomputable def sixVertexFourByTwoSynchronizedSeedComponent :=
  (sixVertexDegreeTwoSynchronizedGraph
    sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
    sixVertexFourByTwo_locallyDegreeTwo).connectedComponentMk
      sixVertexFourByTwoOrientedSeed

set_option maxHeartbeats 2000000 in
theorem sixVertexFourByTwoAlignedPairings_false
    (d : SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows) :
    let retie := orientedDartAlignedRetie
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo d
    retie.pairingP = false ∧ retie.pairingQ = false := by
  let retie := orientedDartAlignedRetie
    sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
    sixVertexFourByTwo_locallyDegreeTwo d
  have hP := retie.compatibleP
  have hQ := retie.compatibleQ
  have hpartner := retie.partnerDisagrees
  have hside := sixVertexDisagreementDart_side_mem d.1
  rw [mem_sixVertexLocalDisagreementSides] at hside
  rcases d with ⟨⟨⟨⟨x, y⟩, side⟩, hdisagree⟩, hincoming⟩
  fin_cases x <;> fin_cases y <;> fin_cases side <;>
    cases hp : retie.pairingP <;> cases hq : retie.pairingQ
  all_goals
    first
    | exact ⟨hp, hq⟩
    | simp_all [retie, compatible, localMate, sixVertexLocalIncomingPattern,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, sixVertexFourByTwoLowArrows,
      sixVertexFourByTwoHighArrows, sixVertexFourByTwoTorus,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred]

theorem sixVertexFourByTwoAlignedRoutingPairing_false
    (layer : Bool) (v : sixVertexFourByTwoTorus.Vertex) :
    alignedRoutingPairing sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo layer v = false := by
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern sixVertexFourByTwoLowArrows v)
      (sixVertexLocalIncomingPattern sixVertexFourByTwoHighArrows v)).card = 2 := by
    rw [card_sixVertexLocalDisagreementSides]
    exact sixVertexFourByTwo_localDisagreementDegree_two v
  rw [alignedRoutingPairing_eq_at_active
    sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
    sixVertexFourByTwo_locallyDegreeTwo layer v hactive]
  dsimp only
  obtain ⟨hP, hQ⟩ := sixVertexFourByTwoAlignedPairings_false
    (orientedDisagreementDartAtActiveVertex
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice v
      hactive)
  cases layer <;> simp [hP, hQ]

theorem sixVertexFourByTwoAlignedRoutingPairing_false_funext (layer : Bool) :
    alignedRoutingPairing sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo layer = fun _ => false := by
  funext v
  exact sixVertexFourByTwoAlignedRoutingPairing_false layer v

def sixVertexFourByTwoOrientedNorthSeed :
    SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows :=
  ⟨⟨(sixVertexFourByTwoVertex 0 1, (3 : Fin 4)), by
      change sixVertexTorusEdgeDisagrees _ _
        (sixVertexTorusIncidentEdge sixVertexFourByTwoTorus
          (sixVertexFourByTwoVertex 0 1) (3 : Fin 4))
      rw [← sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
      decide +revert⟩,
    by decide +revert⟩

def sixVertexFourByTwoOrientedEastSeed :
    SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows :=
  ⟨⟨(sixVertexFourByTwoVertex 1 0, (3 : Fin 4)), by
      change sixVertexTorusEdgeDisagrees _ _
        (sixVertexTorusIncidentEdge sixVertexFourByTwoTorus
          (sixVertexFourByTwoVertex 1 0) (3 : Fin 4))
      rw [← sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
      decide +revert⟩,
    by decide +revert⟩

theorem finiteFirstReturn_eq_step_of_selected_step
    {A : Type*} [Fintype A] [DecidableEq A]
    (sigma : Equiv.Perm A) (selected : A → Prop) [DecidablePred selected]
    (x : {a : A // selected a}) (hstep : selected (sigma x.1)) :
    (finiteFirstReturn sigma selected x).1 = sigma x.1 := by
  have htime : finiteFirstReturnTime sigma selected x = 1 := by
    unfold finiteFirstReturnTime
    rw [Nat.find_eq_iff]
    constructor
    · simpa using hstep
    · intro n hn
      omega
  simp [finiteFirstReturn, htime]

theorem doubledAlignedFirstReturnPerm_eq_of_boundary_step
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x y : DoubledAlignedState omega eta)
    (hstep : alignedBoundaryPerm homega heta hdegree false
      (doubledAlignedBlackDart homega heta hdegree false x) =
        doubledAlignedBlackDart homega heta hdegree false y) :
    doubledAlignedFirstReturnPerm homega heta hdegree x = y := by
  apply (doubledAlignedBlackDartEquiv homega heta hdegree false).injective
  rw [doubledAlignedFirstReturnPerm_false_arrival]
  apply Subtype.ext
  rw [finiteFirstReturn_eq_step_of_selected_step]
  · exact hstep
  · change activeBlackDart
      (alignedBoundaryPerm homega heta hdegree false
        (doubledAlignedBlackDart homega heta hdegree false x))
    rw [hstep]
    simpa [activeBlackDart, doubledAlignedBlackDart, doubledAlignedVertex] using
      sixVertexDisagreementDart_local_card_eq_two hdegree y.1.1

set_option maxHeartbeats 1000000 in
theorem sixVertexFourByTwoAlignedBoundary_seed_step (branch : Bool) :
    alignedBoundaryPerm sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false
        (doubledAlignedBlackDart sixVertexFourByTwoLowArrows_ice
          sixVertexFourByTwoHighArrows_ice
          sixVertexFourByTwo_locallyDegreeTwo false
          (sixVertexFourByTwoOrientedSeed, branch)) =
      doubledAlignedBlackDart sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false
        (sixVertexFourByTwoOrientedNorthSeed, branch) := by
  obtain ⟨hPs, hQs⟩ := sixVertexFourByTwoAlignedPairings_false
    sixVertexFourByTwoOrientedSeed
  obtain ⟨hPn, hQn⟩ := sixVertexFourByTwoAlignedPairings_false
    sixVertexFourByTwoOrientedNorthSeed
  have hroute := sixVertexFourByTwoAlignedRoutingPairing_false_funext false
  cases branch
  · have hstart : doubledAlignedBlackDart
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false
        (sixVertexFourByTwoOrientedSeed, false) =
      fkMedialBlackDart1 (sixVertexFourByTwoVertex 0 0) := by
      apply (fkMedialBlackDartEquivVertexBool sixVertexFourByTwoTorus).injective
      simp [doubledAlignedBlackDart, alignedRoutingLoopPairing, hroute,
        doubledAlignedVertex, doubledAlignedSlot, orientedDartBoundaryAlignedSlot,
        AlignedExitRetie.slotP, hPs, blackDartOfStrandSlot,
        blackSideIndexOfStrandSlot, fkMedialBlackDartEquivVertexBool,
        fkMedialBlackDart1, fkMedialVertexParity,
        sixVertexFourByTwoOrientedSeed, sixVertexFourByTwoVertex,
        sixVertexFourByTwoTorus, strandSlot]
      apply Subtype.ext
      change (fkMedialBlackDart1 (sixVertexFourByTwoVertex 0 0)).1 =
        (fkMedialBlackDart1 (sixVertexFourByTwoVertex 0 0)).1
      rfl
    have hend : doubledAlignedBlackDart
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false
        (sixVertexFourByTwoOrientedNorthSeed, false) =
      fkMedialBlackDart1 (sixVertexFourByTwoVertex 0 1) := by
      unfold doubledAlignedBlackDart alignedRoutingLoopPairing
      rw [hroute]
      simp only [doubledAlignedVertex, doubledAlignedSlot,
        Bool.false_eq_true, if_false, orientedDartBoundaryAlignedSlot,
        AlignedExitRetie.slotP]
      rw [hPn]
      apply Subtype.ext
      simp [blackDartOfStrandSlot,
        blackSideIndexOfStrandSlot, fkMedialBlackDartEquivVertexBool,
        fkMedialBlackDart1, fkMedialVertexParity,
        sixVertexFourByTwoOrientedNorthSeed, sixVertexFourByTwoVertex,
        sixVertexFourByTwoTorus, strandSlot]
      change (fkMedialBlackDart1 (sixVertexFourByTwoVertex 0 1)).1 =
        (fkMedialBlackDart1 (sixVertexFourByTwoVertex 0 1)).1
      rfl
    unfold alignedBoundaryPerm alignedRoutingLoopPairing
    rw [hroute, hstart, hend]
    apply Subtype.ext
    rw [fkMedialBlackBoundaryPerm_val]
    simp [fkMedialBlackDart1,
      fkMedialLocalMate, fkMedialBondMate, fkMedialVertexParity,
      sixVertexFourByTwoVertex, sixVertexFourByTwoTorus,
      SixVertexArrows.cyclicPred, finitePeriodicSucc]
  · have hstart : doubledAlignedBlackDart
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false
        (sixVertexFourByTwoOrientedSeed, true) =
      fkMedialBlackDart0 (sixVertexFourByTwoVertex 0 0) := by
      apply (fkMedialBlackDartEquivVertexBool sixVertexFourByTwoTorus).injective
      simp [doubledAlignedBlackDart, alignedRoutingLoopPairing, hroute,
        doubledAlignedVertex, doubledAlignedSlot, orientedDartBoundaryAlignedSlot,
        AlignedExitRetie.slotP, hPs, blackDartOfStrandSlot,
        blackSideIndexOfStrandSlot, fkMedialBlackDartEquivVertexBool,
        fkMedialBlackDart0, fkMedialVertexParity,
        sixVertexFourByTwoOrientedSeed, sixVertexFourByTwoVertex,
        sixVertexFourByTwoTorus, strandSlot]
      apply Subtype.ext
      change (fkMedialBlackDart0 (sixVertexFourByTwoVertex 0 0)).1 =
        (fkMedialBlackDart0 (sixVertexFourByTwoVertex 0 0)).1
      rfl
    have hend : doubledAlignedBlackDart
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false
        (sixVertexFourByTwoOrientedNorthSeed, true) =
      fkMedialBlackDart0 (sixVertexFourByTwoVertex 0 1) := by
      unfold doubledAlignedBlackDart alignedRoutingLoopPairing
      rw [hroute]
      simp only [doubledAlignedVertex, doubledAlignedSlot,
        Bool.true_eq, if_true, orientedDartBoundaryAlignedSlot,
        Bool.false_eq_true, if_false, AlignedExitRetie.slotP]
      rw [hPn]
      apply Subtype.ext
      simp [blackDartOfStrandSlot,
        blackSideIndexOfStrandSlot, fkMedialBlackDartEquivVertexBool,
        fkMedialBlackDart0, fkMedialVertexParity,
        sixVertexFourByTwoOrientedNorthSeed, sixVertexFourByTwoVertex,
        sixVertexFourByTwoTorus, strandSlot]
      change (fkMedialBlackDart0 (sixVertexFourByTwoVertex 0 1)).1 =
        (fkMedialBlackDart0 (sixVertexFourByTwoVertex 0 1)).1
      rfl
    unfold alignedBoundaryPerm alignedRoutingLoopPairing
    rw [hroute, hstart, hend]
    apply Subtype.ext
    rw [fkMedialBlackBoundaryPerm_val]
    simp [fkMedialBlackDart0,
      fkMedialLocalMate, fkMedialBondMate, fkMedialVertexParity,
      sixVertexFourByTwoVertex, sixVertexFourByTwoTorus,
      SixVertexArrows.cyclicPred, finitePeriodicSucc]

set_option maxHeartbeats 1000000 in
theorem sixVertexFourByTwoAlignedBoundary_east_step :
    alignedBoundaryPerm sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false
        (doubledAlignedBlackDart sixVertexFourByTwoLowArrows_ice
          sixVertexFourByTwoHighArrows_ice
          sixVertexFourByTwo_locallyDegreeTwo false
          (sixVertexFourByTwoOrientedEastSeed, false)) =
      doubledAlignedBlackDart sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false
        (sixVertexFourByTwoOrientedSeed, false) := by
  obtain ⟨hPe, hQe⟩ := sixVertexFourByTwoAlignedPairings_false
    sixVertexFourByTwoOrientedEastSeed
  obtain ⟨hPs, hQs⟩ := sixVertexFourByTwoAlignedPairings_false
    sixVertexFourByTwoOrientedSeed
  have hroute := sixVertexFourByTwoAlignedRoutingPairing_false_funext false
  have hstart : doubledAlignedBlackDart
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo false
      (sixVertexFourByTwoOrientedEastSeed, false) =
    fkMedialBlackDart1 (sixVertexFourByTwoVertex 1 0) := by
    unfold doubledAlignedBlackDart alignedRoutingLoopPairing
    rw [hroute]
    simp only [doubledAlignedVertex, doubledAlignedSlot,
      Bool.false_eq_true, if_false, orientedDartBoundaryAlignedSlot,
      AlignedExitRetie.slotP]
    rw [hPe]
    apply Subtype.ext
    simp [blackDartOfStrandSlot,
      blackSideIndexOfStrandSlot, fkMedialBlackDartEquivVertexBool,
      fkMedialBlackDart1, fkMedialVertexParity,
      sixVertexFourByTwoOrientedEastSeed, sixVertexFourByTwoVertex,
      sixVertexFourByTwoTorus, strandSlot]
    change (fkMedialBlackDart1 (sixVertexFourByTwoVertex 1 0)).1 =
      (fkMedialBlackDart1 (sixVertexFourByTwoVertex 1 0)).1
    rfl
  have hend : doubledAlignedBlackDart
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo false
      (sixVertexFourByTwoOrientedSeed, false) =
    fkMedialBlackDart1 (sixVertexFourByTwoVertex 0 0) := by
    apply (fkMedialBlackDartEquivVertexBool sixVertexFourByTwoTorus).injective
    simp [doubledAlignedBlackDart, alignedRoutingLoopPairing, hroute,
      doubledAlignedVertex, doubledAlignedSlot, orientedDartBoundaryAlignedSlot,
      AlignedExitRetie.slotP, hPs, blackDartOfStrandSlot,
      blackSideIndexOfStrandSlot, fkMedialBlackDartEquivVertexBool,
      fkMedialBlackDart1, fkMedialVertexParity,
      sixVertexFourByTwoOrientedSeed, sixVertexFourByTwoVertex,
      sixVertexFourByTwoTorus, strandSlot]
    apply Subtype.ext
    change (fkMedialBlackDart1 (sixVertexFourByTwoVertex 0 0)).1 =
      (fkMedialBlackDart1 (sixVertexFourByTwoVertex 0 0)).1
    rfl
  unfold alignedBoundaryPerm alignedRoutingLoopPairing
  rw [hroute, hstart, hend]
  apply Subtype.ext
  rw [fkMedialBlackBoundaryPerm_val]
  simp [fkMedialBlackDart1,
    fkMedialLocalMate, fkMedialBondMate, fkMedialVertexParity,
    sixVertexFourByTwoVertex, sixVertexFourByTwoTorus,
    SixVertexArrows.cyclicPred]

theorem sixVertexFourByTwoFirstReturn_seed (branch : Bool) :
    doubledAlignedFirstReturnPerm sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        (sixVertexFourByTwoOrientedSeed, branch) =
      (sixVertexFourByTwoOrientedNorthSeed, branch) :=
  doubledAlignedFirstReturnPerm_eq_of_boundary_step
    sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
    sixVertexFourByTwo_locallyDegreeTwo _ _
    (sixVertexFourByTwoAlignedBoundary_seed_step branch)

theorem sixVertexFourByTwoFirstReturn_east :
    doubledAlignedFirstReturnPerm sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        (sixVertexFourByTwoOrientedEastSeed, false) =
      (sixVertexFourByTwoOrientedSeed, false) :=
  doubledAlignedFirstReturnPerm_eq_of_boundary_step
    sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
    sixVertexFourByTwo_locallyDegreeTwo _ _
    sixVertexFourByTwoAlignedBoundary_east_step

theorem sixVertexFourByTwoBranchPredecessor_eq_seed_iff
    (branch : Bool)
    (d : SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows) :
    sixVertexDegreeTwoBranchPredecessor
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo branch d =
      sixVertexFourByTwoOrientedSeed ↔
    d = sixVertexFourByTwoOrientedNorthSeed := by
  let sigma := doubledAlignedFirstReturnPerm
    sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
    sixVertexFourByTwo_locallyDegreeTwo
  constructor
  · intro hpre
    let z := sigma.symm (d, branch)
    have hz : sigma z = (d, branch) := sigma.apply_symm_apply (d, branch)
    have hzfst : z.1 = sixVertexFourByTwoOrientedSeed := hpre
    cases hbranch : z.2
    · have hzstate : z = (sixVertexFourByTwoOrientedSeed, false) := by
        exact Prod.ext hzfst hbranch
      rw [hzstate, sixVertexFourByTwoFirstReturn_seed] at hz
      exact (congrArg Prod.fst hz).symm
    · have hzstate : z = (sixVertexFourByTwoOrientedSeed, true) := by
        exact Prod.ext hzfst hbranch
      rw [hzstate, sixVertexFourByTwoFirstReturn_seed] at hz
      exact (congrArg Prod.fst hz).symm
  · rintro rfl
    unfold sixVertexDegreeTwoBranchPredecessor
    have hreturn := sixVertexFourByTwoFirstReturn_seed branch
    rw [← hreturn, sigma.symm_apply_apply]

theorem sixVertexFourByTwoSynchronizedSeed_isIsolated :
    (sixVertexDegreeTwoSynchronizedGraph
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo).IsIsolated
        sixVertexFourByTwoOrientedSeed := by
  intro w hadj
  rcases hadj with ⟨hne, d, h | h⟩
  · have hd : d = sixVertexFourByTwoOrientedNorthSeed :=
      (sixVertexFourByTwoBranchPredecessor_eq_seed_iff false d).mp h.1.symm
    have htrue :=
      (sixVertexFourByTwoBranchPredecessor_eq_seed_iff true d).mpr hd
    apply hne
    exact (h.2.trans htrue).symm
  · have hd : d = sixVertexFourByTwoOrientedNorthSeed :=
      (sixVertexFourByTwoBranchPredecessor_eq_seed_iff true d).mp h.2.symm
    have hfalse :=
      (sixVertexFourByTwoBranchPredecessor_eq_seed_iff false d).mpr hd
    apply hne
    exact (h.1.trans hfalse).symm

theorem sixVertexFourByTwoSynchronizedComponentSelector_eq_true_iff
    (d : SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows) :
    sixVertexDegreeTwoSynchronizedComponentSelector
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent d = true ↔
      d = sixVertexFourByTwoOrientedSeed := by
  rw [sixVertexDegreeTwoSynchronizedComponentSelector_eq_true_iff]
  constructor
  · intro hcomponent
    by_contra hne
    have hreach : (sixVertexDegreeTwoSynchronizedGraph
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo).Reachable d
          sixVertexFourByTwoOrientedSeed := by
      apply SimpleGraph.ConnectedComponent.exact
      simpa [sixVertexFourByTwoSynchronizedSeedComponent] using hcomponent
    exact (SimpleGraph.not_reachable_of_neighborSet_right_eq_empty hne
      sixVertexFourByTwoSynchronizedSeed_isIsolated.neighborSet_eq_empty) hreach
  · rintro rfl
    rfl





theorem sixVertexFourByTwoSynchronizedSeedComponent_charge_one :
    sixVertexDegreeTwoSynchronizedComponentCharge
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo
      sixVertexFourByTwoSynchronizedSeedComponent = 1 := by
  rw [sixVertexDegreeTwoSynchronizedComponentCharge_eq_selectorSum]
  classical
  simp only [sixVertexFourByTwoSynchronizedComponentSelector_eq_true_iff]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  unfold sixVertexDegreeTwoStrandStepSeamSign
  have hmem := sixVertexDegreeTwoLocalMate_side_mem
    sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoOrientedSeed.1
  have hne := sixVertexDegreeTwoLocalMate_side_ne
    sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoOrientedSeed.1
  unfold sixVertexTorusDartEdge
  rw [sixVertexDegreeTwoLocalMate_vertex]
  generalize hs :
      (sixVertexDegreeTwoLocalMate sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoOrientedSeed.1).1.2 = side
  rw [hs] at hmem hne
  fin_cases side <;>
    simp [sixVertexFourByTwoOrientedSeed, sixVertexFourByTwoVertex,
      sixVertexFourByTwoTorus, sixVertexFourByTwoLowArrows,
      sixVertexFourByTwoHighArrows, sixVertexLocalIncomingPattern,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, sixVertexTorusDartEdge,
      sixVertexTorusIncidentEdge, SixVertexArrows.cyclicPred,
      sixVertexTorusEdgeSeamSign, svFinLast] at hmem hne ⊢

@[simp] theorem sixVertexFourByTwoSynchronizedSelector_seed :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent
        (sixVertexFourByTwoOrientedSeed, false) = true := by
  exact (sixVertexFourByTwoSynchronizedComponentSelector_eq_true_iff _).mpr rfl

@[simp] theorem sixVertexFourByTwoSynchronizedSelector_seed_true :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent
        (sixVertexFourByTwoOrientedSeed, true) = true := by
  exact (sixVertexFourByTwoSynchronizedComponentSelector_eq_true_iff _).mpr rfl

@[simp] theorem sixVertexFourByTwoSynchronizedSelector_north
    (branch : Bool) :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent
        (sixVertexFourByTwoOrientedNorthSeed, branch) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  have heq :=
    (sixVertexFourByTwoSynchronizedComponentSelector_eq_true_iff _).mp htrue
  have hvertex := congrArg
    (fun d : SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows => d.1.1.1) heq
  norm_num [sixVertexFourByTwoOrientedNorthSeed,
    sixVertexFourByTwoOrientedSeed, sixVertexFourByTwoVertex] at hvertex

@[simp] theorem sixVertexFourByTwoSynchronizedSelector_east :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent
        (sixVertexFourByTwoOrientedEastSeed, false) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  have heq :=
    (sixVertexFourByTwoSynchronizedComponentSelector_eq_true_iff _).mp htrue
  have hvertex := congrArg
    (fun d : SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows => d.1.1.1) heq
  norm_num [sixVertexFourByTwoOrientedEastSeed,
    sixVertexFourByTwoOrientedSeed, sixVertexFourByTwoVertex] at hvertex

@[simp] theorem sixVertexFourByTwoTransition_seed_false :
    sixVertexDegreeTwoSynchronizedComponentTransitionBit
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent
        (sixVertexFourByTwoOrientedSeed, false) = true := by
  unfold sixVertexDegreeTwoSynchronizedComponentTransitionBit
  have hpre :
      (doubledAlignedFirstReturnPerm sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo).symm
          (sixVertexFourByTwoOrientedSeed, false) =
        (sixVertexFourByTwoOrientedEastSeed, false) := by
    rw [← sixVertexFourByTwoFirstReturn_east, Equiv.symm_apply_apply]
  rw [hpre]
  simp

@[simp] theorem sixVertexFourByTwoTransition_north_true :
    sixVertexDegreeTwoSynchronizedComponentTransitionBit
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent
        (sixVertexFourByTwoOrientedNorthSeed, true) = true := by
  unfold sixVertexDegreeTwoSynchronizedComponentTransitionBit
  have hpre :
      (doubledAlignedFirstReturnPerm sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo).symm
          (sixVertexFourByTwoOrientedNorthSeed, true) =
        (sixVertexFourByTwoOrientedSeed, true) := by
    rw [← sixVertexFourByTwoFirstReturn_seed true, Equiv.symm_apply_apply]
  rw [hpre]
  simp

@[simp] theorem sixVertexFourByTwoPhysicalRetieMask_seed_false :
    sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent false
        (doubledAlignedVertex (sixVertexFourByTwoOrientedSeed, false)) =
      true := by
  rw [sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_active]
  obtain ⟨hP, hQ⟩ := sixVertexFourByTwoAlignedPairings_false
    sixVertexFourByTwoOrientedSeed
  simp [hP, hQ]

@[simp] theorem sixVertexFourByTwoPhysicalRetieMask_north_true :
    sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent false
        (doubledAlignedVertex (sixVertexFourByTwoOrientedNorthSeed, true)) =
      true := by
  rw [sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_active]
  obtain ⟨hP, hQ⟩ := sixVertexFourByTwoAlignedPairings_false
    sixVertexFourByTwoOrientedNorthSeed
  simp [hP, hQ]

@[simp] theorem sixVertexFourByTwoParity_seed :
    fkMedialVertexParity
      (doubledAlignedVertex (sixVertexFourByTwoOrientedSeed, false)) = false := by
  decide +revert

@[simp] theorem sixVertexFourByTwoParity_north :
    fkMedialVertexParity
      (doubledAlignedVertex (sixVertexFourByTwoOrientedNorthSeed, true)) = true := by
  decide +revert

@[simp] theorem sixVertexFourByTwoPhysicalReturn_seed :
    sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent false
        (sixVertexFourByTwoOrientedSeed, false) =
      (sixVertexFourByTwoOrientedNorthSeed, false) := by
  unfold sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState
    sixVertexDegreeTwoSynchronizedComponentPhysicalInputState
    sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState
    sixVertexDegreeTwoSynchronizedComponentPhysicalOutputState
  rw [sixVertexFourByTwoPhysicalRetieMask_seed_false,
    sixVertexFourByTwoParity_seed]
  simp only [Bool.and_true, Bool.true_and, beq_self_eq_true, if_true,
    Bool.false_eq_true, if_false, doubledAlignedBranchSwap]
  rw [sixVertexFourByTwoFirstReturn_seed]
  simp only [Bool.not_false]
  rw [sixVertexFourByTwoPhysicalRetieMask_north_true,
    sixVertexFourByTwoParity_north]
  rfl

@[simp] theorem sixVertexFourByTwoActiveColor_true_seed :
    sixVertexDegreeTwoAlignedActiveColor
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo true
        (sixVertexFourByTwoOrientedSeed, false) = false := by
  obtain ⟨hP, hQ⟩ := sixVertexFourByTwoAlignedPairings_false
    sixVertexFourByTwoOrientedSeed
  rw [sixVertexDegreeTwoAlignedActiveColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor]
  simp only [doubledAlignedSlot, orientedDartBoundaryAlignedSlot,
    Bool.false_eq_true, if_false, Bool.true_eq, if_true,
    boundaryAlignedSlotQ, boundaryAlignedSlotQRaw]
  rw [hP, hQ]
  simp [doubledAlignedVertex, doubledAlignedSlot,
    orientedDartBoundaryAlignedSlot, boundaryAlignedSlotQ,
    boundaryAlignedSlotQRaw, AlignedExitRetie.slotP, hP, hQ,
    sixVertexFourByTwoOrientedSeed, sixVertexFourByTwoVertex,
    sixVertexFourByTwoTorus, fkMedialVertexParity, strandSlot,
    horizontalSlot, localMate, sideVertical, sixVertexLocalIncomingPattern,
    fkLoopWestIncoming, fkLoopEastIncoming,
    sixVertexFourByTwoHighArrows]

@[simp] theorem sixVertexFourByTwoActiveColor_false_north :
    sixVertexDegreeTwoAlignedActiveColor
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false
        (sixVertexFourByTwoOrientedNorthSeed, false) = true := by
  obtain ⟨hP, hQ⟩ := sixVertexFourByTwoAlignedPairings_false
    sixVertexFourByTwoOrientedNorthSeed
  rw [sixVertexDegreeTwoAlignedActiveColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor]
  simp only [doubledAlignedSlot, orientedDartBoundaryAlignedSlot,
    Bool.false_eq_true, if_false, AlignedExitRetie.slotP]
  rw [hP]
  simp [doubledAlignedVertex, doubledAlignedSlot,
    orientedDartBoundaryAlignedSlot, AlignedExitRetie.slotP, hP, hQ,
    sixVertexFourByTwoOrientedNorthSeed, sixVertexFourByTwoVertex,
    sixVertexFourByTwoTorus, fkMedialVertexParity, strandSlot,
    horizontalSlot, localMate, sideVertical, sixVertexLocalIncomingPattern,
    fkLoopWestIncoming, sixVertexFourByTwoLowArrows]


theorem sixVertexFourByTwo_not_activeReturnColorInvariant :
    ¬ SixVertexDegreeTwoSynchronizedComponentActiveReturnColorInvariant
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo
      sixVertexFourByTwoSynchronizedSeedComponent := by
  intro hinvariant
  have hbad := hinvariant false (sixVertexFourByTwoOrientedSeed, false)
  rw [sixVertexFourByTwoPhysicalReturn_seed,
    sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor_eq,
    sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor_eq] at hbad
  simp at hbad



def SixVertexFourByTwoSynchronizedActiveStepColorInvariant : Prop :=
  ∀ (layer : Bool) (dart : FKMedialBlackDart sixVertexFourByTwoTorus),
    activeBlackDart (omega := sixVertexFourByTwoLowArrows)
        (eta := sixVertexFourByTwoHighArrows) dart ∨
      activeBlackDart (omega := sixVertexFourByTwoLowArrows)
        (eta := sixVertexFourByTwoHighArrows)
        (alignedBoundaryPerm sixVertexFourByTwoLowArrows_ice
          sixVertexFourByTwoHighArrows_ice
          sixVertexFourByTwo_locallyDegreeTwo false dart) →
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource
          sixVertexFourByTwoLowArrows_ice
          sixVertexFourByTwoHighArrows_ice
          sixVertexFourByTwo_locallyDegreeTwo)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv
          sixVertexFourByTwoLowArrows_ice
          sixVertexFourByTwoHighArrows_ice
          sixVertexFourByTwo_locallyDegreeTwo
          sixVertexFourByTwoSynchronizedSeedComponent
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            sixVertexFourByTwoLowArrows_ice
            sixVertexFourByTwoHighArrows_ice
            sixVertexFourByTwo_locallyDegreeTwo layer
            (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart
              sixVertexFourByTwoLowArrows_ice
              sixVertexFourByTwoHighArrows_ice
              sixVertexFourByTwo_locallyDegreeTwo
              sixVertexFourByTwoSynchronizedSeedComponent layer dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource
          sixVertexFourByTwoLowArrows_ice
          sixVertexFourByTwoHighArrows_ice
          sixVertexFourByTwo_locallyDegreeTwo)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv
          sixVertexFourByTwoLowArrows_ice
          sixVertexFourByTwoHighArrows_ice
          sixVertexFourByTwo_locallyDegreeTwo
          sixVertexFourByTwoSynchronizedSeedComponent
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            sixVertexFourByTwoLowArrows_ice
            sixVertexFourByTwoHighArrows_ice
            sixVertexFourByTwo_locallyDegreeTwo layer dart))



theorem sixVertexFourByTwo_not_synchronizedActiveStepColorInvariant :
    ¬ SixVertexFourByTwoSynchronizedActiveStepColorInvariant := by
  classical
  intro hactive
  have hinvariant :=
    sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_active
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo
      sixVertexFourByTwoSynchronizedSeedComponent hactive
  let x : DoubledAlignedState sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows :=
    (sixVertexFourByTwoOrientedSeed, false)
  let returned :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo
      sixVertexFourByTwoSynchronizedSeedComponent false x
  let targetPairing :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo
      sixVertexFourByTwoSynchronizedSeedComponent false
  let coordinate := fkColoredBlackDartStrandSlotEquiv targetPairing
  let slot : sixVertexFourByTwoTorus.Vertex × Bool :=
    (doubledAlignedVertex x,
      doubledAlignedSlot sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false x)
  let dart : FKMedialBlackDart sixVertexFourByTwoTorus :=
    coordinate.symm slot
  have hslot : coordinate dart = slot := coordinate.apply_symm_apply slot
  have hdartActive : activeBlackDart
      (omega := sixVertexFourByTwoLowArrows)
      (eta := sixVertexFourByTwoHighArrows) dart := by
    unfold activeBlackDart
    rw [card_sixVertexLocalDisagreementSides]
    exact sixVertexFourByTwo_localDisagreementDegree_two dart.1.1
  have hstepActive : activeBlackDart
      (omega := sixVertexFourByTwoLowArrows)
      (eta := sixVertexFourByTwoHighArrows)
      (fkMedialBlackBoundaryPerm targetPairing dart) := by
    unfold activeBlackDart
    rw [card_sixVertexLocalDisagreementSides]
    exact sixVertexFourByTwo_localDisagreementDegree_two _
  have hfirst :
      (finiteFirstReturn
        (fkMedialBlackBoundaryPerm targetPairing)
        (activeBlackDart (omega := sixVertexFourByTwoLowArrows)
          (eta := sixVertexFourByTwoHighArrows))
        ⟨dart, hdartActive⟩).1 =
      fkMedialBlackBoundaryPerm targetPairing dart :=
    finiteFirstReturn_eq_step_of_selected_step
      (fkMedialBlackBoundaryPerm targetPairing)
      (activeBlackDart (omega := sixVertexFourByTwoLowArrows)
        (eta := sixVertexFourByTwoHighArrows))
      ⟨dart, hdartActive⟩ hstepActive
  have hreturnSlot :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_slot
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo
      sixVertexFourByTwoSynchronizedSeedComponent false x dart hdartActive
      hslot
  change coordinate
      ((finiteFirstReturn
        (fkMedialBlackBoundaryPerm targetPairing)
        (activeBlackDart (omega := sixVertexFourByTwoLowArrows)
          (eta := sixVertexFourByTwoHighArrows))
        ⟨dart, hdartActive⟩).1) =
    (doubledAlignedVertex returned,
      doubledAlignedSlot sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false returned) at hreturnSlot
  rw [hfirst] at hreturnSlot
  have hboundaryCoordinate :
      fkColoredStrandSlotBoundaryPerm targetPairing slot =
        (doubledAlignedVertex returned,
          doubledAlignedSlot sixVertexFourByTwoLowArrows_ice
            sixVertexFourByTwoHighArrows_ice
            sixVertexFourByTwo_locallyDegreeTwo false returned) := by
    change coordinate
      (fkMedialBlackBoundaryPerm targetPairing (coordinate.symm slot)) = _
    change coordinate (fkMedialBlackBoundaryPerm targetPairing dart) = _
    exact hreturnSlot
  have hcolor := hinvariant (false, slot)
  rw [fkColoredLayeredStrandSlotBoundaryPerm_apply,
    hboundaryCoordinate] at hcolor
  change
    sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent false returned =
      sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent false x at hcolor
  dsimp only [returned, x] at hcolor
  rw [sixVertexFourByTwoPhysicalReturn_seed,
    sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor_eq,
    sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor_eq] at hcolor
  simp at hcolor

end StatMech.FrontierD
