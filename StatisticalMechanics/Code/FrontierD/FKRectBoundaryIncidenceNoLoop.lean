/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryIncidenceConnected
import Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
import Code.FrontierD.FKRectWiredDualBoundarySplice



namespace StatMech.FrontierD

noncomputable section

open Filter Topology




def FKRectForcedDualSameSideSharedRightBoundaryContact
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  forall C D : FKRectZeroTurnCutRemainderComponent R omega,
    forall X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ->
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega D ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega C ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega D ->
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D ->
      ∃ y : Fin R.height,
        y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C ∧
          y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega D



def FKRectForcedDualSameSideRightBoundaryConnected
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  forall C D : FKRectZeroTurnCutRemainderComponent R omega,
    forall X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ->
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega D ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega C ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega D ->
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D ->
      ∃ yC yD : Fin R.height,
        yC ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C ∧
          yD ∈ fkRectZeroTurnDualRightBoundaryContacts R omega D ∧
          (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Reachable
            (fkRectRightColumn R, yC) (fkRectRightColumn R, yD)




def FKRectForcedDualSameSideRightBoundaryConnectivityReflection
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  forall C D : FKRectZeroTurnCutRemainderComponent R omega,
    forall X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ->
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega D ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega C ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega D ->
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D ->
      forall yC yD : Fin R.height,
        yC ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C ->
        yD ∈ fkRectZeroTurnDualRightBoundaryContacts R omega D ->
        (fkRectOpenGraph R
          (fkRectDualConfigurationEquiv R
            (fkRectForceCutClosed R omega))).Reachable
              (fkRectRightColumn R, yC) (fkRectRightColumn R, yD) ->
        (fkRectOpenGraph R
          (fkRectDualConfigurationEquiv R omega)).Reachable
            (fkRectRightColumn R, yC) (fkRectRightColumn R, yD)



theorem fkRectForcedDualSameSideRightBoundaryConnected_of_reflection
    (R : FKRectTorus) (omega : R.Configuration)
    (hreflect :
      FKRectForcedDualSameSideRightBoundaryConnectivityReflection R omega) :
    FKRectForcedDualSameSideRightBoundaryConnected R omega := by
  intro C D X hCbranch hDbranch hCX hDX hside
  obtain ⟨yC, hyC⟩ :=
    fkRectZeroTurnDualRightBoundaryContacts_nonempty R omega C
  obtain ⟨yD, hyD⟩ :=
    fkRectZeroTurnDualRightBoundaryContacts_nonempty R omega D
  refine ⟨yC, yD, hyC, hyD, ?_⟩
  apply hreflect C D X hCbranch hDbranch hCX hDX hside yC yD hyC hyD
  exact fkRectDualOpenGraph_rightBoundary_reachable R
    (fkRectForceCutClosed R omega)
    (fkRectCutClosedConfiguration_forceCutClosed R omega) yC yD

set_option maxHeartbeats 800000 in



theorem
    fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_rightBoundaryContacts_reachable
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (yC yD : Fin R.height)
    (hyC : yC ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C)
    (hyD : yD ∈ fkRectZeroTurnDualRightBoundaryContacts R omega D)
    (hyCD : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).Reachable
        (fkRectRightColumn R, yC) (fkRectRightColumn R, yD)) :
    fkRectBlackBoundaryCyclePrimalComponent R
        (fkRectDualConfigurationEquiv R omega)
        (fkRectBlackBoundaryCycleDualEquiv R omega
          (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega C))) =
      fkRectBlackBoundaryCyclePrimalComponent R
        (fkRectDualConfigurationEquiv R omega)
        (fkRectBlackBoundaryCycleDualEquiv R omega
          (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega D))) := by
  let eta := fkRectDualConfigurationEquiv R omega
  let bC := fkRectZeroTurnRemainderBlackDart R omega C
  let bD := fkRectZeroTurnRemainderBlackDart R omega D
  let sC := fkRectMedialDualShiftDart R bC.1
  let sD := fkRectMedialDualShiftDart R bD.1
  let zC : R.Vertex := (fkRectRightColumn R, yC)
  let zD : R.Vertex := (fkRectRightColumn R, yD)
  have hzC : zC ∈
      (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C).support :=
    (mem_fkRectZeroTurnDualRightBoundaryContacts R omega C yC).1 hyC
  have hzD : zD ∈
      (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega D).support :=
    (mem_fkRectZeroTurnDualRightBoundaryContacts R omega D yD).1 hyD
  have hCstart : (fkRectOpenGraph R eta).Reachable
      (fkRectMedialDartPrimalLabel R
        (fkRectDualBlackDartEquiv R omega bC).1) zC := by
    have hpC : (fkRectOpenGraph R eta).Reachable
        (fkRectMedialDartPrimalLabel R sC) zC := by
      simpa [eta, sC, bC, zC] using
        ((fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C).takeUntil
          zC hzC).reachable
    have hlocal := fkRectMedialDartPrimalLabel_localMate_reachable
      R eta sC
    simpa [eta, sC, bC, fkRectDualBlackDartEquiv] using
      hlocal.symm.trans hpC
  have hDstart : (fkRectOpenGraph R eta).Reachable
      (fkRectMedialDartPrimalLabel R
        (fkRectDualBlackDartEquiv R omega bD).1) zD := by
    have hpD : (fkRectOpenGraph R eta).Reachable
        (fkRectMedialDartPrimalLabel R sD) zD := by
      simpa [eta, sD, bD, zD] using
        ((fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega D).takeUntil
          zD hzD).reachable
    have hlocal := fkRectMedialDartPrimalLabel_localMate_reachable
      R eta sD
    simpa [eta, sD, bD, fkRectDualBlackDartEquiv] using
      hlocal.symm.trans hpD
  rw [fkRectBlackBoundaryCycleDualEquiv_mk,
    fkRectBlackBoundaryCycleDualEquiv_mk,
    fkRectBlackBoundaryCyclePrimalComponent_mk,
    fkRectBlackBoundaryCyclePrimalComponent_mk]
  apply SimpleGraph.ConnectedComponent.sound
  exact hCstart.trans (hyCD.trans hDstart.symm)



theorem
    fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_sharedRightBoundaryContact
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (y : Fin R.height)
    (hyC : y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C)
    (hyD : y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega D) :
    fkRectBlackBoundaryCyclePrimalComponent R
        (fkRectDualConfigurationEquiv R omega)
        (fkRectBlackBoundaryCycleDualEquiv R omega
          (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega C))) =
      fkRectBlackBoundaryCyclePrimalComponent R
        (fkRectDualConfigurationEquiv R omega)
        (fkRectBlackBoundaryCycleDualEquiv R omega
          (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega D))) := by
  apply
    fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_rightBoundaryContacts_reachable
      R omega C D y y hyC hyD
  exact SimpleGraph.Reachable.refl _



theorem fkRectBlackBoundaryCycle_eq_of_primalComponent_eq_of_fst_mul_pos
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectConfigurationBlackBoundaryCycle R omega)
    (hcomponent : fkRectBlackBoundaryCyclePrimalComponent R omega C =
      fkRectBlackBoundaryCyclePrimalComponent R omega D)
    (hsign : 0 < (fkRectBlackBoundaryCycleWinding R omega C).1 *
      (fkRectBlackBoundaryCycleWinding R omega D).1) :
    C = D := by
  classical
  induction C using Quot.ind with
  | _ c =>
      induction D using Quot.ind with
      | _ d =>
          let x := fkRectMedialDartPrimalLabel R c.1
          have hmemC : fkRectBlackBoundaryCycleInPrimalCluster R omega x
              (Quot.mk _ c) := by
            rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent]
            simp [x, fkRectBlackBoundaryCyclePrimalComponent]
          have hmemD : fkRectBlackBoundaryCycleInPrimalCluster R omega x
              (Quot.mk _ d) := by
            rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent]
            exact hcomponent.symm.trans
              ((fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent
                R omega x (Quot.mk _ c)).mp hmemC)
          exact fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_fst_mul_pos
            R omega x
              (card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_atVertex
                R omega x)
              hmemC hmemD hsign



theorem fkRectZeroTurnRemainderBlackDart_fst_mul_pos_of_sameSide
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (hside : fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D) :
    0 < (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega
            (fkRectZeroTurnRemainderBlackDart R omega C))).1 *
        (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega
            (fkRectZeroTurnRemainderBlackDart R omega D))).1 := by
  cases hCside : fkRectZeroTurnRemainderSide R omega C
  · have hDside : fkRectZeroTurnRemainderSide R omega D = false := by
      rw [← hside, hCside]
    exact mul_pos_of_neg_of_neg
      ((fkRectZeroTurnRemainderSide_eq_false_iff R omega C).mp hCside)
      ((fkRectZeroTurnRemainderSide_eq_false_iff R omega D).mp hDside)
  · have hDside : fkRectZeroTurnRemainderSide R omega D = true := by
      rw [← hside, hCside]
    exact mul_pos
      ((fkRectZeroTurnRemainderSide_eq_true_iff R omega C).mp hCside)
      ((fkRectZeroTurnRemainderSide_eq_true_iff R omega D).mp hDside)



theorem fkRectZeroTurnRemainder_eq_of_primalComponent_eq_of_sameSide
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (hcomponent : fkRectZeroTurnRemainderPrimalComponent R omega C =
      fkRectZeroTurnRemainderPrimalComponent R omega D)
    (hside : fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D) :
    C = D := by
  let bC := fkRectZeroTurnRemainderBlackDart R omega C
  let bD := fkRectZeroTurnRemainderBlackDart R omega D
  let cC : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bC
  let cD : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bD
  have hcycleComponent :
      fkRectBlackBoundaryCyclePrimalComponent R omega cC =
        fkRectBlackBoundaryCyclePrimalComponent R omega cD := by
    calc
      fkRectBlackBoundaryCyclePrimalComponent R omega cC =
          (fkRectOpenGraph R omega).connectedComponentMk
            (fkRectMedialDartPrimalLabel R bC.1) := by
              simp [cC]
      _ = fkRectZeroTurnRemainderPrimalComponent R omega C :=
        (fkRectZeroTurnRemainderPrimalComponent_eq_label R omega C).symm
      _ = fkRectZeroTurnRemainderPrimalComponent R omega D := hcomponent
      _ = (fkRectOpenGraph R omega).connectedComponentMk
            (fkRectMedialDartPrimalLabel R bD.1) :=
        fkRectZeroTurnRemainderPrimalComponent_eq_label R omega D
      _ = fkRectBlackBoundaryCyclePrimalComponent R omega cD := by
        simp [cD]
  have hcycleSign : 0 <
      (fkRectBlackBoundaryCycleWinding R omega cC).1 *
        (fkRectBlackBoundaryCycleWinding R omega cD).1 := by
    rw [show cC = Quot.mk _ bC from rfl,
      show cD = Quot.mk _ bD from rfl,
      fkRectBlackBoundaryCycleWinding_mk,
      fkRectBlackBoundaryCycleWinding_mk,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega bC,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega bD]
    exact fkRectZeroTurnRemainderBlackDart_fst_mul_pos_of_sameSide
      R omega C D hside
  have hcycleEq : cC = cD :=
    fkRectBlackBoundaryCycle_eq_of_primalComponent_eq_of_fst_mul_pos
      R omega cC cD hcycleComponent hcycleSign
  have hsame : (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R omega)).SameCycle bC bD :=
    Quotient.exact hcycleEq
  apply Subtype.ext
  calc
    C.1 = (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          bC.1 := (fkRectZeroTurnRemainderBlackDart_component R omega C).symm
    _ = (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          bD.1 := by
      apply SimpleGraph.ConnectedComponent.sound
      exact (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).mp hsame
    _ = D.1 := fkRectZeroTurnRemainderBlackDart_component R omega D



theorem fkRectZeroTurnRemainder_eq_of_dualComponent_eq_of_sameSide
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (hcomponent :
      fkRectBlackBoundaryCyclePrimalComponent R
          (fkRectDualConfigurationEquiv R omega)
          (fkRectBlackBoundaryCycleDualEquiv R omega
            (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega C))) =
        fkRectBlackBoundaryCyclePrimalComponent R
          (fkRectDualConfigurationEquiv R omega)
          (fkRectBlackBoundaryCycleDualEquiv R omega
            (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega D))))
    (hside : fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D) :
    C = D := by
  let eta := fkRectDualConfigurationEquiv R omega
  let bC := fkRectZeroTurnRemainderBlackDart R omega C
  let bD := fkRectZeroTurnRemainderBlackDart R omega D
  let cC : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bC
  let cD : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bD
  let dcC := fkRectBlackBoundaryCycleDualEquiv R omega cC
  let dcD := fkRectBlackBoundaryCycleDualEquiv R omega cD
  have horigSign : 0 <
      (fkRectBlackBoundaryCycleWinding R omega cC).1 *
        (fkRectBlackBoundaryCycleWinding R omega cD).1 := by
    rw [show cC = Quot.mk _ bC from rfl,
      show cD = Quot.mk _ bD from rfl,
      fkRectBlackBoundaryCycleWinding_mk,
      fkRectBlackBoundaryCycleWinding_mk,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega bC,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega bD]
    exact fkRectZeroTurnRemainderBlackDart_fst_mul_pos_of_sameSide
      R omega C D hside
  have hdualSign : 0 <
      (fkRectBlackBoundaryCycleWinding R eta dcC).1 *
        (fkRectBlackBoundaryCycleWinding R eta dcD).1 := by
    change 0 <
      (fkRectBlackBoundaryCycleWinding R
        (fkRectDualConfigurationEquiv R omega) dcC).1 *
      (fkRectBlackBoundaryCycleWinding R
        (fkRectDualConfigurationEquiv R omega) dcD).1
    rw [show dcC = fkRectBlackBoundaryCycleDualEquiv R omega cC from rfl,
      show dcD = fkRectBlackBoundaryCycleDualEquiv R omega cD from rfl,
      fkRectBlackBoundaryCycleWinding_dualEquiv,
      fkRectBlackBoundaryCycleWinding_dualEquiv]
    simpa using horigSign
  have hdualEq : dcC = dcD :=
    fkRectBlackBoundaryCycle_eq_of_primalComponent_eq_of_fst_mul_pos
      R eta dcC dcD hcomponent hdualSign
  have horigEq : cC = cD :=
    (fkRectBlackBoundaryCycleDualEquiv R omega).injective hdualEq
  have hsame : (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R omega)).SameCycle bC bD :=
    Quotient.exact horigEq
  apply Subtype.ext
  calc
    C.1 = (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          bC.1 := (fkRectZeroTurnRemainderBlackDart_component R omega C).symm
    _ = (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          bD.1 := by
      apply SimpleGraph.ConnectedComponent.sound
      exact (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).mp hsame
    _ = D.1 := fkRectZeroTurnRemainderBlackDart_component R omega D


noncomputable def fkRectZeroTurnSelectedPrimalTouchedCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    FKRectRawPrimalHorizontalCrossingComponent R omega :=
  (fkRectZeroTurnPrimalTouchedCrossings_nonempty_of_avoidsRowSeam
    R omega C hC).choose

theorem fkRectZeroTurnSelectedPrimalTouchedCrossing_mem
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    fkRectZeroTurnSelectedPrimalTouchedCrossing R omega C hC ∈
      fkRectZeroTurnPrimalTouchedCrossings R omega C :=
  (fkRectZeroTurnPrimalTouchedCrossings_nonempty_of_avoidsRowSeam
    R omega C hC).choose_spec



noncomputable def fkRectZeroTurnSelectedDualRightBoundaryContact
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) : Fin R.height :=
  (fkRectZeroTurnDualRightBoundaryContacts_nonempty R omega C).choose

theorem fkRectZeroTurnSelectedDualRightBoundaryContact_mem
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    fkRectZeroTurnSelectedDualRightBoundaryContact R omega C ∈
      fkRectZeroTurnDualRightBoundaryContacts R omega C :=
  (fkRectZeroTurnDualRightBoundaryContacts_nonempty R omega C).choose_spec



abbrev FKRectZeroTurnPrimalOrRightBoundaryContact
    (R : FKRectTorus) (omega : R.Configuration) :=
  FKRectRawPrimalHorizontalCrossingComponent R omega ⊕ Fin R.height



noncomputable def fkRectZeroTurnSelectedPrimalOrRightBoundaryContact
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    FKRectZeroTurnPrimalOrRightBoundaryContact R omega := by
  classical
  exact if hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C then
      Sum.inl (fkRectZeroTurnSelectedPrimalTouchedCrossing R omega C hC)
    else
      Sum.inr (fkRectZeroTurnSelectedDualRightBoundaryContact R omega C)

set_option maxHeartbeats 800000 in



theorem fkRectZeroTurnSelectedPrimalOrRightBoundaryContact_side_injective
    (R : FKRectTorus) (omega : R.Configuration) :
    Function.Injective fun C : FKRectZeroTurnCutRemainderComponent R omega =>
      (fkRectZeroTurnSelectedPrimalOrRightBoundaryContact R omega C,
        fkRectZeroTurnRemainderSide R omega C) := by
  intro C D h
  have hchoice := congrArg Prod.fst h
  have hside := congrArg Prod.snd h
  change fkRectZeroTurnSelectedPrimalOrRightBoundaryContact R omega C =
    fkRectZeroTurnSelectedPrimalOrRightBoundaryContact R omega D at hchoice
  change fkRectZeroTurnRemainderSide R omega C =
    fkRectZeroTurnRemainderSide R omega D at hside
  by_cases hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C
  · by_cases hD : FKRectZeroTurnUsesPrimalTouchedCrossings R omega D
    · rw [fkRectZeroTurnSelectedPrimalOrRightBoundaryContact,
        dif_pos hC,
        fkRectZeroTurnSelectedPrimalOrRightBoundaryContact,
        dif_pos hD] at hchoice
      injection hchoice with hcross
      apply fkRectZeroTurnRemainder_eq_of_primalComponent_eq_of_sameSide
        R omega C D _ hside
      apply fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_touchedCrossing
        R omega C D
          (fkRectZeroTurnSelectedPrimalTouchedCrossing R omega C hC)
      · exact fkRectZeroTurnSelectedPrimalTouchedCrossing_mem
          R omega C hC
      · rw [hcross]
        exact fkRectZeroTurnSelectedPrimalTouchedCrossing_mem
          R omega D hD
    · simp [fkRectZeroTurnSelectedPrimalOrRightBoundaryContact,
        hC, hD] at hchoice
  · by_cases hD : FKRectZeroTurnUsesPrimalTouchedCrossings R omega D
    · simp [fkRectZeroTurnSelectedPrimalOrRightBoundaryContact,
        hC, hD] at hchoice
    · rw [fkRectZeroTurnSelectedPrimalOrRightBoundaryContact,
        dif_neg hC,
        fkRectZeroTurnSelectedPrimalOrRightBoundaryContact,
        dif_neg hD] at hchoice
      injection hchoice with hcontact
      apply fkRectZeroTurnRemainder_eq_of_dualComponent_eq_of_sameSide
        R omega C D _ hside
      apply
        fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_sharedRightBoundaryContact
          R omega C D
            (fkRectZeroTurnSelectedDualRightBoundaryContact R omega C)
      · exact fkRectZeroTurnSelectedDualRightBoundaryContact_mem R omega C
      · rw [hcontact]
        exact fkRectZeroTurnSelectedDualRightBoundaryContact_mem R omega D



theorem
    fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_height_unconditional
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 * R.height := by
  let encode : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectZeroTurnPrimalOrRightBoundaryContact R omega × Bool :=
    fun C =>
      (fkRectZeroTurnSelectedPrimalOrRightBoundaryContact R omega C,
        fkRectZeroTurnRemainderSide R omega C)
  have hcard := Fintype.card_le_of_injective encode
    (fkRectZeroTurnSelectedPrimalOrRightBoundaryContact_side_injective
      R omega)
  have hrem : Fintype.card (FKRectZeroTurnCutRemainderComponent R omega) =
      fkRectZeroTurnCutRemainderCount R omega := by
    classical
    unfold FKRectZeroTurnCutRemainderComponent
      fkRectZeroTurnCutRemainderCount
    exact Fintype.card_ofFinset
      (fkRectZeroTurnCutRemainderComponents R omega) (by simp)
  have hprimal :
      Fintype.card (FKRectRawPrimalHorizontalCrossingComponent R omega) =
        fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) := by
    unfold fkRectRawHorizontalCrossingClusterCount
    exact Fintype.card_congr (Equiv.refl _)
  rw [hrem, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_sum, hprimal, Fintype.card_fin] at hcard
  omega



theorem fkRect_not_crossesVerticalSeam_indexedEdge_of_not_mem_horizontalCut
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∉ fkRectHorizontalCutEdges R) :
    ¬ fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectHorizontalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  change y.val ≠ 0 at ha
  have hh := R.height_gt_two
  have hylt := y.isLt
  intro hcross
  cases b
  · by_cases hy : Even y.val <;>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true, fkRectCrossesVerticalSeam_mk] at hcross
    all_goals rw [fkRectCyclicPred_val] at hcross
    all_goals split at hcross <;> omega
  · simp only [fkRectTorusIndexedEdge, if_true,
      fkRectCrossesVerticalSeam_mk] at hcross
    rw [fkRectCyclicPred_val] at hcross
    split at hcross <;> omega



theorem exists_fkRectHorizontalCutEdge_mem_remainderBoundaryCycleWalk
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    ∃ a : R.EdgeIndex, a ∈ fkRectHorizontalCutEdges R ∧
      fkRectTorusIndexedEdge R a ∈
        (fkRectBlackBoundaryPrimalCycleWalk R omega
          (fkRectZeroTurnRemainderBlackDart R omega C)).edges := by
  unfold FKRectZeroTurnUsesPrimalTouchedCrossings
    FKRectWalkAvoidsRowSeam at hC
  push Not at hC
  obtain ⟨e, he, hcross⟩ := hC
  have hex : ∃ x y : R.Vertex, e = s(x, y) := by
    induction e using Sym2.inductionOn with
    | _ x y => exact ⟨x, y, rfl⟩
  obtain ⟨x, y, rfl⟩ := hex
  have hadj := (fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)).adj_of_mem_edges he
  rcases hadj with ⟨a, haopen, haedge⟩
  refine ⟨a, ?_, ?_⟩
  · by_contra hnot
    exact (fkRect_not_crossesVerticalSeam_indexedEdge_of_not_mem_horizontalCut
      R a hnot) (by rwa [haedge])
  · rwa [haedge]



abbrev FKRectHorizontalCutEdge (R : FKRectTorus) :=
  {a : R.EdgeIndex // a ∈ fkRectHorizontalCutEdges R}


noncomputable def fkRectZeroTurnSelectedHorizontalCutEdge
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    FKRectHorizontalCutEdge R :=
  ⟨(exists_fkRectHorizontalCutEdge_mem_remainderBoundaryCycleWalk
      R omega C hC).choose,
    (exists_fkRectHorizontalCutEdge_mem_remainderBoundaryCycleWalk
      R omega C hC).choose_spec.1⟩

theorem fkRectZeroTurnSelectedHorizontalCutEdge_mem_boundaryCycleWalk
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    fkRectTorusIndexedEdge R
        (fkRectZeroTurnSelectedHorizontalCutEdge R omega C hC).1 ∈
      (fkRectBlackBoundaryPrimalCycleWalk R omega
        (fkRectZeroTurnRemainderBlackDart R omega C)).edges :=
  (exists_fkRectHorizontalCutEdge_mem_remainderBoundaryCycleWalk
    R omega C hC).choose_spec.2

set_option maxHeartbeats 800000 in



theorem fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_boundaryEdge
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (a : R.EdgeIndex)
    (haC : fkRectTorusIndexedEdge R a ∈
      (fkRectBlackBoundaryPrimalCycleWalk R omega
        (fkRectZeroTurnRemainderBlackDart R omega C)).edges)
    (haD : fkRectTorusIndexedEdge R a ∈
      (fkRectBlackBoundaryPrimalCycleWalk R omega
        (fkRectZeroTurnRemainderBlackDart R omega D)).edges) :
    fkRectZeroTurnRemainderPrimalComponent R omega C =
      fkRectZeroTurnRemainderPrimalComponent R omega D := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : R.Vertex,
      fkRectTorusIndexedEdge R a = s(x, y) := by
    induction fkRectTorusIndexedEdge R a using Sym2.inductionOn with
    | _ x y => exact ⟨x, y, rfl⟩
  have hxC : x ∈ (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C)).support := by
    apply (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C)).fst_mem_support_of_mem_edges
    rwa [← hxy]
  have hxD : x ∈ (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega D)).support := by
    apply (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega D)).fst_mem_support_of_mem_edges
    rwa [← hxy]
  rw [fkRectZeroTurnRemainderPrimalComponent_eq_label,
    fkRectZeroTurnRemainderPrimalComponent_eq_label]
  apply SimpleGraph.ConnectedComponent.sound
  exact ((fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C)).takeUntil x hxC).reachable
    |>.trans
      ((fkRectBlackBoundaryPrimalCycleWalk R omega
        (fkRectZeroTurnRemainderBlackDart R omega D)).takeUntil x hxD).reachable.symm



abbrev FKRectZeroTurnPrimalOrHorizontalCutEdge
    (R : FKRectTorus) (omega : R.Configuration) :=
  FKRectRawPrimalHorizontalCrossingComponent R omega ⊕
    FKRectHorizontalCutEdge R

noncomputable def fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    FKRectZeroTurnPrimalOrHorizontalCutEdge R omega := by
  classical
  exact if hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C then
      Sum.inl (fkRectZeroTurnSelectedPrimalTouchedCrossing R omega C hC)
    else
      Sum.inr (fkRectZeroTurnSelectedHorizontalCutEdge R omega C hC)

set_option maxHeartbeats 800000 in

theorem fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge_side_injective
    (R : FKRectTorus) (omega : R.Configuration) :
    Function.Injective fun C : FKRectZeroTurnCutRemainderComponent R omega =>
      (fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge R omega C,
        fkRectZeroTurnRemainderSide R omega C) := by
  intro C D h
  have hchoice := congrArg Prod.fst h
  have hside := congrArg Prod.snd h
  change fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge R omega C =
    fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge R omega D at hchoice
  change fkRectZeroTurnRemainderSide R omega C =
    fkRectZeroTurnRemainderSide R omega D at hside
  by_cases hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C
  · by_cases hD : FKRectZeroTurnUsesPrimalTouchedCrossings R omega D
    · rw [fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge,
        dif_pos hC, fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge,
        dif_pos hD] at hchoice
      injection hchoice with hcross
      apply fkRectZeroTurnRemainder_eq_of_primalComponent_eq_of_sameSide
        R omega C D _ hside
      apply fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_touchedCrossing
        R omega C D
          (fkRectZeroTurnSelectedPrimalTouchedCrossing R omega C hC)
      · exact fkRectZeroTurnSelectedPrimalTouchedCrossing_mem
          R omega C hC
      · rw [hcross]
        exact fkRectZeroTurnSelectedPrimalTouchedCrossing_mem
          R omega D hD
    · simp [fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge,
        hC, hD] at hchoice
  · by_cases hD : FKRectZeroTurnUsesPrimalTouchedCrossings R omega D
    · simp [fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge,
        hC, hD] at hchoice
    · rw [fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge,
        dif_neg hC, fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge,
        dif_neg hD] at hchoice
      injection hchoice with hedge
      apply fkRectZeroTurnRemainder_eq_of_primalComponent_eq_of_sameSide
        R omega C D _ hside
      apply fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_boundaryEdge
        R omega C D
          (fkRectZeroTurnSelectedHorizontalCutEdge R omega C hC).1
      · exact fkRectZeroTurnSelectedHorizontalCutEdge_mem_boundaryCycleWalk
          R omega C hC
      · rw [hedge]
        exact fkRectZeroTurnSelectedHorizontalCutEdge_mem_boundaryCycleWalk
          R omega D hD



theorem
    fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_four_width_unconditional
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 4 * R.width := by
  let encode : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectZeroTurnPrimalOrHorizontalCutEdge R omega × Bool :=
    fun C =>
      (fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge R omega C,
        fkRectZeroTurnRemainderSide R omega C)
  have hcard := Fintype.card_le_of_injective encode
    (fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge_side_injective R omega)
  have hrem : Fintype.card (FKRectZeroTurnCutRemainderComponent R omega) =
      fkRectZeroTurnCutRemainderCount R omega := by
    classical
    unfold FKRectZeroTurnCutRemainderComponent
      fkRectZeroTurnCutRemainderCount
    exact Fintype.card_ofFinset
      (fkRectZeroTurnCutRemainderComponents R omega) (by simp)
  have hprimal :
      Fintype.card (FKRectRawPrimalHorizontalCrossingComponent R omega) =
        fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) := by
    unfold fkRectRawHorizontalCrossingClusterCount
    exact Fintype.card_congr (Equiv.refl _)
  have hcut : Fintype.card (FKRectHorizontalCutEdge R) = 2 * R.width := by
    rw [← fkRectHorizontalCutEdges_card R]
    exact Fintype.card_ofFinset (fkRectHorizontalCutEdges R) (by simp)
  rw [hrem, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_sum, hprimal, hcut] at hcard
  omega



theorem fkRectCritical_zeroTurnAbove_le_half_of_boundaryIncidenceAdaptiveTail
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (n : Nat)
    (hsmall : Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤
      FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) / 2) :
    fkRectCriticalZeroTurnAboveMass R q
        (2 * R.width + (4 * R.width + 2 * n)) ≤ (1 : Real) / 2 := by
  let K : R.Configuration → Nat := fun eta =>
    2 * fkRectRawHorizontalCrossingClusterCount R
      (fkRectForceCutClosed R eta) + 4 * R.width
  have htop : ∀ omega : R.Configuration,
      fkRectZeroTurnLoopCount R omega ≤
        2 * R.width + K (fkRectForceCutClosed R omega) := by
    intro omega
    apply (fkRectZeroTurnLoopCount_le_two_width_add_cutRemainder
      R omega).trans
    apply Nat.add_le_add_left
    dsimp [K]
    simpa using
      (fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_four_width_unconditional
        R omega)
  have htransfer := fkRectCritical_zeroTurnAbove_cut_transfer
    R hq K htop (4 * R.width + 2 * n)
  let A : Set R.Configuration :=
    {eta | n < fkRectRawHorizontalCrossingClusterCount R
      (fkRectForceCutClosed R eta)}
  have hset :
      {eta | FKRectCutClosedConfiguration R eta ∧
          4 * R.width + 2 * n < K eta} =
        {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} := by
    ext eta
    simp only [Set.mem_setOf_eq, A, K]
    constructor <;> intro h
    · exact ⟨h.1, by omega⟩
    · exact ⟨h.1, by omega⟩
  rw [hset] at htransfer
  have htop' : FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) *
      fkRectCriticalZeroTurnAboveMass R q
        (2 * R.width + (4 * R.width + 2 * n)) ≤
    fkRectCriticalEventMass R q
      {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} := by
    exact htransfer
  rw [← closedMass_mul_fkRectCriticalCutFreeEventMass R hq A] at htop'
  have hcutNonneg : 0 ≤ fkRectCriticalCutFreeEventMass R q A :=
    fkRectCriticalCutFreeEventMass_nonneg R hq A
  have hmassLe :
      fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) *
          fkRectCriticalCutFreeEventMass R q A ≤
        fkRectCriticalCutFreeEventMass R q A := by
    nlinarith [fkRectCriticalClosedMass_cut_le_one R hq]
  have hbinom : fkRectCriticalCutFreeEventMass R q A ≤
      Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) := by
    exact fkRectCriticalCutFree_primalCrossingTail_le_choose_mul_pow
      R hq n
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq
  have hpow : 0 < FK.cFE (fkRectCriticalP q) q ^
      (2 * R.width + R.height) := pow_pos hc _
  have hfinal := htop'.trans (hmassLe.trans (hbinom.trans hsmall))
  nlinarith




theorem
    tendsto_allSectorNormalization_negLog_div_height_zero_of_boundaryIncidenceAdaptiveTail
    (R : Nat → FKRectTorus) {q : Real} (hq : 4 < q) (n : Nat → Nat)
    (hsmall : ∀ k,
      Nat.choose (R k).height (n k + 1) *
          ((FK.freeInfiniteVolume 2
            (fkRectCriticalP_pos (by linarith : 0 < q))
            (fkRectCriticalP_lt_one (by linarith : 0 < q))
            (by linarith : 0 < q) :
              MeasureTheory.Measure (ConfigSpace
                (Sym2 (StatMech.Lattice.Site 2)))).real
            (FK.boxBdryConnEvent 2 ((R k).width - 2))) ^ (n k + 1) ≤
        FK.cFE (fkRectCriticalP q) q ^
          (2 * (R k).width + (R k).height) / 2)
    (hwidth : Tendsto (fun k ↦ ((R k).width : Real) / (R k).height)
      atTop (nhds 0))
    (hn : Tendsto (fun k ↦ (n k : Real) / (R k).height)
      atTop (nhds 0))
    (hheight : Tendsto (fun k ↦ (R k).height) atTop atTop) :
    Tendsto (fun k ↦
      -Real.log (fkRectAllSectorNormalization (R k) q) /
        (R k).height) atTop (nhds 0) := by
  let L : Nat → Nat := fun k =>
    2 * (R k).width + (4 * (R k).width + 2 * n k)
  apply tendsto_allSectorNormalization_negLog_div_height_zero_of_sublinear_tail
    R hq L
  · intro k
    exact
      fkRectCritical_zeroTurnAbove_le_half_of_boundaryIncidenceAdaptiveTail
        (R k) (by linarith) (n k) (hsmall k)
  · have hcomb := (hwidth.const_mul (6 : Real)).add
        (hn.const_mul (2 : Real))
    have hcomb0 : Tendsto (fun k =>
        6 * ((R k).width : Real) / (R k).height +
          2 * (n k : Real) / (R k).height) atTop (nhds 0) := by
      simpa [mul_div_assoc] using hcomb
    apply hcomb0.congr'
    filter_upwards [] with k
    dsimp [L]
    push_cast
    ring
  · exact hheight




def FKRectForcedDualSameSideOriginalComponent
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  forall C D : FKRectZeroTurnCutRemainderComponent R omega,
    forall X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ->
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega D ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega C ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega D ->
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D ->
      fkRectBlackBoundaryCyclePrimalComponent R
          (fkRectDualConfigurationEquiv R omega)
          (fkRectBlackBoundaryCycleDualEquiv R omega
            (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega C))) =
        fkRectBlackBoundaryCyclePrimalComponent R
          (fkRectDualConfigurationEquiv R omega)
          (fkRectBlackBoundaryCycleDualEquiv R omega
            (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega D)))



theorem fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnected
    (R : FKRectTorus) (omega : R.Configuration)
    (hconnected : FKRectForcedDualSameSideRightBoundaryConnected R omega) :
    FKRectForcedDualSameSideOriginalComponent R omega := by
  intro C D X hCbranch hDbranch hCX hDX hside
  obtain ⟨yC, yD, hyC, hyD, hyCD⟩ :=
    hconnected C D X hCbranch hDbranch hCX hDX hside
  exact
    fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_rightBoundaryContacts_reachable
      R omega C D yC yD hyC hyD hyCD


theorem
    fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnectivityReflection
    (R : FKRectTorus) (omega : R.Configuration)
    (hreflect :
      FKRectForcedDualSameSideRightBoundaryConnectivityReflection R omega) :
    FKRectForcedDualSameSideOriginalComponent R omega :=
  fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnected
    R omega
      (fkRectForcedDualSameSideRightBoundaryConnected_of_reflection
        R omega hreflect)



theorem fkRectForcedDualSameSideOriginalComponent_of_sharedRightBoundaryContact
    (R : FKRectTorus) (omega : R.Configuration)
    (hcontact :
      FKRectForcedDualSameSideSharedRightBoundaryContact R omega) :
    FKRectForcedDualSameSideOriginalComponent R omega := by
  intro C D X hCbranch hDbranch hCX hDX hside
  obtain ⟨y, hyC, hyD⟩ :=
    hcontact C D X hCbranch hDbranch hCX hDX hside
  exact
    fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_sharedRightBoundaryContact
      R omega C D y hyC hyD

set_option maxHeartbeats 800000 in



theorem fkRectZeroTurnOriginalDualSameSideUnique_of_originalComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (hcomponent : FKRectForcedDualSameSideOriginalComponent R omega) :
    FKRectZeroTurnOriginalDualSameSideUnique R omega := by
  classical
  intro C D X hCbranch hDbranch hCX hDX hside
  let eta := fkRectDualConfigurationEquiv R omega
  let bC := fkRectZeroTurnRemainderBlackDart R omega C
  let bD := fkRectZeroTurnRemainderBlackDart R omega D
  let cC : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bC
  let cD : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bD
  let dcC := fkRectBlackBoundaryCycleDualEquiv R omega cC
  let dcD := fkRectBlackBoundaryCycleDualEquiv R omega cD
  let x := fkRectMedialDartPrimalLabel R
    (fkRectDualBlackDartEquiv R omega bC).1
  have hcomp : fkRectBlackBoundaryCyclePrimalComponent R eta dcC =
      fkRectBlackBoundaryCyclePrimalComponent R eta dcD := by
    exact hcomponent C D X hCbranch hDbranch hCX hDX hside
  have hmemC : fkRectBlackBoundaryCycleInPrimalCluster R eta x dcC := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent]
    simp [dcC, cC, x, fkRectBlackBoundaryCyclePrimalComponent]
  have hmemD : fkRectBlackBoundaryCycleInPrimalCluster R eta x dcD := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent]
    exact hcomp.symm.trans
      ((fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent
        R eta x dcC).mp hmemC)
  have horigSign : 0 <
      (fkRectBlackBoundaryCycleWinding R omega cC).1 *
        (fkRectBlackBoundaryCycleWinding R omega cD).1 := by
    rw [show cC = Quot.mk _ bC from rfl,
      show cD = Quot.mk _ bD from rfl,
      fkRectBlackBoundaryCycleWinding_mk,
      fkRectBlackBoundaryCycleWinding_mk,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega bC,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega bD]
    cases hCside : fkRectZeroTurnRemainderSide R omega C
    · have hDside : fkRectZeroTurnRemainderSide R omega D = false := by
        rw [← hside, hCside]
      exact mul_pos_of_neg_of_neg
        ((fkRectZeroTurnRemainderSide_eq_false_iff R omega C).mp hCside)
        ((fkRectZeroTurnRemainderSide_eq_false_iff R omega D).mp hDside)
    · have hDside : fkRectZeroTurnRemainderSide R omega D = true := by
        rw [← hside, hCside]
      exact mul_pos
        ((fkRectZeroTurnRemainderSide_eq_true_iff R omega C).mp hCside)
        ((fkRectZeroTurnRemainderSide_eq_true_iff R omega D).mp hDside)
  have hdualSign : 0 <
      (fkRectBlackBoundaryCycleWinding R eta dcC).1 *
        (fkRectBlackBoundaryCycleWinding R eta dcD).1 := by
    change 0 <
      (fkRectBlackBoundaryCycleWinding R
        (fkRectDualConfigurationEquiv R omega) dcC).1 *
      (fkRectBlackBoundaryCycleWinding R
        (fkRectDualConfigurationEquiv R omega) dcD).1
    rw [show dcC = fkRectBlackBoundaryCycleDualEquiv R omega cC from rfl,
      show dcD = fkRectBlackBoundaryCycleDualEquiv R omega cD from rfl,
      fkRectBlackBoundaryCycleWinding_dualEquiv,
      fkRectBlackBoundaryCycleWinding_dualEquiv]
    simpa using horigSign
  have hdualEq : dcC = dcD := by
    apply fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_fst_mul_pos
      R eta x
      (card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_atVertex R eta x)
      hmemC hmemD hdualSign
  have horigEq : cC = cD :=
    (fkRectBlackBoundaryCycleDualEquiv R omega).injective hdualEq
  have hsame : (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R omega)).SameCycle bC bD :=
    Quotient.exact horigEq
  apply Subtype.ext
  calc
    C.1 = (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          bC.1 := (fkRectZeroTurnRemainderBlackDart_component R omega C).symm
    _ = (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          bD.1 := by
      apply SimpleGraph.ConnectedComponent.sound
      exact (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).mp hsame
    _ = D.1 := fkRectZeroTurnRemainderBlackDart_component R omega D



theorem
    fkRectZeroTurnOriginalDualSameSideUnique_of_rightBoundaryConnectivityReflection
    (R : FKRectTorus) (omega : R.Configuration)
    (hreflect :
      FKRectForcedDualSameSideRightBoundaryConnectivityReflection R omega) :
    FKRectZeroTurnOriginalDualSameSideUnique R omega :=
  fkRectZeroTurnOriginalDualSameSideUnique_of_originalComponent R omega
    (fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnectivityReflection
      R omega hreflect)



theorem fkRectPrimalBoundaryFiberSameSignUnique_unconditional
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectPrimalBoundaryFiberSameSignUnique R omega := by
  apply fkRectPrimalBoundaryFiberSameSignUnique_of_card_nonzero_le_two
  intro _ x
  exact card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_atVertex
    R omega x



def FKRectPrimalRankOneRegularNeighborhood.ofBoundaryIncidence
    (R : FKRectTorus) (omega : R.Configuration)
    (hextreme : FKRectPrimalDevelopedExtremeSameSign R omega) :
    FKRectPrimalRankOneRegularNeighborhood R omega :=
  FKRectPrimalRankOneRegularNeighborhood.ofParts R omega
    (fkRectPrimalBoundaryFiberSameSignUnique_unconditional R omega) hextreme



theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_boundaryIncidence_height
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (hextreme : forall omega : R.Configuration,
      FKRectPrimalDevelopedExtremeSameSign R omega)
    (hdual : forall omega : R.Configuration,
      FKRectZeroTurnOriginalDualSameSideUnique R omega) :
    (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) <=
      fkRectAllSectorNormalization R q := by
  apply zeroTurnCost_div_two_q_le_allSectorNormalization_of_regularNeighborhood_height
    R hq
  · intro omega
    exact FKRectPrimalRankOneRegularNeighborhood.ofBoundaryIncidence
      R omega (hextreme omega)
  · exact hdual

end

end StatMech.FrontierD
