/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectZeroTurnDevelopedIncidence












namespace StatMech.FrontierD

noncomputable section



def FKRectZeroTurnReachablePrimalTouchedCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : Prop :=
  X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C ∧
    (fkRectOpenGraph R omega).Reachable
      (fkRectMedialWestPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C)))
      (fkRectMedialEastPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C)))



structure FKRectZeroTurnAdaptiveMixedRouting
    (R : FKRectTorus) (omega : R.Configuration) where
  crossing : FKRectZeroTurnCutRemainderComponent R omega →
    FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega
  primal_spec : ∀ C X, crossing C = Sum.inl X →
    FKRectZeroTurnReachablePrimalTouchedCrossing R omega C X
  dual_spec : ∀ C X, crossing C = Sum.inr X →
    X ∈ fkRectZeroTurnDualTouchedCrossings R omega C




def FKRectZeroTurnUsesAdaptiveDualRoute
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) : Prop :=
  ¬ ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
    FKRectZeroTurnReachablePrimalTouchedCrossing R omega C X

theorem fkRectZeroTurnUsesAdaptiveDualRoute_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    FKRectZeroTurnUsesAdaptiveDualRoute R omega C ↔
      ∀ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
        X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C →
        ¬ (fkRectOpenGraph R omega).Reachable
          (fkRectMedialWestPrimal R
            (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
              (fkRectZeroTurnRemainderSide R omega C)))
          (fkRectMedialEastPrimal R
            (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
              (fkRectZeroTurnRemainderSide R omega C))) := by
  constructor
  · intro h X hX hreach
    exact h ⟨X, hX, hreach⟩
  · rintro h ⟨X, hX, hreach⟩
    exact h X hX hreach




noncomputable def FKRectZeroTurnAdaptiveMixedRouting.toCharge
    (R : FKRectTorus) (omega : R.Configuration)
    (routing : FKRectZeroTurnAdaptiveMixedRouting R omega)
    (hdual : ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
      ∀ X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
        routing.crossing C = Sum.inr X →
        routing.crossing D = Sum.inr X →
        fkRectZeroTurnRemainderSide R omega C =
          fkRectZeroTurnRemainderSide R omega D → C = D) :
    FKRectZeroTurnMixedAnnulusCharge R omega :=
  FKRectZeroTurnMixedAnnulusCharge.ofCrossing
    R omega routing.crossing (by
      intro C D hcross hside
      cases hC : routing.crossing C with
      | inl X =>
          have hD : routing.crossing D = Sum.inl X := hcross.symm.trans hC
          have hXC := routing.primal_spec C X hC
          have hXD := routing.primal_spec D X hD
          exact
            fkRectZeroTurnRemainder_eq_of_shared_primalTouchedCrossing_of_endpointReachable
              R omega C D X hXC.1 hXD.1 hXC.2 hXD.2 hside
      | inr X =>
          have hD : routing.crossing D = Sum.inr X := hcross.symm.trans hC
          exact hdual C D X hC hD hside)




noncomputable def fkRectZeroTurnAdaptiveMixedRouting
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectZeroTurnAdaptiveMixedRouting R omega := by
  classical
  refine {
    crossing := fun C =>
      if h : ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
          FKRectZeroTurnReachablePrimalTouchedCrossing R omega C X then
        Sum.inl (Classical.choose h)
      else
        Sum.inr
          (fkRectZeroTurnDualTouchedCrossings_nonempty R omega C).choose
    primal_spec := ?_
    dual_spec := ?_ }
  · intro C X hX
    split at hX
    next h =>
      simp only [Sum.inl.injEq] at hX
      subst X
      exact Classical.choose_spec h
    next h => simp at hX
  · intro C X hX
    split at hX
    next h => simp at hX
    next h =>
      simp only [Sum.inr.injEq] at hX
      subst X
      exact (fkRectZeroTurnDualTouchedCrossings_nonempty R omega C).choose_spec



theorem fkRectZeroTurnUsesAdaptiveDualRoute_of_routing_eq_inr
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawWiredDualHorizontalCrossingComponent R omega)
    (hX : (fkRectZeroTurnAdaptiveMixedRouting R omega).crossing C =
      Sum.inr X) :
    FKRectZeroTurnUsesAdaptiveDualRoute R omega C := by
  classical
  unfold FKRectZeroTurnUsesAdaptiveDualRoute
  intro h
  change (if h' : ∃ Y : FKRectRawPrimalHorizontalCrossingComponent R omega,
      FKRectZeroTurnReachablePrimalTouchedCrossing R omega C Y then
        Sum.inl (Classical.choose h')
      else
        Sum.inr
          (fkRectZeroTurnDualTouchedCrossings_nonempty R omega C).choose) =
      Sum.inr X at hX
  rw [dif_pos h] at hX
  exact Sum.inl_ne_inr hX



theorem fkRectZeroTurnAdaptiveMixedRouting_eq_inr_of_usesDualRoute
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : FKRectZeroTurnUsesAdaptiveDualRoute R omega C) :
    (fkRectZeroTurnAdaptiveMixedRouting R omega).crossing C =
      Sum.inr
        (fkRectZeroTurnDualTouchedCrossings_nonempty R omega C).choose := by
  classical
  change ¬ ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
    FKRectZeroTurnReachablePrimalTouchedCrossing R omega C X at hC
  change (if h : ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
      FKRectZeroTurnReachablePrimalTouchedCrossing R omega C X then
        Sum.inl (Classical.choose h)
      else
        Sum.inr
          (fkRectZeroTurnDualTouchedCrossings_nonempty R omega C).choose) = _
  rw [dif_neg hC]




def FKRectZeroTurnAdaptiveDualRouteSameSideUnique
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
    FKRectZeroTurnUsesAdaptiveDualRoute R omega C →
    FKRectZeroTurnUsesAdaptiveDualRoute R omega D →
    fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D → C = D



noncomputable def fkRectZeroTurnAdaptiveMixedCharge_of_dualRouteUniqueness
    (R : FKRectTorus) (omega : R.Configuration)
    (hdual : FKRectZeroTurnAdaptiveDualRouteSameSideUnique R omega) :
    FKRectZeroTurnMixedAnnulusCharge R omega :=
  (fkRectZeroTurnAdaptiveMixedRouting R omega).toCharge R omega (by
    intro C D X hC hD hside
    exact hdual C D
      (fkRectZeroTurnUsesAdaptiveDualRoute_of_routing_eq_inr R omega C X hC)
      (fkRectZeroTurnUsesAdaptiveDualRoute_of_routing_eq_inr R omega D X hD)
      hside)



theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_dualRouteUniqueness
    (R : FKRectTorus) (omega : R.Configuration)
    (hdual : FKRectZeroTurnAdaptiveDualRouteSameSideUnique R omega) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge
    R omega
      (fkRectZeroTurnAdaptiveMixedCharge_of_dualRouteUniqueness R omega hdual)

end

end StatMech.FrontierD
