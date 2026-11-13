/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectZeroTurnAnnulusCharge
import Code.FrontierD.FKRectDualBoundaryWiring











namespace StatMech.FrontierD

noncomputable section



abbrev FKRectRawWiredDualHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :=
  {C : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R
        (fkRectForceCutClosed R omega))).ConnectedComponent //
    FKRectRawHorizontalCrossingComponent R
      (fkRectDualConfigurationEquiv R
        (fkRectForceCutClosed R omega)) C}

noncomputable instance instDecidablePredFKRectRawWiredDualHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    DecidablePred (FKRectRawHorizontalCrossingComponent R
      (fkRectDualConfigurationEquiv R
        (fkRectForceCutClosed R omega))) :=
  Classical.decPred _


abbrev FKRectRawPrimalWiredDualHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :=
  FKRectRawPrimalHorizontalCrossingComponent R omega ⊕
    FKRectRawWiredDualHorizontalCrossingComponent R omega



structure FKRectZeroTurnMixedAnnulusCharge
    (R : FKRectTorus) (omega : R.Configuration) where
  crossing : FKRectZeroTurnCutRemainderComponent R omega →
    FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega
  side : FKRectZeroTurnCutRemainderComponent R omega → Bool
  injective_pair : Function.Injective fun C => (crossing C, side C)



noncomputable def FKRectZeroTurnMixedAnnulusCharge.ofCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega)
    (hunique : ∀ C D,
      crossing C = crossing D →
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D → C = D) :
    FKRectZeroTurnMixedAnnulusCharge R omega where
  crossing := crossing
  side := fkRectZeroTurnRemainderSide R omega
  injective_pair := by
    intro C D h
    injection h with hcross hside
    exact hunique C D hcross hside




noncomputable def FKRectZeroTurnMixedAnnulusCharge.ofAnchor
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega)
    (anchor :
      FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega →
        Bool → FKMedialDart R.medialTorus)
    (hanchor : ∀ C,
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (anchor (crossing C)
            (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
    FKRectZeroTurnMixedAnnulusCharge R omega :=
  FKRectZeroTurnMixedAnnulusCharge.ofCrossing R omega crossing (by
    intro C D hcross hside
    apply Subtype.ext
    rw [← hanchor C, ← hanchor D, hcross, hside])

private theorem card_fkRectRawWiredDualHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card
        (FKRectRawWiredDualHorizontalCrossingComponent R omega) =
      fkRectRawHorizontalCrossingClusterCount R
        (fkRectDualConfigurationEquiv R
          (fkRectForceCutClosed R omega)) := by
  unfold fkRectRawHorizontalCrossingClusterCount
  exact Fintype.card_congr (Equiv.refl _)

private theorem card_fkRectZeroTurnCutRemainderComponent_mixed
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card (FKRectZeroTurnCutRemainderComponent R omega) =
      fkRectZeroTurnCutRemainderCount R omega := by
  classical
  unfold FKRectZeroTurnCutRemainderComponent
    fkRectZeroTurnCutRemainderCount
  exact Fintype.card_ofFinset
    (fkRectZeroTurnCutRemainderComponents R omega) (by simp)

private theorem card_fkRectRawPrimalHorizontalCrossingComponent_mixed
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card (FKRectRawPrimalHorizontalCrossingComponent R omega) =
      fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) := by
  unfold fkRectRawHorizontalCrossingClusterCount
  exact Fintype.card_congr (Equiv.refl _)

private theorem card_fkRectRawPrimalWiredDualHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card
        (FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega) =
      fkRectRawPrimalDualHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) := by
  rw [Fintype.card_sum,
    card_fkRectRawPrimalHorizontalCrossingComponent_mixed,
    card_fkRectRawWiredDualHorizontalCrossingComponent]
  rfl


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimalDual_of_mixedCharge
    (R : FKRectTorus) (omega : R.Configuration)
    (charge : FKRectZeroTurnMixedAnnulusCharge R omega) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawPrimalDualHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) := by
  let encode : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega × Bool :=
    fun C => (charge.crossing C, charge.side C)
  have hcard := Fintype.card_le_of_injective encode charge.injective_pair
  rw [card_fkRectZeroTurnCutRemainderComponent_mixed] at hcard
  rw [Fintype.card_prod, Fintype.card_bool,
    card_fkRectRawPrimalWiredDualHorizontalCrossingComponent] at hcard
  omega



theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge
    (R : FKRectTorus) (omega : R.Configuration)
    (charge : FKRectZeroTurnMixedAnnulusCharge R omega) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 := by
  have hcharge :=
    fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimalDual_of_mixedCharge
      R omega charge
  have hdual := fkRectRawHorizontalCrossingClusterCount_dual_le_one
    R (fkRectForceCutClosed R omega)
      (fkRectCutClosedConfiguration_forceCutClosed R omega)
  unfold fkRectRawPrimalDualHorizontalCrossingClusterCount at hcharge
  omega


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega)
    (hunique : ∀ C D,
      crossing C = crossing D →
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D → C = D) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge
    R omega
      (FKRectZeroTurnMixedAnnulusCharge.ofCrossing
        R omega crossing hunique)


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedAnchor
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega)
    (anchor :
      FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega →
        Bool → FKMedialDart R.medialTorus)
    (hanchor : ∀ C,
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (anchor (crossing C)
            (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge
    R omega
      (FKRectZeroTurnMixedAnnulusCharge.ofAnchor
        R omega crossing anchor hanchor)

end

end StatMech.FrontierD
