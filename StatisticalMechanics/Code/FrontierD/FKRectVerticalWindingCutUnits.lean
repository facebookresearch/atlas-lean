/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectVerticalWindingRankOneReduction
import Code.FrontierD.FKRectVerticalWindingCutTouch









open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectPositiveBoundaryUnitMultiplicity
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (C : FKRectConfigurationBlackBoundaryCycle R omega) : Nat := by
  classical
  exact if fkRectBlackBoundaryCyclePrimalComponent R omega C = K then
    (fkRectBlackBoundaryCycleWinding R omega C).2.toNat else 0



abbrev FKRectPositiveBoundaryUnit
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :=
  Σ C : FKRectConfigurationBlackBoundaryCycle R omega,
    Fin (fkRectPositiveBoundaryUnitMultiplicity R omega K C)

theorem card_fkRectPositiveBoundaryUnit
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    Fintype.card (FKRectPositiveBoundaryUnit R omega K) =
      fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  unfold fkRectPositiveBoundaryUnitMultiplicity
    fkRectPrimalComponentPositiveBoundaryVerticalMass
  apply Finset.sum_congr rfl
  intro C _
  rfl

theorem FKRectPositiveBoundaryUnit.component
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (u : FKRectPositiveBoundaryUnit R omega K) :
    fkRectBlackBoundaryCyclePrimalComponent R omega u.1 = K := by
  have hu := u.2.isLt
  unfold fkRectPositiveBoundaryUnitMultiplicity at hu
  split at hu <;> simp_all

theorem FKRectPositiveBoundaryUnit.winding_snd_pos
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (u : FKRectPositiveBoundaryUnit R omega K) :
    0 < (fkRectBlackBoundaryCycleWinding R omega u.1).2 := by
  have hu := u.2.isLt
  unfold fkRectPositiveBoundaryUnitMultiplicity at hu
  split at hu
  · omega
  · simp at hu



abbrev FKRectHorizontalCutCrossingInFiber
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :=
  {X : {X : (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent //
      FKRectHorizontalCutPrimalCrossingComponent R
        (fkRectForceHorizontalCutClosed R omega) X} //
    fkRectHorizontalCutComponentTorusComponent R omega X.1 = K}

noncomputable instance instFintypeFKRectHorizontalCutCrossingInFiber
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    Fintype (FKRectHorizontalCutCrossingInFiber R omega K) :=
  Fintype.ofFinite _

theorem card_fkRectHorizontalCutCrossingInFiber
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    Fintype.card (FKRectHorizontalCutCrossingInFiber R omega K) =
      fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
  classical
  rw [Fintype.card_subtype]
  rfl



theorem positiveBoundaryMass_le_crossingCount_iff_nonempty_embedding
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤
        fkRectPrimalComponentHorizontalCutCrossingCount R omega K ↔
      Nonempty (FKRectPositiveBoundaryUnit R omega K ↪
        FKRectHorizontalCutCrossingInFiber R omega K) := by
  rw [Function.Embedding.nonempty_iff_card_le,
    card_fkRectPositiveBoundaryUnit,
    card_fkRectHorizontalCutCrossingInFiber]


theorem rankOnePositiveBoundaryCutFiberBound_iff_unitEmbedding
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega ↔
      ∀ K : (fkRectOpenGraph R omega).ConnectedComponent,
        ¬ FKRectPrimalComponentHasNet R omega K →
          Nonempty (FKRectPositiveBoundaryUnit R omega K ↪
            FKRectHorizontalCutCrossingInFiber R omega K) := by
  constructor
  · intro h K hnet
    rw [← positiveBoundaryMass_le_crossingCount_iff_nonempty_embedding]
    exact h K hnet
  · intro h K hnet
    rw [positiveBoundaryMass_le_crossingCount_iff_nonempty_embedding]
    exact h K hnet

end

end StatMech.FrontierD
