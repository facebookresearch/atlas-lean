/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectVerticalWindingCutFiberReduction









open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section


noncomputable def fkRectPrimalComponentBoundaryVerticalWindingSum
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) : Int := by
  classical
  exact ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
    if fkRectBlackBoundaryCyclePrimalComponent R omega C = K then
      (fkRectBlackBoundaryCycleWinding R omega C).2
    else 0



theorem sum_fkRectPrimalComponentBoundaryVerticalWinding_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    fkRectPrimalComponentBoundaryVerticalWindingSum R omega K = 0 := by
  classical
  unfold fkRectPrimalComponentBoundaryVerticalWindingSum
  induction K using ConnectedComponent.ind with
  | _ x =>
      have hpred (C : FKRectConfigurationBlackBoundaryCycle R omega) :
          fkRectBlackBoundaryCyclePrimalComponent R omega C =
              (fkRectOpenGraph R omega).connectedComponentMk x ↔
            fkRectBlackBoundaryCycleInPrimalCluster R omega x C := by
        induction C using Quot.ind with
        | _ d =>
            rw [fkRectBlackBoundaryCyclePrimalComponent_mk,
              fkRectBlackBoundaryCycleInPrimalCluster_mk,
              ConnectedComponent.eq]
            exact ⟨fun h => h.symm, fun h => h.symm⟩
      have h := congrArg Prod.snd
        (fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero R omega x)
      unfold fkRectPrimalClusterBoundaryCycleWindingSum at h
      simpa only [Prod.snd_sum, apply_ite Prod.snd, Prod.snd_zero,
        hpred] using h

private theorem two_mul_sum_toNat_eq_sum_natAbs_of_sum_eq_zero
    {α : Type*} [Fintype α] (w : α → Int)
    (hsum : ∑ a, w a = 0) :
    2 * (∑ a, (w a).toNat) = ∑ a, (w a).natAbs := by
  have hdiff :
      (∑ a, ((w a).toNat : Int)) -
          (∑ a, ((-w a).toNat : Int)) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [Int.toNat_sub_toNat_neg] using hsum
  have hbalance : (∑ a, (w a).toNat) = ∑ a, (-w a).toNat := by
    exact_mod_cast sub_eq_zero.mp hdiff
  calc
    2 * (∑ a, (w a).toNat) =
        (∑ a, (w a).toNat) + ∑ a, (-w a).toNat := by omega
    _ = ∑ a, ((w a).toNat + (-w a).toNat) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ a, (w a).natAbs := by
      apply Finset.sum_congr rfl
      intro a _
      exact Int.toNat_add_toNat_neg_eq_natAbs (w a)



theorem fkRectPrimalComponentBoundaryVerticalMass_eq_two_mul_positive
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    fkRectPrimalComponentBoundaryVerticalMass R omega K =
      2 * fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K := by
  classical
  let w : FKRectConfigurationBlackBoundaryCycle R omega → Int := fun C =>
    if fkRectBlackBoundaryCyclePrimalComponent R omega C = K then
      (fkRectBlackBoundaryCycleWinding R omega C).2
    else 0
  have hsum : ∑ C, w C = 0 := by
    simpa only [w, fkRectPrimalComponentBoundaryVerticalWindingSum] using
      sum_fkRectPrimalComponentBoundaryVerticalWinding_eq_zero R omega K
  have hbalance :=
    two_mul_sum_toNat_eq_sum_natAbs_of_sum_eq_zero w hsum
  unfold fkRectPrimalComponentBoundaryVerticalMass
    fkRectPrimalComponentPositiveBoundaryVerticalMass
  simpa only [w, apply_ite Int.toNat, Int.toNat_zero,
    apply_ite Int.natAbs, Int.natAbs_zero] using hbalance.symm



theorem verticalBoundaryMassCutFiberBound_iff_positive
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectVerticalBoundaryMassCutFiberBound R omega ↔
      FKRectPositiveVerticalBoundaryCutFiberBound R omega := by
  constructor
  · intro h K
    have hK := h K
    rw [fkRectPrimalComponentBoundaryVerticalMass_eq_two_mul_positive]
      at hK
    omega
  · intro h K
    rw [fkRectPrimalComponentBoundaryVerticalMass_eq_two_mul_positive]
    exact Nat.mul_le_mul_left 2 (h K)

end

end StatMech.FrontierD
