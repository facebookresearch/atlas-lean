/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.IsoradialKacWardRibbonIdentification













namespace StatMech.FrontierA

open Finset
open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


noncomputable def finiteCRSFFormanProduct
    (transport : V -> V -> Complex) (next : V -> V) : Complex :=
  ∏ cycle : finiteCRSFAtomicCycle next,
    (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle)





theorem finiteCRSFFormanProduct_eq_zero_of_twoCycle
    (transport : V -> V -> Complex) (next : V -> V) {v w : V}
    (hvw : v ≠ w) (hnextv : next v = w) (hnextw : next w = v)
    (htransport : transport v w * transport w v = 1) :
    finiteCRSFFormanProduct transport next = 0 := by
  let cycle : finiteCRSFAtomicCycle next :=
    ⟨Equiv.swap v w, Equiv.Perm.isCycle_swap hvw, by
      intro u hu
      rw [Equiv.Perm.support_swap hvw] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · simpa [hvw] using hnextv.symm
      · simpa [hvw] using hnextw.symm⟩
  unfold finiteCRSFFormanProduct
  apply Finset.prod_eq_zero (Finset.mem_univ cycle)
  rw [sub_eq_zero]
  unfold finiteCRSFAmbientAtomicCycleHolonomy
  rw [Equiv.Perm.support_swap hvw]
  rw [Finset.prod_insert (fun h => hvw (Finset.mem_singleton.mp h)),
    Finset.prod_singleton,
    hnextv, hnextw, htransport]




structure GenusZeroOneActiveRibbonFormanIdentification
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex) where
  genus_le_one : C.genus <= 1
  outgoingEdgeSet : (V -> V) -> Finset E
  conductanceMonomial : forall next : V -> V,
    finiteCRSFFormanProduct transport next ≠ 0 ->
      finiteCRSFOutgoingConductance conductance next =
        ∏ e ∈ outgoingEdgeSet next, weight e
  boundaryCoefficientFiber : forall F : Finset E,
    ribbonBoundaryCharacterCoefficient R character F =
      ∑ next : finiteMapFiber outgoingEdgeSet F,
        finiteCRSFFormanProduct transport next.1

namespace GenusZeroOneActiveRibbonFormanIdentification



theorem ribbonSubgraphSum_eq_laplacianDet
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex)
    (I : GenusZeroOneActiveRibbonFormanIdentification
      R C character weight conductance transport) :
    kwDualSubgraphSum
        (ribbonBoundaryCharacterCoefficient R character) weight =
      (finiteTwistedLaplacian conductance transport).det := by
  rw [det_finiteTwistedLaplacian_eq_sum_outgoing_mul_formanProduct]
  unfold kwDualSubgraphSum
  change (∑ F : Finset E,
      ribbonBoundaryCharacterCoefficient R character F *
        ∏ e ∈ F, weight e) =
    ∑ next : V -> V,
      finiteCRSFOutgoingConductance conductance next *
        finiteCRSFFormanProduct transport next
  calc
    (∑ F : Finset E,
        ribbonBoundaryCharacterCoefficient R character F *
          ∏ e ∈ F, weight e) =
      ∑ F : Finset E,
        (∑ next : finiteMapFiber I.outgoingEdgeSet F,
          finiteCRSFFormanProduct transport next.1) *
            ∏ e ∈ F, weight e := by
      apply Finset.sum_congr rfl
      intro F _
      rw [I.boundaryCoefficientFiber F]
    _ = ∑ F : Finset E,
        ∑ next : finiteMapFiber I.outgoingEdgeSet F,
          finiteCRSFOutgoingConductance conductance next.1 *
            finiteCRSFFormanProduct transport next.1 := by
      apply Finset.sum_congr rfl
      intro F _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro next _
      by_cases hactive : finiteCRSFFormanProduct transport next.1 = 0
      · simp [hactive]
      · rw [I.conductanceMonomial next.1 hactive, next.2]
        ring
    _ = ∑ next : V -> V,
        finiteCRSFOutgoingConductance conductance next *
          finiteCRSFFormanProduct transport next := by
      exact Fintype.sum_fiberwise I.outgoingEdgeSet
        (fun next : V -> V =>
          finiteCRSFOutgoingConductance conductance next *
            finiteCRSFFormanProduct transport next)

end GenusZeroOneActiveRibbonFormanIdentification



theorem criticalKacWard_det_eq_laplacian_of_activeRibbonIdentification
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool)
    (I : GenusZeroOneActiveRibbonFormanIdentification R C character
      (fun e => isoradialCriticalMu (thetaEdge e))
      (isoradialMuConductance thetaVertex) transport)
    (K : CriticalKacWardRibbonExpansion
      R character kacWard thetaEdge exceptional) :
    (1 - kacWard).det =
      (-1 : Complex) ^ coneExceptionCount exceptional *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det := by
  rw [K.expansion,
    I.ribbonSubgraphSum_eq_laplacianDet,
    det_finiteTwistedLaplacian_isoradialMu]
  calc
    ((-1 : Complex) ^ Fintype.card V *
          kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
          (∏ v : V, coneQuarterPhase exceptional v) *
          kwLaplacianEdgePrefactor thetaEdge) *
        (Complex.I ^ Fintype.card V *
          (finiteTwistedLaplacian
            (isoradialLaplacianConductance thetaVertex) transport).det) =
      (((-1 : Complex) ^ Fintype.card V *
          (∏ v : V, coneQuarterPhase exceptional v) *
          Complex.I ^ Fintype.card V) *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det) := by
      ring
    _ = _ := by rw [conePhase_prefactor_eq_exceptionSign]

end StatMech.FrontierA
