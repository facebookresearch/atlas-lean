/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitLowRankSwitching
import Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching
import Code.FrontierA.IsingSurfaceTensionPrismGinibre
import Code.FrontierA.IsingSurfaceTensionInteriorBlockClosure
import Code.FrontierA.IsingSurfaceTensionCriticalInfiniteVolumeReduction











open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance selectedSeamCapacityDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _




theorem isingSurfaceTension_certificate_of_selectedSeamCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 < beta) (hJ : forall e, 0 <= J e)
    (hhf : forall x, 0 <= hf x) (hr : 0 <= r)
    (hcapacity : forall q,
      LPReplicaAggregateSelectedSeamCapacity G sites hsite q)
    (n : Nat) (hn : 0 < n)
    (hcritical : rectangularIsingSurfaceTension
      (StatMech.Ising.betaC 3) = 0) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    ((∑ i : I, ∑ j : I,
        lpMatchingFiveCurrentCoefficient H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0) ∧
      (2 * magnetization 3 beta ^ 2 *
          (((2 * n + 1 : Nat) : Real) ^ 2) <=
        fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 -
          fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
            (bondFinsetTouch 3 n) beta 0) ∧
      (0 < rectangularIsingSurfaceTension beta <->
        StatMech.Ising.betaC 3 < beta) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_selectedSeamCapacity
      G sites hsite beta J hf r hbeta.le hJ hhf hr hcapacity
  · exact finiteInterfaceEnergyDeficit_ge_area_mul_two_mul_sq
      beta hbeta.le n hn
  · exact rectangularIsingSurfaceTension_pos_iff_ordered_of_critical_zero
      hcritical beta hbeta




theorem isingSurfaceTension_certificate_of_highRankAggregateInjection
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 < beta) (hJ : forall e, 0 <= J e)
    (hhf : forall x, 0 <= hf x) (hr : 0 <= r)
    (hhigh : forall q,
      5 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q) ->
      LPReplicaAggregateDecoratedInjection G sites q)
    (hmean : forall m, OddPrismUnequalBridgeSymmetricMeanOrder
      (StatMech.Ising.betaC 3) m)
    (n : Nat) (hn : 0 < n) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    ((∑ i : I, ∑ j : I,
        lpMatchingFiveCurrentCoefficient H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0) ∧
      (2 * magnetization 3 beta ^ 2 *
          (((2 * n + 1 : Nat) : Real) ^ 2) <=
        fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 -
          fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
            (bondFinsetTouch 3 n) beta 0) ∧
      (0 < rectangularIsingSurfaceTension beta <->
        StatMech.Ising.betaC 3 < beta) := by
  dsimp only
  have hcritical : rectangularIsingSurfaceTension
      (StatMech.Ising.betaC 3) = 0 :=
    rectangularIsingSurfaceTension_critical_eq_zero_of_symmetricMeanOrder_infinite
      hmean
  refine ⟨?_, ?_, ?_⟩
  · exact
      lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_highRankAggregateInjection
        G sites hsite beta J hf r hbeta.le hJ hhf hr hhigh
  · exact finiteInterfaceEnergyDeficit_ge_area_mul_two_mul_sq
      beta hbeta.le n hn
  · exact rectangularIsingSurfaceTension_pos_iff_ordered_of_critical_zero
      hcritical beta hbeta

end

end StatMech.FrontierA
