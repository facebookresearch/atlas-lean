/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamWeightedFirstGKSDropGlobal
















open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]





theorem finiteTree_component_sourceReplacement
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    {i j k l : V}
    (hi : i ∉ S) (hj : j ∉ S) (hk : k ∈ S) (hl : l ∈ S) :
    grahamFirstComponentFiber G beta J S i {i, j} {k, l} =
      expectationJ G beta (couplingIn J S) {k, l} *
        grahamFirstComponentFiber G beta J S i {i, j} ∅ := by
  rw [grahamFirstComponentFiber_mixed_factor G beta J S hi hj hk hl,
    grahamFirstComponentFiber_remainder_factor G beta J S hi hj,
    StatMech.Ising.acr_eq15_insertion' G beta (couplingIn J S) {k, l}]
  ring




theorem finiteTree_mixedDisconnection_eq_componentReplacement
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    sourcePairDisconnSum G beta J {i, j} {k, l} i k =
      ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k,
        expectationJ G beta (couplingIn J S) {k, l} *
          grahamFirstComponentFiber G beta J S i {i, j} ∅ := by
  have hmass :
      sourcePairDisconnSum G beta J {i, j} {k, l} i k =
        grahamFirstMixedRemainderMass G beta J i j k l k := by
    rw [show sourcePairDisconnSum G beta J {i, j} {k, l} i k =
        gatedSourcePairSum G beta J {i, j} {k, l}
          (fun n => ¬ CurrentConnected G n i k) by rfl]
    unfold grahamFirstMixedRemainderMass
    apply gatedSourcePairSum_congr_sources
    intro p q hp hq
    simp only [and_self]
  rw [hmass,
    grahamFirstMixedRemainderMass_eq_componentSum G beta J hij hkl]
  apply Finset.sum_congr rfl
  intro S hS
  rw [grahamFirstAdmissibleComponentComplements,
    Finset.mem_filter] at hS
  exact finiteTree_component_sourceReplacement G beta J S
    hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1



theorem finiteTree_componentReplacement_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (S : Finset V) (i j k l : V) :
    0 <= expectationJ G beta (couplingIn J S) {k, l} *
      grahamFirstComponentFiber G beta J S i {i, j} ∅ := by
  apply mul_nonneg
  · exact StatMech.Ising.acr_expectationJ_nonneg G beta
      (couplingIn J S) hbeta
      (fun e => by
        unfold couplingIn
        split <;> simp_all [hJ e]) {k, l}
  · exact gatedSourcePairSum_nonneg G beta J hbeta hJ {i, j} ∅
      (fun n => notConnComp G n i = S)

end StatMech.FrontierA
