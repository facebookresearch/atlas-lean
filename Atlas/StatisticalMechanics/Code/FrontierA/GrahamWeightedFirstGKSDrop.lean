/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.GrahamWeightedSurvivorSwitching

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]



noncomputable def grahamFirstComponentFiber
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (i : V)
    (A B : Finset V) : Real :=
  gatedSourcePairSum G beta J A B
    (fun n => notConnComp G n i = S)


noncomputable def grahamFirstComponentContext
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (i j : V) : Real :=
  ∑' bd, claim1Context G beta J S
    (fun n => notConnComp G n i = S) {i, j} ∅ bd

private theorem grahamFirstComponent_noCrossing
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {i : V} (hi : i ∉ S) :
    ∀ n, notConnComp G n i = S -> NoCrossing G n S := by
  intro n hn
  exact noCrossing_of_event G n S i hi hn

private theorem grahamFirstComponent_congr
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {i : V} (hi : i ∉ S) :
    ∀ n n' : Current V,
      (∀ e ∈ G.edgeFinset, ¬ edgeInside S e -> n e = n' e) ->
      (notConnComp G n i = S ↔ notConnComp G n' i = S) := by
  intro n n' hagree
  constructor
  · intro hn
    exact notConnComp_congr G n n' S i hi hn hagree
  · intro hn'
    exact notConnComp_congr G n' n S i hi hn'
      (fun e he hnot => (hagree e he hnot).symm)



theorem grahamFirstComponentFiber_remainder_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    {i j : V} (hi : i ∉ S) (hj : j ∉ S) :
    grahamFirstComponentFiber G beta J S i {i, j} ∅ =
      currentSum G beta (couplingIn J S) ∅ ^ 2 *
        grahamFirstComponentContext G beta J S i j := by
  unfold grahamFirstComponentFiber grahamFirstComponentContext
  have hfactor := gatedSourcePairSum_factor G beta J S
    (fun n => notConnComp G n i = S)
    (grahamFirstComponent_noCrossing G S hi)
    (grahamFirstComponent_congr G S hi)
    ∅ {i, j} ∅ ∅
    (Finset.empty_subset S)
    (by
      intro x hx
      rw [Finset.mem_compl]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hj)
    (Finset.empty_subset S)
    (Finset.empty_subset Sᶜ)
  have hleft : (∅ : Finset V) ∆ {i, j} = {i, j} := by
    ext x
    simp [Finset.mem_symmDiff]
  have hzero : (∅ : Finset V) ∆ ∅ = ∅ := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hleft, hzero] at hfactor
  calc
    gatedSourcePairSum G beta J {i, j} ∅
        (fun n => notConnComp G n i = S) =
      currentSum G beta (couplingIn J S) ∅ *
        currentSum G beta (couplingIn J S) ∅ *
          (∑' bd, claim1Context G beta J S
            (fun n => notConnComp G n i = S) {i, j} ∅ bd) := hfactor
    _ = _ := by ring




theorem grahamFirstComponentFiber_mixed_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    {i j k l : V} (hi : i ∉ S) (hj : j ∉ S)
    (hk : k ∈ S) (hl : l ∈ S) :
    grahamFirstComponentFiber G beta J S i {i, j} {k, l} =
      currentSum G beta (couplingIn J S) ∅ *
        currentSum G beta (couplingIn J S) {k, l} *
          grahamFirstComponentContext G beta J S i j := by
  unfold grahamFirstComponentFiber grahamFirstComponentContext
  have hfactor := gatedSourcePairSum_factor G beta J S
    (fun n => notConnComp G n i = S)
    (grahamFirstComponent_noCrossing G S hi)
    (grahamFirstComponent_congr G S hi)
    ∅ {i, j} {k, l} ∅
    (Finset.empty_subset S)
    (by
      intro x hx
      rw [Finset.mem_compl]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hj)
    (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hk
      · exact hl)
    (Finset.empty_subset Sᶜ)
  have hleft : (∅ : Finset V) ∆ {i, j} = {i, j} := by
    ext x
    simp [Finset.mem_symmDiff]
  have hright : ({k, l} : Finset V) ∆ ∅ = {k, l} := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hleft, hright] at hfactor
  exact hfactor


theorem grahamFirstComponentGKSDrop_identity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    {i j k l : V} (hi : i ∉ S) (hj : j ∉ S)
    (hk : k ∈ S) (hl : l ∈ S) :
    currentSum G beta J {k, l} *
        grahamFirstComponentFiber G beta J S i {i, j} ∅ -
      currentSum G beta J ∅ *
        grahamFirstComponentFiber G beta J S i {i, j} {k, l} =
      currentSum G beta J ∅ *
        grahamFirstComponentFiber G beta J S i {i, j} ∅ *
          (expectationJ G beta J {k, l} -
            expectationJ G beta (couplingIn J S) {k, l}) := by
  rw [grahamFirstComponentFiber_remainder_factor G beta J S hi hj]
  rw [grahamFirstComponentFiber_mixed_factor G beta J S hi hj hk hl]
  rw [StatMech.Ising.acr_eq15_insertion' G beta J {k, l}]
  rw [StatMech.Ising.acr_eq15_insertion' G beta (couplingIn J S) {k, l}]
  ring



theorem grahamFirstComponentGKSDrop_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) {i j k l : V}
    (hi : i ∉ S) (hj : j ∉ S) (hk : k ∈ S) (hl : l ∈ S) :
    0 ≤ currentSum G beta J {k, l} *
        grahamFirstComponentFiber G beta J S i {i, j} ∅ -
      currentSum G beta J ∅ *
        grahamFirstComponentFiber G beta J S i {i, j} {k, l} := by
  rw [grahamFirstComponentGKSDrop_identity G beta J S hi hj hk hl]
  exact mul_nonneg
    (mul_nonneg
      (le_of_lt (StatMech.Ising.acr_currentSum_empty_pos G beta J))
      (gatedSourcePairSum_nonneg G beta J hbeta hJ {i, j} ∅
        (fun n => notConnComp G n i = S)))
    (grahamComponentGKSDifference_nonneg G beta J hbeta hJ S k l)

end StatMech.FrontierA
