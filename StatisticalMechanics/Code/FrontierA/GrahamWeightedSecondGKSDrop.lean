/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamWeightedFirstGKSDropGlobal

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]



noncomputable def grahamSecondComponentFiber
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (k : V)
    (A B : Finset V) (P : Current V -> Prop) [DecidablePred P] : Real :=
  gatedSourcePairSum G beta J A B
    (fun n => notConnComp G n k = S ∧ P n)


noncomputable def grahamSecondComponentContext
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (k l : V) : Real :=
  ∑' bd, claim1Context G beta J S
    (fun n => notConnComp G n k = S) {k, l} ∅ bd

private theorem grahamSecondComponent_noCrossing
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {k : V} (hk : k ∉ S) :
    ∀ n, notConnComp G n k = S -> NoCrossing G n S := by
  intro n hn
  exact noCrossing_of_event G n S k hk hn

private theorem grahamSecondComponent_congr
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {k : V} (hk : k ∉ S) :
    ∀ n n' : Current V,
      (∀ e ∈ G.edgeFinset, ¬ edgeInside S e -> n e = n' e) ->
      (notConnComp G n k = S ↔ notConnComp G n' k = S) := by
  intro n n' hagree
  constructor
  · intro hn
    exact notConnComp_congr G n n' S k hk hn hagree
  · intro hn'
    exact notConnComp_congr G n' n S k hk hn'
      (fun e he hnot => (hagree e he hnot).symm)



theorem grahamSecondComponentFiber_remainder_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    {k l : V} (hk : k ∉ S) (hl : l ∉ S) :
    grahamSecondComponentFiber G beta J S k {k, l} ∅ (fun _ => True) =
      currentSum G beta (couplingIn J S) ∅ ^ 2 *
        grahamSecondComponentContext G beta J S k l := by
  unfold grahamSecondComponentFiber grahamSecondComponentContext
  have hgate : gatedSourcePairSum G beta J {k, l} ∅
      (fun n => notConnComp G n k = S ∧ True) =
      gatedSourcePairSum G beta J {k, l} ∅
        (fun n => notConnComp G n k = S) := by
    apply gatedSourcePairSum_congr_sources
    intro p q hp hq
    simp
  rw [hgate]
  have hfactor := gatedSourcePairSum_factor G beta J S
    (fun n => notConnComp G n k = S)
    (grahamSecondComponent_noCrossing G S hk)
    (grahamSecondComponent_congr G S hk)
    ∅ {k, l} ∅ ∅
    (Finset.empty_subset S)
    (by
      intro x hx
      rw [Finset.mem_compl]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hk
      · exact hl)
    (Finset.empty_subset S)
    (Finset.empty_subset Sᶜ)
  have hleft : (∅ : Finset V) ∆ {k, l} = {k, l} := by
    ext x
    simp [Finset.mem_symmDiff]
  have hzero : (∅ : Finset V) ∆ ∅ = ∅ := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hleft, hzero] at hfactor
  calc
    gatedSourcePairSum G beta J {k, l} ∅
        (fun n => notConnComp G n k = S) =
      currentSum G beta (couplingIn J S) ∅ *
        currentSum G beta (couplingIn J S) ∅ *
          (∑' bd, claim1Context G beta J S
            (fun n => notConnComp G n k = S) {k, l} ∅ bd) := hfactor
    _ = _ := by ring




theorem grahamSecondComponentFiber_mixed_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    {i j k l m : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (hi : i ∈ S) (hj : j ∈ S) (hm : m ∈ S)
    (hk : k ∉ S) (hl : l ∉ S) :
    grahamSecondComponentFiber G beta J S k {i, j} {k, l}
        (fun n => CurrentConnected G n i m) =
      currentSum G beta (couplingIn J S) {j, m} *
        currentSum G beta (couplingIn J S) {i, m} *
          grahamSecondComponentContext G beta J S k l := by
  let Pfix : Current V -> Prop := fun n => notConnComp G n k = S
  let Pim : Current V -> Prop := fun n => Pfix n ∧ CurrentConnected G n i m
  have hsdKL : ({i, j, k, l} : Finset V) ∆ {k, l} = {i, j} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;>
      by_cases hxk : x = k <;> by_cases hxl : x = l <;>
      simp_all [eq_comm]
  have hsdIM : ({i, j, k, l} : Finset V) ∆ {i, m} = {j, k, l, m} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;>
      by_cases hxk : x = k <;> by_cases hxl : x = l <;>
      by_cases hxm : x = m <;> simp_all [eq_comm]
  have hsdSplit : ({j, m} : Finset V) ∆ {k, l} = {j, k, l, m} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    by_cases hxj : x = j <;> by_cases hxm : x = m <;>
      by_cases hxk : x = k <;> by_cases hxl : x = l <;>
      simp_all [eq_comm]
  have hswitchKL := gatedSourcePairSum_switching G beta J
    ({i, j, k, l} : Finset V) hkl Pim
  rw [hsdKL] at hswitchKL
  have hconnKL : gatedSourcePairSum G beta J {i, j, k, l} ∅
      (fun n => Pim n ∧ CurrentConnected G n k l) =
      gatedSourcePairSum G beta J {i, j, k, l} ∅ Pim := by
    apply gatedSourcePairSum_congr_sources
    intro p q hp hq
    constructor
    · exact And.left
    · intro hP
      refine ⟨hP, ?_⟩
      by_contra hdisc
      apply hl
      rw [← hP.1, mem_notConnComp]
      exact hdisc
  have hswitchIM := gatedSourcePairSum_switching G beta J
    ({i, j, k, l} : Finset V) him Pfix
  rw [hsdIM] at hswitchIM
  have hfactor := gatedSourcePairSum_factor G beta J S Pfix
    (grahamSecondComponent_noCrossing G S hk)
    (grahamSecondComponent_congr G S hk)
    {j, m} {k, l} {i, m} ∅
    (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hj
      · exact hm)
    (by
      intro x hx
      rw [Finset.mem_compl]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hk
      · exact hl)
    (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hm)
    (Finset.empty_subset Sᶜ)
  rw [hsdSplit] at hfactor
  have hright : ({i, m} : Finset V) ∆ ∅ = {i, m} := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hright] at hfactor
  unfold grahamSecondComponentFiber grahamSecondComponentContext
  change gatedSourcePairSum G beta J {i, j} {k, l} Pim = _
  calc
    gatedSourcePairSum G beta J {i, j} {k, l} Pim =
        gatedSourcePairSum G beta J {i, j, k, l} ∅ Pim := by
          rw [hswitchKL, hconnKL]
    _ = gatedSourcePairSum G beta J {j, k, l, m} {i, m} Pfix :=
      hswitchIM.symm
    _ = _ := hfactor


theorem grahamSecondComponentGKSDrop_identity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    {i j k l m : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (hi : i ∈ S) (hj : j ∈ S) (hm : m ∈ S)
    (hk : k ∉ S) (hl : l ∉ S) :
    (currentSum G beta J {i, m} * currentSum G beta J {j, m}) *
        grahamSecondComponentFiber G beta J S k {k, l} ∅ (fun _ => True) -
      currentSum G beta J ∅ ^ 2 *
        grahamSecondComponentFiber G beta J S k {i, j} {k, l}
          (fun n => CurrentConnected G n i m) =
      currentSum G beta J ∅ ^ 2 *
        grahamSecondComponentFiber G beta J S k {k, l} ∅ (fun _ => True) *
          (expectationJ G beta J {i, m} * expectationJ G beta J {j, m} -
            expectationJ G beta (couplingIn J S) {i, m} *
              expectationJ G beta (couplingIn J S) {j, m}) := by
  rw [grahamSecondComponentFiber_remainder_factor G beta J S hk hl]
  rw [grahamSecondComponentFiber_mixed_factor G beta J S
    hij hik hil him hjk hjl hjm hkl hkm hlm hi hj hm hk hl]
  rw [StatMech.Ising.acr_eq15_insertion' G beta J {i, m}]
  rw [StatMech.Ising.acr_eq15_insertion' G beta J {j, m}]
  rw [StatMech.Ising.acr_eq15_insertion' G beta (couplingIn J S) {i, m}]
  rw [StatMech.Ising.acr_eq15_insertion' G beta (couplingIn J S) {j, m}]
  ring



theorem grahamRestrictedCorrelationProduct_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (i j m : V) :
    expectationJ G beta (couplingIn J S) {i, m} *
        expectationJ G beta (couplingIn J S) {j, m} ≤
      expectationJ G beta J {i, m} * expectationJ G beta J {j, m} := by
  have hi := expectationJ_couplingIn_le G beta J hbeta hJ S {i, m}
  have hj := expectationJ_couplingIn_le G beta J hbeta hJ S {j, m}
  have hiFull : 0 ≤ expectationJ G beta J {i, m} :=
    StatMech.Ising.acr_expectationJ_nonneg G beta J hbeta hJ {i, m}
  have hjLocal : 0 ≤ expectationJ G beta (couplingIn J S) {j, m} :=
    StatMech.Ising.acr_expectationJ_nonneg G beta (couplingIn J S) hbeta
      (fun e => by unfold couplingIn; split <;> simp_all [hJ e]) {j, m}
  exact mul_le_mul hi hj hjLocal hiFull


theorem grahamSecondComponentGKSDrop_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) {i j k l m : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (hi : i ∈ S) (hj : j ∈ S) (hm : m ∈ S)
    (hk : k ∉ S) (hl : l ∉ S) :
    0 ≤ (currentSum G beta J {i, m} * currentSum G beta J {j, m}) *
        grahamSecondComponentFiber G beta J S k {k, l} ∅ (fun _ => True) -
      currentSum G beta J ∅ ^ 2 *
        grahamSecondComponentFiber G beta J S k {i, j} {k, l}
          (fun n => CurrentConnected G n i m) := by
  rw [grahamSecondComponentGKSDrop_identity G beta J S
    hij hik hil him hjk hjl hjm hkl hkm hlm hi hj hm hk hl]
  apply mul_nonneg
  · exact mul_nonneg (sq_nonneg _)
      (gatedSourcePairSum_nonneg G beta J hbeta hJ {k, l} ∅
        (fun n => notConnComp G n k = S ∧ True))
  · have hprod := grahamRestrictedCorrelationProduct_le
      G beta J hbeta hJ S i j m
    linarith

end StatMech.FrontierA
