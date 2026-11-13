/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamWeightedBridgeGap
import Code.Sharpness.Claim1IsingComplete









open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def grahamSourcePairComponentFiber
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (m : V)
    (A B : Finset V) : Real :=
  gatedSourcePairSum G beta J A B
    (fun n => notConnComp G n m = S)

noncomputable def grahamComponentExteriorContext
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (m : V) : Real :=
  ∑' bd, claim1Context G beta J S
    (fun n => notConnComp G n m = S) ∅ ∅ bd

private theorem grahamComponentFiber_noCrossing
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {m : V} (hm : m ∉ S) :
    ∀ n, notConnComp G n m = S -> NoCrossing G n S := by
  intro n hn
  exact noCrossing_of_event G n S m hm hn

private theorem grahamComponentFiber_congr
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {m : V} (hm : m ∉ S) :
    ∀ n n' : Current V,
      (∀ i ∈ G.edgeFinset, ¬ edgeInside S i -> n i = n' i) ->
      (notConnComp G n m = S ↔ notConnComp G n' m = S) := by
  intro n n' hagree
  constructor
  · intro hn
    exact notConnComp_congr G n n' S m hm hn hagree
  · intro hn'
    exact notConnComp_congr G n' n S m hm hn'
      (fun i hi hni => (hagree i hi hni).symm)

theorem grahamSourcePairComponentFiber_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (m : V)
    (hm : m ∉ S) (A C : Finset V) (hA : A ⊆ S) (hC : C ⊆ S) :
    grahamSourcePairComponentFiber G beta J S m A C =
      currentSum G beta (couplingIn J S) A *
        currentSum G beta (couplingIn J S) C *
          grahamComponentExteriorContext G beta J S m := by
  unfold grahamSourcePairComponentFiber grahamComponentExteriorContext
  have hA0 : A ∆ (∅ : Finset V) = A := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.notMem_empty, not_false_eq_true,
      and_true, false_and, or_false]
  have hC0 : C ∆ (∅ : Finset V) = C := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.notMem_empty, not_false_eq_true,
      and_true, false_and, or_false]
  have hfactor := gatedSourcePairSum_factor G beta J S
    (fun n => notConnComp G n m = S)
    (grahamComponentFiber_noCrossing G S hm)
    (grahamComponentFiber_congr G S hm)
    A ∅ C ∅ hA (by simp) hC (by simp)
  rw [hA0, hC0] at hfactor
  exact hfactor

theorem grahamSourcePairComponentFiber_mixed_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    {j k l m : V} (hm : m ∉ S) (hj : j ∈ S) (hk : k ∈ S)
    (hl : l ∈ S) :
    grahamSourcePairComponentFiber G beta J S m {j, k} {k, l} =
      currentSum G beta (couplingIn J S) {j, k} *
        currentSum G beta (couplingIn J S) {k, l} *
          grahamComponentExteriorContext G beta J S m := by
  exact grahamSourcePairComponentFiber_factor G beta J S m hm
    {j, k} {k, l}
      (by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hj
        · exact hk)
      (by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hk
        · exact hl)

theorem grahamSourcePairComponentFiber_left_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    {j k m : V} (hm : m ∉ S) (hj : j ∈ S) (hk : k ∈ S) :
    grahamSourcePairComponentFiber G beta J S m {j, k} ∅ =
      currentSum G beta (couplingIn J S) {j, k} *
        currentSum G beta (couplingIn J S) ∅ *
          grahamComponentExteriorContext G beta J S m := by
  exact grahamSourcePairComponentFiber_factor G beta J S m hm
    {j, k} ∅
      (by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hj
        · exact hk)
      (by exact empty_subset S)

theorem grahamSourcePairComponentFiber_right_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    {k l m : V} (hm : m ∉ S) (hk : k ∈ S) (hl : l ∈ S) :
    grahamSourcePairComponentFiber G beta J S m {k, l} ∅ =
      currentSum G beta (couplingIn J S) {k, l} *
        currentSum G beta (couplingIn J S) ∅ *
          grahamComponentExteriorContext G beta J S m := by
  exact grahamSourcePairComponentFiber_factor G beta J S m hm
    {k, l} ∅
      (by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hk
        · exact hl)
      (by exact empty_subset S)

theorem grahamSourcePairComponentFiber_vacuum_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    {m : V} (hm : m ∉ S) :
    grahamSourcePairComponentFiber G beta J S m ∅ ∅ =
      currentSum G beta (couplingIn J S) ∅ ^ 2 *
        grahamComponentExteriorContext G beta J S m := by
  rw [grahamSourcePairComponentFiber_factor G beta J S m hm ∅ ∅
    (by simp) (by simp)]
  ring


theorem grahamSourcePairComponentFiber_det_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    {j k l m : V} (hm : m ∉ S) (hj : j ∈ S) (hk : k ∈ S)
    (hl : l ∈ S) :
    grahamSourcePairComponentFiber G beta J S m {j, k} {k, l} *
        grahamSourcePairComponentFiber G beta J S m ∅ ∅ =
      grahamSourcePairComponentFiber G beta J S m {j, k} ∅ *
        grahamSourcePairComponentFiber G beta J S m {k, l} ∅ := by
  rw [grahamSourcePairComponentFiber_mixed_factor G beta J S hm hj hk hl,
    grahamSourcePairComponentFiber_vacuum_factor G beta J S hm,
    grahamSourcePairComponentFiber_left_factor G beta J S hm hj hk,
    grahamSourcePairComponentFiber_right_factor G beta J S hm hk hl]
  ring

end StatMech.FrontierA
