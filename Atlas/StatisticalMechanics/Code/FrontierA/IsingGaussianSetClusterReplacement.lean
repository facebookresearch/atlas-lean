/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianClusterDisentangling
import Code.Ising.FreeCorrelationDomainMonotonicity












open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteTreeCurrentCluster
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : Current V) (A : Finset V) : Finset V :=
  Finset.univ.filter (fun v =>
    exists a, a ∈ A ∧ CurrentConnected G n a v)

theorem mem_finiteTreeCurrentCluster
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : Current V) (A : Finset V) (v : V) :
    v ∈ finiteTreeCurrentCluster G n A ↔
      exists a, a ∈ A ∧ CurrentConnected G n a v := by
  simp [finiteTreeCurrentCluster]

theorem subset_finiteTreeCurrentCluster
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : Current V) (A : Finset V) :
    A ⊆ finiteTreeCurrentCluster G n A := by
  intro a ha
  rw [mem_finiteTreeCurrentCluster]
  exact ⟨a, ha, CurrentConnected.refl G n a⟩



theorem finiteTreeCurrentCluster_singleton_eq_compl_notConnComp
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : Current V) (i : V) :
    finiteTreeCurrentCluster G n {i} = (notConnComp G n i)ᶜ := by
  ext v
  rw [mem_finiteTreeCurrentCluster, Finset.mem_compl, mem_notConnComp]
  simp only [Finset.mem_singleton, exists_eq_left, not_not]



theorem finiteTree_clusters_intersect_iff_mem_generated
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m n : Current V) (i k : V) :
    (exists y,
        CurrentConnected G m i y ∧ CurrentConnected G n k y) ↔
      k ∈ finiteTreeCurrentCluster G n
        (finiteTreeCurrentCluster G m {i}) := by
  constructor
  · rintro ⟨y, hiy, hky⟩
    rw [mem_finiteTreeCurrentCluster]
    refine ⟨y, ?_, CurrentConnected.symm G hky⟩
    rw [mem_finiteTreeCurrentCluster]
    exact ⟨i, by simp, hiy⟩
  · intro hk
    rw [mem_finiteTreeCurrentCluster] at hk
    obtain ⟨y, hy, hyk⟩ := hk
    rw [mem_finiteTreeCurrentCluster] at hy
    obtain ⟨i', hi', hiy⟩ := hy
    simp only [Finset.mem_singleton] at hi'
    subst i'
    exact ⟨y, hiy, CurrentConnected.symm G hyk⟩


theorem finiteTreeCurrentCluster_noCrossing
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : Current V) (A T : Finset V)
    (hcluster : finiteTreeCurrentCluster G n A = T) :
    NoCrossing G n T := by
  intro e he hpos
  obtain ⟨⟨u, v⟩, huv⟩ := e.exists_rep
  subst huv
  have hadj : G.Adj u v := by
    rw [mem_edgeFinset, mem_edgeSet] at he
    exact he
  by_cases hu : u ∈ T <;> by_cases hv : v ∈ T
  · left
    intro w hw
    rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> assumption
  · exfalso
    have hu' : u ∈ finiteTreeCurrentCluster G n A := hcluster.symm ▸ hu
    rw [mem_finiteTreeCurrentCluster] at hu'
    obtain ⟨a, ha, hau⟩ := hu'
    have huvConn : CurrentConnected G n u v :=
      Adj.reachable ⟨hadj, hpos⟩
    apply hv
    rw [← hcluster, mem_finiteTreeCurrentCluster]
    exact ⟨a, ha, CurrentConnected.trans G hau huvConn⟩
  · exfalso
    have hv' : v ∈ finiteTreeCurrentCluster G n A := hcluster.symm ▸ hv
    rw [mem_finiteTreeCurrentCluster] at hv'
    obtain ⟨a, ha, hav⟩ := hv'
    have hvuConn : CurrentConnected G n v u :=
      Adj.reachable ⟨hadj.symm, by simpa [Sym2.eq_swap] using hpos⟩
    apply hu
    rw [← hcluster, mem_finiteTreeCurrentCluster]
    exact ⟨a, ha, CurrentConnected.trans G hav hvuConn⟩
  · right
    intro w hw
    rw [Finset.mem_compl]
    rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> assumption



theorem finiteTreeCurrentCluster_congr
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n n' : Current V) (A T : Finset V)
    (hAT : A ⊆ T)
    (hcluster : finiteTreeCurrentCluster G n A = T)
    (hagree : ∀ e ∈ G.edgeFinset, ¬ edgeInside Tᶜ e -> n e = n' e) :
    finiteTreeCurrentCluster G n' A = T := by
  have hn : NoCrossing G n Tᶜ := by
    intro e he hpos
    rcases finiteTreeCurrentCluster_noCrossing G n A T hcluster e he hpos with hT | hTc
    · exact Or.inr (by simpa only [compl_compl] using hT)
    · exact Or.inl hTc
  have hn' : NoCrossing G n' Tᶜ :=
    noCrossing_congr G n n' Tᶜ hn hagree
  have hsub := currentSubgraph_restrictCompl_congr G n n' Tᶜ hagree
  ext v
  change (v ∈ finiteTreeCurrentCluster G n' A) ↔ v ∈ T
  rw [← hcluster, mem_finiteTreeCurrentCluster,
    mem_finiteTreeCurrentCluster]
  by_cases hv : v ∈ Tᶜ
  · have hvT : v ∉ T := by simpa using hv
    constructor
    · rintro ⟨a, ha, hav⟩
      have haTc : a ∉ Tᶜ := by
        simpa using hAT ha
      exact (not_currentConnected_in_S G n' Tᶜ hn' a haTc v hv hav).elim
    · rintro ⟨a, ha, hav⟩
      apply (hvT ?_).elim
      rw [← hcluster, mem_finiteTreeCurrentCluster]
      exact ⟨a, ha, hav⟩
  · have haTc (a : V) (ha : a ∈ A) : a ∉ Tᶜ := by
      simpa using hAT ha
    have hconn (a : V) (ha : a ∈ A) :
        CurrentConnected G n' a v ↔ CurrentConnected G n a v := by
      rw [currentConnected_iff_compl G n' Tᶜ hn' a v (haTc a ha),
        currentConnected_iff_compl G n Tᶜ hn a v (haTc a ha)]
      unfold CurrentConnected
      rw [hsub]
    constructor
    · rintro ⟨a, ha, hav⟩
      exact ⟨a, ha, (hconn a ha).mp hav⟩
    · rintro ⟨a, ha, hav⟩
      exact ⟨a, ha, (hconn a ha).mpr hav⟩



theorem finiteTree_setCluster_sourceReplacement
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A T : Finset V)
    {k l : V} (hAT : A ⊆ T) (hk : k ∉ T) (hl : l ∉ T) :
    gatedSourcePairSum G beta J {k, l} ∅
        (fun n => finiteTreeCurrentCluster G n A = T) =
      expectationJ G beta (couplingIn J Tᶜ) {k, l} *
        gatedSourcePairSum G beta J ∅ ∅
          (fun n => finiteTreeCurrentCluster G n A = T) := by
  let P : Current V -> Prop := fun n => finiteTreeCurrentCluster G n A = T
  have hno : forall n, P n -> NoCrossing G n Tᶜ := by
    intro n hn
    intro e he hpos
    rcases finiteTreeCurrentCluster_noCrossing G n A T hn e he hpos with hT | hTc
    · exact Or.inr (by simpa only [compl_compl] using hT)
    · exact Or.inl hTc
  have hcongr : forall n n' : Current V,
      (∀ e ∈ G.edgeFinset, ¬ edgeInside Tᶜ e -> n e = n' e) ->
      (P n ↔ P n') := by
    intro n n' hagree
    constructor
    · intro hn
      exact finiteTreeCurrentCluster_congr G n n' A T hAT hn hagree
    · intro hn'
      exact finiteTreeCurrentCluster_congr G n' n A T hAT hn'
        (fun e he hnot => (hagree e he hnot).symm)
  have hpair := gatedSourcePairSum_factor G beta J Tᶜ P hno hcongr
    {k, l} ∅ ∅ ∅
    (by
      intro x hx
      rw [Finset.mem_compl]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hk
      · exact hl)
    (Finset.empty_subset _)
    (Finset.empty_subset _)
    (Finset.empty_subset _)
  have hvac := gatedSourcePairSum_factor G beta J Tᶜ P hno hcongr
    ∅ ∅ ∅ ∅
    (Finset.empty_subset _)
    (Finset.empty_subset _)
    (Finset.empty_subset _)
    (Finset.empty_subset _)
  have hpairEmpty : ({k, l} : Finset V) ∆ ∅ = {k, l} := by
    ext x
    simp [Finset.mem_symmDiff]
  have hempty : (∅ : Finset V) ∆ ∅ = ∅ := by
    ext x
    simp
  rw [hpairEmpty, hempty] at hpair
  rw [hempty] at hvac
  change gatedSourcePairSum G beta J {k, l} ∅ P =
    expectationJ G beta (couplingIn J Tᶜ) {k, l} *
      gatedSourcePairSum G beta J ∅ ∅ P
  rw [hpair, hvac,
    StatMech.Ising.acr_eq15_insertion' G beta (couplingIn J Tᶜ) {k, l}]
  ring

end StatMech.FrontierA
