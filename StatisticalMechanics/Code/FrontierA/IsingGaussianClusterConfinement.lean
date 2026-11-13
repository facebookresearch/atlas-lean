/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianClusterDisentangling
import Code.FrontierA.GrahamWeightedFourCurrent
import Code.Ising.FreeCorrelationDomainMonotonicity












open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteTreeSafeRegion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : Current V) (roots : Finset V) : Finset V :=
  Finset.univ.filter (fun v => ∀ g ∈ roots, ¬ CurrentConnected G m g v)

@[simp] theorem mem_finiteTreeSafeRegion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : Current V) (roots : Finset V) (v : V) :
    v ∈ finiteTreeSafeRegion G m roots ↔
      ∀ g ∈ roots, ¬ CurrentConnected G m g v := by
  simp [finiteTreeSafeRegion]

theorem finiteTreeSafeRegion_subset_compl
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : Current V) (roots : Finset V) :
    finiteTreeSafeRegion G m roots ⊆ rootsᶜ := by
  intro v hv
  rw [Finset.mem_compl]
  intro hvroot
  exact (mem_finiteTreeSafeRegion G m roots v).mp hv v hvroot
    (CurrentConnected.refl G m v)

theorem finiteTreeSafeRegion_closed_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : Current V) (roots : Finset V) {u v : V}
    (hu : u ∈ finiteTreeSafeRegion G m roots)
    (huv : CurrentConnected G m u v) :
    v ∈ finiteTreeSafeRegion G m roots := by
  rw [mem_finiteTreeSafeRegion] at hu ⊢
  intro g hg hgv
  exact hu g hg (CurrentConnected.trans G hgv (CurrentConnected.symm G huv))


theorem finiteTreeSafeRegion_noCrossing
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : Current V) (roots T : Finset V)
    (hev : finiteTreeSafeRegion G m roots = T) :
    NoCrossing G m T := by
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
    have huvC : CurrentConnected G m u v := Adj.reachable ⟨hadj, hpos⟩
    have huSafe : u ∈ finiteTreeSafeRegion G m roots := by simpa [hev] using hu
    have hvNot : v ∉ finiteTreeSafeRegion G m roots := by simpa [hev] using hv
    rw [mem_finiteTreeSafeRegion] at huSafe hvNot
    push Not at hvNot
    obtain ⟨g, hg, hgv⟩ := hvNot
    exact huSafe g hg
      (CurrentConnected.trans G hgv (CurrentConnected.symm G huvC))
  · exfalso
    have hvuC : CurrentConnected G m v u :=
      Adj.reachable ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
    have hvSafe : v ∈ finiteTreeSafeRegion G m roots := by simpa [hev] using hv
    have huNot : u ∉ finiteTreeSafeRegion G m roots := by simpa [hev] using hu
    rw [mem_finiteTreeSafeRegion] at hvSafe huNot
    push Not at huNot
    obtain ⟨g, hg, hgu⟩ := huNot
    exact hvSafe g hg
      (CurrentConnected.trans G hgu (CurrentConnected.symm G hvuC))
  · right
    intro w hw
    rw [Finset.mem_compl]
    rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> assumption



theorem finiteTreeSafeRegion_congr
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m m' : Current V) (roots T : Finset V)
    (hev : finiteTreeSafeRegion G m roots = T)
    (hagree : ∀ e ∈ G.edgeFinset, ¬ edgeInside T e -> m e = m' e) :
    finiteTreeSafeRegion G m' roots = T := by
  have hnm : NoCrossing G m T :=
    finiteTreeSafeRegion_noCrossing G m roots T hev
  have hnm' : NoCrossing G m' T := noCrossing_congr G m m' T hnm hagree
  have hsub := currentSubgraph_restrictCompl_congr G m m' T hagree
  ext v
  constructor
  · intro hvSafe
    by_contra hvT
    have hvNot : v ∉ finiteTreeSafeRegion G m roots := by simpa [hev] using hvT
    rw [mem_finiteTreeSafeRegion] at hvSafe hvNot
    push Not at hvNot
    obtain ⟨g, hg, hgv⟩ := hvNot
    have hgT : g ∉ T := by
      intro hgT
      have hgSafe : g ∈ finiteTreeSafeRegion G m roots := by simpa [hev] using hgT
      exact (mem_finiteTreeSafeRegion G m roots g).mp hgSafe g hg
        (CurrentConnected.refl G m g)
    have hgv' : CurrentConnected G m' g v := by
      apply (currentConnected_iff_compl G m' T hnm' g v hgT).mpr
      have hgvR := (currentConnected_iff_compl G m T hnm g v hgT).mp hgv
      unfold CurrentConnected
      rw [← hsub]
      exact hgvR
    exact hvSafe g hg hgv'
  · intro hvT
    rw [mem_finiteTreeSafeRegion]
    intro g hg hgv
    have hgT : g ∉ T := by
      intro hgT
      have hgSafe : g ∈ finiteTreeSafeRegion G m roots := by simpa [hev] using hgT
      exact (mem_finiteTreeSafeRegion G m roots g).mp hgSafe g hg
        (CurrentConnected.refl G m g)
    exact not_currentConnected_in_S G m' T hnm' g hgT v hvT hgv


noncomputable def finiteTreeSafeRegionFiber
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (roots T : Finset V)
    (A C : Finset V) : Real :=
  gatedSourcePairSum G beta J A C
    (fun n => finiteTreeSafeRegion G n roots = T)

noncomputable def finiteTreeSafeRegionContext
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (roots T : Finset V) : Real :=
  ∑' bd, claim1Context G beta J T
    (fun n => finiteTreeSafeRegion G n roots = T) ∅ ∅ bd

theorem finiteTreeSafeRegionFiber_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (roots T : Finset V)
    (A C : Finset V) (hA : A ⊆ T) (hC : C ⊆ T) :
    finiteTreeSafeRegionFiber G beta J roots T A C =
      currentSum G beta (couplingIn J T) A *
        currentSum G beta (couplingIn J T) C *
          finiteTreeSafeRegionContext G beta J roots T := by
  unfold finiteTreeSafeRegionFiber finiteTreeSafeRegionContext
  have hcongr : ∀ n n' : Current V,
      (∀ e ∈ G.edgeFinset, ¬ edgeInside T e -> n e = n' e) ->
      (finiteTreeSafeRegion G n roots = T ↔
        finiteTreeSafeRegion G n' roots = T) := by
    intro n n' hagree
    constructor
    · intro hn
      exact finiteTreeSafeRegion_congr G n n' roots T hn hagree
    · intro hn'
      exact finiteTreeSafeRegion_congr G n' n roots T hn'
        (fun e he hnot => (hagree e he hnot).symm)
  have hfactor := gatedSourcePairSum_factor G beta J T
    (fun n => finiteTreeSafeRegion G n roots = T)
    (fun n hn => finiteTreeSafeRegion_noCrossing G n roots T hn)
    hcongr A ∅ C ∅ hA (by simp) hC (by simp)
  have hA0 : symmDiff A (∅ : Finset V) = A := by
    ext x
    simp [Finset.mem_symmDiff]
  have hC0 : symmDiff C (∅ : Finset V) = C := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hA0, hC0] at hfactor
  exact hfactor

theorem finiteTreeSafeRegionFiber_sourceReplacement
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (roots T : Finset V)
    (A : Finset V) (hA : A ⊆ T) :
    finiteTreeSafeRegionFiber G beta J roots T A ∅ =
      expectationJ G beta (couplingIn J T) A *
        finiteTreeSafeRegionFiber G beta J roots T ∅ ∅ := by
  rw [finiteTreeSafeRegionFiber_factor G beta J roots T A ∅ hA (by simp),
    finiteTreeSafeRegionFiber_factor G beta J roots T ∅ ∅ (by simp) (by simp),
    StatMech.Ising.acr_eq15_insertion' G beta (couplingIn J T) A]
  ring

theorem finiteTreeSafeRegionFiber_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (roots T A C : Finset V) :
    0 <= finiteTreeSafeRegionFiber G beta J roots T A C := by
  exact gatedSourcePairSum_nonneg G beta J hbeta hJ A C
    (fun n => finiteTreeSafeRegion G n roots = T)



noncomputable def finiteTreeClusterConfinementMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (k l : V) (S : Finset V) : Real :=
  gatedSourcePairSum G beta J {k, l} ∅
    (fun n => k ∈ finiteTreeSafeRegion G n Sᶜ)

theorem finiteTreeClusterConfinementMass_eq_fibers
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (k l : V) (S : Finset V) :
    finiteTreeClusterConfinementMass G beta J k l S =
      ∑ T : Finset V, if k ∈ T then
        finiteTreeSafeRegionFiber G beta J Sᶜ T {k, l} ∅ else 0 := by
  let P : Current V -> Prop := fun n => k ∈ finiteTreeSafeRegion G n Sᶜ
  let f : Current V -> Finset V := fun n => finiteTreeSafeRegion G n Sᶜ
  have hpart := gatedSourcePairSum_partition G beta J {k, l} ∅ P f
  unfold finiteTreeClusterConfinementMass
  change gatedSourcePairSum G beta J {k, l} ∅ P = _
  rw [hpart]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hkT : k ∈ T
  · rw [if_pos hkT]
    unfold finiteTreeSafeRegionFiber
    apply gatedSourcePairSum_congr_sources
    intro p q hp hq
    dsimp only [P, f]
    constructor
    · exact And.left
    · intro hT
      exact ⟨hT, by simpa [hT] using hkT⟩
  · rw [if_neg hkT]
    rw [gatedSourcePairSum_congr_sources G beta J {k, l} ∅
      (fun n => f n = T ∧ P n) (fun _ => False)]
    · unfold gatedSourcePairSum
      simp
    · intro p q hp hq
      constructor
      · rintro ⟨hT, hkSafe⟩
        apply (hkT ?_).elim
        rw [← hT]
        exact hkSafe
      · exact False.elim

theorem sum_finiteTreeSafeRegionFiber_vacuum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (roots : Finset V) :
    ∑ T : Finset V, finiteTreeSafeRegionFiber G beta J roots T ∅ ∅ =
      currentSum G beta J ∅ ^ 2 := by
  let f : Current V -> Finset V := fun n => finiteTreeSafeRegion G n roots
  have hpart := gatedSourcePairSum_partition G beta J ∅ ∅
    (fun _ => True) f
  calc
    (∑ T : Finset V, finiteTreeSafeRegionFiber G beta J roots T ∅ ∅) =
        ∑ T : Finset V, gatedSourcePairSum G beta J ∅ ∅
          (fun n => f n = T ∧ True) := by
      apply Finset.sum_congr rfl
      intro T _
      unfold finiteTreeSafeRegionFiber
      apply gatedSourcePairSum_congr_sources
      intro p q hp hq
      simp only [and_true, f]
    _ = gatedSourcePairSum G beta J ∅ ∅ (fun _ => True) := hpart.symm
    _ = sourcePairSum G beta J ∅ ∅ := gatedSourcePairSum_true G beta J ∅ ∅
    _ = currentSum G beta J ∅ ^ 2 := by
      rw [sourcePairSum_eq_mul]
      ring



theorem finiteTreeClusterConfinementMass_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {k l : V} (hkl : k ≠ l) (S : Finset V) :
    finiteTreeClusterConfinementMass G beta J k l S <=
      expectationJ G beta (couplingIn J S) {k, l} *
        currentSum G beta J ∅ ^ 2 := by
  rw [finiteTreeClusterConfinementMass_eq_fibers]
  rw [← sum_finiteTreeSafeRegionFiber_vacuum G beta J Sᶜ,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T hT
  have hvac := finiteTreeSafeRegionFiber_nonneg
    G beta J hbeta hJ Sᶜ T ∅ ∅
  have hcorrS : 0 <= expectationJ G beta (couplingIn J S) {k, l} :=
    StatMech.Ising.acr_expectationJ_nonneg G beta (couplingIn J S) hbeta
      (fun e => by
        unfold couplingIn
        split <;> simp_all [hJ e]) {k, l}
  by_cases hkT : k ∈ T
  · rw [if_pos hkT]
    by_cases hTS : T ⊆ S
    · by_cases hlT : l ∈ T
      · rw [finiteTreeSafeRegionFiber_sourceReplacement G beta J Sᶜ T
          {k, l} (by
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl
            · exact hkT
            · exact hlT)]
        apply mul_le_mul_of_nonneg_right
        · exact expectationJ_couplingIn_mono_domain G beta J hbeta hJ
            hTS {k, l}
        · exact hvac
      · have hzero : finiteTreeSafeRegionFiber G beta J Sᶜ T {k, l} ∅ = 0 := by
          unfold finiteTreeSafeRegionFiber
          rw [gatedSourcePairSum_congr_sources G beta J {k, l} ∅
            (fun n => finiteTreeSafeRegion G n Sᶜ = T) (fun _ => False)]
          · unfold gatedSourcePairSum
            simp
          · intro p q hp hq
            constructor
            · intro heq
              have hconnP := currentConnected_of_sources_pair G p hkl hp
              have hconn := grahamCurrentConnected_add_right G p q hconnP
              have hkSafe : k ∈ finiteTreeSafeRegion G
                  (ofEdgeFun G (fun e => p e + q e)) Sᶜ := by simpa [heq] using hkT
              have hlSafe := finiteTreeSafeRegion_closed_of_connected G
                (ofEdgeFun G (fun e => p e + q e)) Sᶜ hkSafe hconn
              exact (hlT (by simpa [heq] using hlSafe)).elim
            · exact False.elim
        rw [hzero]
        exact mul_nonneg hcorrS hvac
    · have hzero : finiteTreeSafeRegionFiber G beta J Sᶜ T {k, l} ∅ = 0 := by
        unfold finiteTreeSafeRegionFiber
        rw [gatedSourcePairSum_congr_sources G beta J {k, l} ∅
          (fun n => finiteTreeSafeRegion G n Sᶜ = T) (fun _ => False)]
        · unfold gatedSourcePairSum
          simp
        · intro p q hp hq
          constructor
          · intro heq
            apply hTS
            intro v hv
            have hvSafe : v ∈ finiteTreeSafeRegion G
                (ofEdgeFun G (fun e => p e + q e)) Sᶜ := by simpa [heq] using hv
            have hvCompl := finiteTreeSafeRegion_subset_compl G
              (ofEdgeFun G (fun e => p e + q e)) Sᶜ hvSafe
            simpa using hvCompl
          · exact False.elim
      rw [hzero]
      exact mul_nonneg hcorrS hvac
  · rw [if_neg hkT]
    exact mul_nonneg hcorrS hvac

end StatMech.FrontierA
