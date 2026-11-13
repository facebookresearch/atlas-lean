/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRandomClusterFKG
import Code.FrontierD.FKRectCutPushforward
import Code.FK.EdgeConfigEventLaw



open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

open StatMech

local instance fkRectCriticalFullGraphDecidableRel (R : FKRectTorus) :
    DecidableRel (fkRectTorusGraph R).Adj := Classical.decRel _



theorem fkRectGraphConfigurationExtend_configurationGraphEquiv
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectGraphConfigurationExtend R
        (fkRectConfigurationGraphEquiv R omega) =
      fkRectFullGraphConfiguration R omega := by
  funext e
  by_cases he : e ∈ (fkRectTorusGraph R).edgeSet
  · simp [fkRectGraphConfigurationExtend, fkRectFullGraphConfiguration,
      fkRectConfigurationGraphEquiv, he]
  · rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R omega he]
    simp [fkRectGraphConfigurationExtend, he]



def fkRectFullEdgeConfigEquiv (R : FKRectTorus) :
    R.Configuration ≃ FK.ecz_ClosedOff (fkRectTorusGraph R) where
  toFun omega := ⟨fkRectFullGraphConfiguration R omega, by
    intro e he
    apply fkRectFullGraphConfiguration_eq_false_of_not_edge R omega
    simpa only [SimpleGraph.mem_edgeFinset] using he⟩
  invFun sigma a := sigma.1 (fkRectTorusIndexedEdge R a)
  left_inv omega := by
    funext a
    exact fkRectFullGraphConfiguration_indexedEdge R omega a
  right_inv sigma := by
    apply Subtype.ext
    funext e
    change fkRectFullGraphConfiguration R
        (fun a => sigma.1 (fkRectTorusIndexedEdge R a)) e = sigma.1 e
    by_cases he : e ∈ (fkRectTorusGraph R).edgeSet
    · obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 he
      rw [← ha, fkRectFullGraphConfiguration_indexedEdge]
    · rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ he]
      symm
      apply sigma.2 e
      simpa only [SimpleGraph.mem_edgeFinset] using he



def fkRectFullEdgeEvent (R : FKRectTorus) (A : Set R.Configuration) :
    Set (FK.ecz_ClosedOff (fkRectTorusGraph R)) :=
  {sigma | (fkRectFullEdgeConfigEquiv R).symm sigma ∈ A}



theorem fkWeight_fullEdgeConfigEquiv
    (R : FKRectTorus) (p q : Real) (omega : R.Configuration) :
    FK.fkWeight (fkRectTorusGraph R) p q
        (fkRectFullEdgeConfigEquiv R omega).1 =
      fkRectRandomClusterWeight R p q omega := by
  change FK.fkWeight (fkRectTorusGraph R) p q
      (fkRectFullGraphConfiguration R omega) = _
  rw [← fkRectGraphConfigurationExtend_configurationGraphEquiv]
  exact fkWeight_configurationGraphEquiv R p q omega



theorem fkRectFull_ecz_eventWeight_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) :
    FK.ecz_eventWeight (fkRectTorusGraph R) (fkRectCriticalP q) q
        (fkRectFullEdgeEvent R A) =
      fkRectCriticalEdgeFactor R q *
        ∑ omega : R.Configuration,
          A.indicator (fun omega =>
            fkRectCriticalReducedWeight R q omega) omega := by
  unfold FK.ecz_eventWeight
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (fkRectFullEdgeConfigEquiv R)
  intro omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (show fkRectFullEdgeConfigEquiv R omega ∈
        fkRectFullEdgeEvent R A by simpa [fkRectFullEdgeEvent])]
    rw [fkWeight_fullEdgeConfigEquiv,
      fkRectRandomClusterWeight_critical_eq R hq]
    rfl
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (show fkRectFullEdgeConfigEquiv R omega ∉
        fkRectFullEdgeEvent R A by simpa [fkRectFullEdgeEvent])]
    simp



theorem fkRectFull_ecz_fkZEdge_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    FK.ecz_fkZEdge (fkRectTorusGraph R) (fkRectCriticalP q) q =
      fkRectCriticalEdgeFactor R q * fkRectCriticalReducedZ R q := by
  rw [← show (∑ omega : R.Configuration,
      (Set.univ : Set R.Configuration).indicator
        (fun omega => fkRectCriticalReducedWeight R q omega) omega) =
      fkRectCriticalReducedZ R q by simp [fkRectCriticalReducedZ]]
  simpa [fkRectFullEdgeEvent, FK.ecz_eventWeight, FK.ecz_fkZEdge] using
    fkRectFull_ecz_eventWeight_eq R hq
      (Set.univ : Set R.Configuration)



theorem fkRectCriticalEventMass_eq_fullGraph
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q A =
      ∑ sigma : ConfigSpace (Sym2 R.Vertex),
        (FK.ecz_closeOff (fkRectTorusGraph R) ⁻¹'
          fkRectFullEdgeEvent R A).indicator (fun _ => (1 : Real)) sigma *
          FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q sigma := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [FK.ecz_eventProb_eq,
    fkRectFull_ecz_eventWeight_eq R hq0,
    fkRectFull_ecz_fkZEdge_eq R hq0]
  unfold fkRectCriticalEventMass fkRectCriticalRandomClusterProb
  have hfactor : fkRectCriticalEdgeFactor R q ≠ 0 :=
    (fkRectCriticalEdgeFactor_pos R hq0).ne'
  have hZ : fkRectCriticalReducedZ R q ≠ 0 :=
    (fkRectCriticalReducedZ_pos R hq0).ne'
  rw [show (∑ omega : R.Configuration,
      A.indicator
        (fun omega => fkRectCriticalReducedWeight R q omega /
          fkRectCriticalReducedZ R q) omega) =
      (∑ omega : R.Configuration,
        A.indicator (fun omega =>
          fkRectCriticalReducedWeight R q omega) omega) /
        fkRectCriticalReducedZ R q by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro omega _
      by_cases homega : omega ∈ A <;>
        simp [Set.indicator, homega]]
  field_simp

end

end StatMech.FrontierD
