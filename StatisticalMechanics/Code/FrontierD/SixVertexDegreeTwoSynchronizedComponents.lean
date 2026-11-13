/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

local instance synchronizedComponentsActiveDecidable
    {T : EvenTorus} {omega eta : SixVertexArrows T} :
    DecidablePred (activeBlackDart (omega := omega) (eta := eta)) :=
  Classical.decPred _


noncomputable def sixVertexDegreeTwoBranchPredecessor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (branch : Bool)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    SixVertexOrientedDisagreementDart omega eta :=
  ((doubledAlignedFirstReturnPerm homega heta hdegree).symm (d, branch)).1




noncomputable def sixVertexDegreeTwoSynchronizedGraph
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    SimpleGraph (SixVertexOrientedDisagreementDart omega eta) where
  Adj a b := a ≠ b ∧ ∃ d,
    (a = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d ∧
      b = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) ∨
    (b = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d ∧
      a = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d)
  symm := by
    rintro a b ⟨hne, d, h | h⟩
    · exact ⟨hne.symm, d, Or.inr ⟨h.1, h.2⟩⟩
    · exact ⟨hne.symm, d, Or.inl ⟨h.1, h.2⟩⟩
  loopless := by
    exact ⟨fun a h => h.1 rfl⟩

theorem sixVertexDegreeTwoSynchronizedGraph_predecessors_reachable
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Reachable
      (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d)
      (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) := by
  by_cases heq : sixVertexDegreeTwoBranchPredecessor homega heta hdegree
      false d = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d
  · simpa [heq] using (SimpleGraph.Reachable.refl
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree)
      (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d))
  · exact SimpleGraph.Adj.reachable ⟨heq, d, Or.inl ⟨rfl, rfl⟩⟩



noncomputable def sixVertexDegreeTwoSynchronizedEdgeTransition
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (edge : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Dart) :
    SixVertexOrientedDisagreementDart omega eta :=
  Classical.choose edge.2.2



theorem sixVertexDegreeTwoSynchronizedEdgeTransition_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (edge : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Dart) :
    (edge.1.1 = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false
        (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree edge) /\
      edge.1.2 = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true
        (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree edge)) \/
    (edge.1.2 = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false
        (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree edge) /\
      edge.1.1 = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true
        (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree edge)) :=
  Classical.choose_spec edge.2.2


noncomputable def sixVertexDegreeTwoSynchronizedComponentCharge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    Int := by
  classical
  exact ∑ d : SixVertexOrientedDisagreementDart omega eta,
    if (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk d =
        component then sixVertexDegreeTwoStrandStepSeamSign hdegree d else 0

noncomputable def sixVertexDegreeTwoSynchronizedTotalComponentCharge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) : Int :=
  ∑ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
    sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component


noncomputable def sixVertexDegreeTwoSynchronizedComponentPositiveDarts
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    Finset (SixVertexOrientedDisagreementDart omega eta) := by
  classical
  exact Finset.univ.filter fun dart =>
    (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
        dart = component /\
      sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 1



theorem sixVertexDegreeTwoSynchronizedComponentCharge_le_positiveDarts
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component ≤
      (sixVertexDegreeTwoSynchronizedComponentPositiveDarts homega heta hdegree
        component).card := by
  classical
  unfold sixVertexDegreeTwoSynchronizedComponentCharge
  calc
    (∑ dart : SixVertexOrientedDisagreementDart omega eta,
      if (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
          dart = component then
        sixVertexDegreeTwoStrandStepSeamSign hdegree dart else 0) ≤
        ∑ dart : SixVertexOrientedDisagreementDart omega eta,
          if dart ∈ sixVertexDegreeTwoSynchronizedComponentPositiveDarts
              homega heta hdegree component then (1 : Int) else 0 := by
      apply Finset.sum_le_sum
      intro dart _
      by_cases hcomponent :
          (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
            dart = component
      · rcases sixVertexDegreeTwoOrderedStep_zeroOrUnit hdegree dart with
          hzero | hpos | hneg
        · simp [sixVertexDegreeTwoSynchronizedComponentPositiveDarts,
            hcomponent, hzero]
        · simp [sixVertexDegreeTwoSynchronizedComponentPositiveDarts,
            hcomponent, hpos]
        · simp [sixVertexDegreeTwoSynchronizedComponentPositiveDarts,
            hcomponent, hneg]
      · simp [sixVertexDegreeTwoSynchronizedComponentPositiveDarts, hcomponent]
    _ = (sixVertexDegreeTwoSynchronizedComponentPositiveDarts homega heta hdegree
          component).card := by
      simp



theorem exists_two_sixVertexDegreeTwoSynchronizedComponentPositiveDarts
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hcharge : 2 ≤
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component) :
    ∃ first second : SixVertexOrientedDisagreementDart omega eta,
      first ≠ second /\
        first ∈ sixVertexDegreeTwoSynchronizedComponentPositiveDarts
          homega heta hdegree component /\
        second ∈ sixVertexDegreeTwoSynchronizedComponentPositiveDarts
          homega heta hdegree component := by
  classical
  let positive := sixVertexDegreeTwoSynchronizedComponentPositiveDarts
    homega heta hdegree component
  have hcardInt : (2 : Int) ≤ positive.card :=
    hcharge.trans
      (sixVertexDegreeTwoSynchronizedComponentCharge_le_positiveDarts
        homega heta hdegree component)
  have hcard : 1 < Fintype.card {dart // dart ∈ positive} := by
    rw [Fintype.card_coe]
    omega
  obtain ⟨first, second, hne⟩ := Fintype.exists_pair_of_one_lt_card hcard
  exact ⟨first, second, fun heq => hne (Subtype.ext heq), first.2, second.2⟩



structure SixVertexDegreeTwoSynchronizedHighChargeSeed
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    where
  first : SixVertexOrientedDisagreementDart omega eta
  second : SixVertexOrientedDisagreementDart omega eta
  distinct : first ≠ second
  first_mem : first ∈
    sixVertexDegreeTwoSynchronizedComponentPositiveDarts homega heta hdegree component
  second_mem : second ∈
    sixVertexDegreeTwoSynchronizedComponentPositiveDarts homega heta hdegree component
  connected :
    (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Reachable first second


theorem sixVertexDegreeTwoSynchronizedHighChargeSeed_nonempty
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hcharge : 2 ≤
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component) :
    Nonempty
      (SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
        component) := by
  classical
  obtain ⟨first, second, hne, hfirst, hsecond⟩ :=
    exists_two_sixVertexDegreeTwoSynchronizedComponentPositiveDarts
      homega heta hdegree component hcharge
  have hfirstComponent :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
          first = component :=
    (Finset.mem_filter.mp hfirst).2.1
  have hsecondComponent :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
          second = component :=
    (Finset.mem_filter.mp hsecond).2.1
  have hconnected :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Reachable
        first second :=
    ConnectedComponent.exact
      (hfirstComponent.trans hsecondComponent.symm)
  exact ⟨⟨first, second, hne, hfirst, hsecond, hconnected⟩⟩



noncomputable def sixVertexDegreeTwoSynchronizedHighChargeSeed
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hcharge : 2 ≤
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component) :
    SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component :=
  Classical.choice
    (sixVertexDegreeTwoSynchronizedHighChargeSeed_nonempty homega heta hdegree
      component hcharge)



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.walk
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Walk
      seed.first seed.second :=
  (Classical.choice seed.connected).toPath




theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.walk_isPath
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.walk.IsPath :=
  (Classical.choice seed.connected).toPath.isPath



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.walk_support_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.walk.support.Nodup :=
  seed.walk_isPath.support_nodup



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.walk_length_pos
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    0 < seed.walk.length := by
  by_contra hnot
  have hzero : seed.walk.length = 0 := by omega
  have hendpoints : seed.first = seed.second := by
    exact SimpleGraph.Walk.eq_of_length_eq_zero hzero
  exact seed.distinct hendpoints


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    List (SixVertexOrientedDisagreementDart omega eta) :=
  seed.walk.darts.map
    (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree)



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions_length
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.transitions.length = seed.walk.length := by
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions,
    SimpleGraph.Walk.length_darts]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions_ne_nil
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.transitions ≠ [] := by
  intro hempty
  have hzero : seed.transitions.length = 0 := by simp [hempty]
  rw [seed.transitions_length] at hzero
  exact (Nat.ne_of_gt seed.walk_length_pos) hzero



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (i : Fin seed.walk.length) :
    SixVertexOrientedDisagreementDart omega eta :=
  sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree
    ⟨(seed.walk.getVert i, seed.walk.getVert (i + 1)),
      seed.walk.adj_getVert_succ i.isLt⟩



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (i : Fin seed.walk.length) :
    (seed.walk.getVert i =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree false
        (seed.transitionAt i) /\
      seed.walk.getVert (i + 1) =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree true
        (seed.transitionAt i)) \/
    (seed.walk.getVert (i + 1) =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree false
        (seed.transitionAt i) /\
      seed.walk.getVert i =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree true
        (seed.transitionAt i)) := by
  exact sixVertexDegreeTwoSynchronizedEdgeTransition_endpoints homega heta
    hdegree ⟨(seed.walk.getVert i, seed.walk.getVert (i + 1)),
      seed.walk.adj_getVert_succ i.isLt⟩



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_getVert_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (i : Fin seed.walk.length) :
    (seed.walk.getVert i =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree false
          (seed.transitionAt i) /\
      seed.walk.getVert (i + 1) =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree true
          (seed.transitionAt i)) \/
    (seed.walk.getVert (i + 1) =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree false
          (seed.transitionAt i) /\
      seed.walk.getVert i =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree true
          (seed.transitionAt i)) := by
  exact seed.transitionAt_endpoints i



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    Function.Injective seed.transitionAt := by
  intro i j hij
  have hi := seed.transitionAt_getVert_endpoints i
  have hj := seed.transitionAt_getVert_endpoints j
  rw [hij] at hi
  have hget {a b : Nat} (ha : a ≤ seed.walk.length)
      (hb : b ≤ seed.walk.length)
      (h : seed.walk.getVert a = seed.walk.getVert b) : a = b :=
    seed.walk_isPath.getVert_injOn ha hb h
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · apply Fin.ext
    exact hget i.isLt.le j.isLt.le (hi.1.trans hj.1.symm)
  · have hfirst : i.val = j.val + 1 :=
      hget i.isLt.le (Nat.succ_le_of_lt j.isLt) (hi.1.trans hj.1.symm)
    have hsecond : i.val + 1 = j.val :=
      hget (Nat.succ_le_of_lt i.isLt) j.isLt.le (hi.2.trans hj.2.symm)
    omega
  · have hfirst : i.val + 1 = j.val :=
      hget (Nat.succ_le_of_lt i.isLt) j.isLt.le (hi.1.trans hj.1.symm)
    have hsecond : i.val = j.val + 1 :=
      hget i.isLt.le (Nat.succ_le_of_lt j.isLt) (hi.2.trans hj.2.symm)
    omega
  · apply Fin.ext
    exact hget i.isLt.le j.isLt.le (hi.2.trans hj.2.symm)



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionEmbedding
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    Fin seed.walk.length ↪ SixVertexOrientedDisagreementDart omega eta :=
  ⟨seed.transitionAt, seed.transitionAt_injective⟩



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_eq_get
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (i : Fin seed.walk.length) :
    seed.transitionAt i =
      seed.transitions.get (Fin.cast seed.transitions_length.symm i) := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt
    SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions
  simp only [List.get_eq_getElem, List.getElem_map]
  congr 1
  exact (seed.walk.darts_getElem_eq_getVert i
    (by simpa [SimpleGraph.Walk.length_darts] using i.isLt)).symm


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.transitions.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  let e : Fin seed.transitions.length ≃ Fin seed.walk.length :=
    finCongr seed.transitions_length
  apply e.injective
  apply seed.transitionAt_injective
  rw [seed.transitionAt_eq_get (e i), seed.transitionAt_eq_get (e j)]
  simpa [e] using hij




noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    List (DoubledAlignedState omega eta) :=
  seed.transitions.flatMap fun dart => [(dart, false), (dart, true)]

@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.mem_splitStates_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    x ∈ seed.splitStates ↔ x.1 ∈ seed.transitions := by
  rcases x with ⟨dart, branch⟩
  cases branch <;>
    simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates]



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.branchSwap_mem_splitStates_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    doubledAlignedBranchSwap x ∈ seed.splitStates ↔ x ∈ seed.splitStates := by
  rw [seed.mem_splitStates_iff, seed.mem_splitStates_iff]
  rfl

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates_length
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.splitStates.length = seed.transitions.length * 2 := by
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates_ne_nil
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.splitStates ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, seed.splitStates_length]
  exact Nat.mul_pos (List.length_pos_of_ne_nil seed.transitions_ne_nil)
    (by norm_num)



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.splitStates.Nodup := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates
  rw [List.nodup_flatMap]
  refine ⟨?_, seed.transitions_nodup.imp ?_⟩
  · intro dart hdart
    simp
  · intro first second hne
    simp [List.disjoint_left, hne]



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.splitBoundary_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    (doubledAlignedBoundarySegments homega heta hdegree false
      seed.splitStates).Nodup :=
  doubledAlignedBoundarySegments_nodup homega heta hdegree false
    seed.splitStates seed.splitStates_nodup


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.first_seamSign
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    sixVertexDegreeTwoStrandStepSeamSign hdegree seed.first = 1 := by
  classical
  exact (Finset.mem_filter.mp seed.first_mem).2.2


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.second_seamSign
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    sixVertexDegreeTwoStrandStepSeamSign hdegree seed.second = 1 := by
  classical
  exact (Finset.mem_filter.mp seed.second_mem).2.2


abbrev SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :=
  {dart : FKMedialBlackDart T // dart ∈
    doubledAlignedBoundarySegments homega heta hdegree false seed.splitStates}


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.splitBoundary_nonempty
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    Nonempty (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed) := by
  cases hstates : seed.splitStates with
  | nil => exact False.elim (seed.splitStates_ne_nil hstates)
  | cons x states =>
      refine ⟨⟨doubledAlignedBlackDart homega heta hdegree false x, ?_⟩⟩
      rw [doubledAlignedBlackDart_mem_boundarySegments_iff, hstates]
      simp


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.splitBoundary_card_pos
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    0 < Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed) :=
  Fintype.card_pos_iff.mpr seed.splitBoundary_nonempty


noncomputable def sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool)
    (i : Fin (Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))) :
    T.Vertex × Bool :=
  sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer
    ((Fintype.equivFin
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)).symm i).1

theorem sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed layer) := by
  intro first second heq
  apply (Fintype.equivFin
    (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)).symm.injective
  apply Subtype.ext
  unfold sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey at heq
  cases layer
  · exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)).injective heq
  · apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)).injective heq


noncomputable def sixVertexDegreeTwoSynchronizedSplitBoundaryEmbedding
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) :
    Fin (Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)) ↪
      T.Vertex × Bool :=
  ⟨sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed layer,
    sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed layer⟩



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.occurrenceEquiv
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    Equiv.Perm (FKLayeredStrandSlot T) :=
  fkIndexedOccurrenceSlotEquiv
    (Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)

@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.occurrenceEquiv_self
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (slot : FKLayeredStrandSlot T) :
    seed.occurrenceEquiv (seed.occurrenceEquiv slot) = slot := by
  exact fkIndexedOccurrenceSlotEquiv_apply_self _ _ _ slot


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.occurrenceEquiv_symm
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.occurrenceEquiv.symm = seed.occurrenceEquiv := by
  apply Equiv.ext
  intro slot
  apply seed.occurrenceEquiv.injective
  simp



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.desiredTargetBoundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    Equiv.Perm (FKLayeredStrandSlot T) :=
  seed.occurrenceEquiv.trans
    ((fkColoredLayeredStrandSlotBoundaryPerm fun layer =>
      ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        layer).pairing).trans seed.occurrenceEquiv)



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.desiredTargetBoundary_intertwining
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (slot : FKLayeredStrandSlot T) :
    seed.occurrenceEquiv (seed.desiredTargetBoundary slot) =
      fkColoredLayeredStrandSlotBoundaryPerm
        (fun layer =>
          ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
            layer).pairing)
        (seed.occurrenceEquiv slot) := by
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.desiredTargetBoundary,
    Equiv.trans_apply]





structure SixVertexDegreeTwoSynchronizedSplitColorTarget
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) where
  pairing : Bool -> FKMedialLoopPairing T
  slotColorInvariant :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      pairing
      (Fintype.card
        (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)



noncomputable def SixVertexDegreeTwoSynchronizedSplitColorTarget.toSplice
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (target : SixVertexDegreeTwoSynchronizedSplitColorTarget seed) :
    FKColoredStrandSplice
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) :=
  fkColoredSlotColorInvariantSplice
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    target.pairing
    (Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)
    target.slotColorInvariant




structure SixVertexDegreeTwoSynchronizedExactBoundaryTarget
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) where
  pairing : Bool -> FKMedialLoopPairing T
  boundary_eq :
    fkColoredLayeredStrandSlotBoundaryPerm pairing = seed.desiredTargetBoundary



theorem SixVertexDegreeTwoSynchronizedExactBoundaryTarget.slotIntertwining
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (target : SixVertexDegreeTwoSynchronizedExactBoundaryTarget seed) :
    FKColoredIndexedOccurrenceSlotIntertwining
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      target.pairing
      (Fintype.card
        (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed) := by
  intro slot
  change seed.occurrenceEquiv
      (fkColoredLayeredStrandSlotBoundaryPerm target.pairing slot) = _
  rw [target.boundary_eq]
  exact seed.desiredTargetBoundary_intertwining slot



theorem SixVertexDegreeTwoSynchronizedExactBoundaryTarget.slotColorInvariant
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (target : SixVertexDegreeTwoSynchronizedExactBoundaryTarget seed) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      target.pairing
      (Fintype.card
        (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed) := by
  intro slot
  rw [target.slotIntertwining slot]
  exact fkColoredLayeredSlotColor_boundaryPerm
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    (seed.occurrenceEquiv slot)



noncomputable def SixVertexDegreeTwoSynchronizedExactBoundaryTarget.toColorTarget
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (target : SixVertexDegreeTwoSynchronizedExactBoundaryTarget seed) :
    SixVertexDegreeTwoSynchronizedSplitColorTarget seed :=
  ⟨target.pairing, target.slotColorInvariant⟩



noncomputable def SixVertexDegreeTwoSynchronizedExactBoundaryTarget.toSplice
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (target : SixVertexDegreeTwoSynchronizedExactBoundaryTarget seed) :
    FKColoredStrandSplice
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) :=
  FKColoredStrandSplice.ofIndexedSlotIntertwining
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    target.pairing
    (Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)
    target.slotIntertwining



noncomputable def SixVertexDegreeTwoSynchronizedExactBoundaryTarget.colorSplice
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (target : SixVertexDegreeTwoSynchronizedExactBoundaryTarget seed) :
    FKColoredStrandSplice
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) :=
  fkColoredSlotColorInvariantSplice
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    target.pairing
    (Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)
    target.slotColorInvariant


structure SixVertexDegreeTwoSynchronizedSupportedSplitTarget
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) where
  target : SixVertexDegreeTwoSynchronizedSplitColorTarget seed
  seamDelta_false : target.toSplice.seamDelta false = 1
  seamDelta_true : target.toSplice.seamDelta true = -1
  fine :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((target.toSplice.target false).arrows.horizontal,
          (target.toSplice.target true).arrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
          false).arrows.horizontal,
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
            true).arrows.horizontal)
  twoCycle :
    sixVertexPairAtMostTwoCycleRelated
      ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
          false).arrows,
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
          true).arrows)
      ((target.toSplice.target false).arrows,
        (target.toSplice.target true).arrows)



theorem SixVertexDegreeTwoSynchronizedSupportedSplitTarget.preservesTotalC
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (supported : SixVertexDegreeTwoSynchronizedSupportedSplitTarget seed) :
    supported.target.toSplice.PreservesTotalC := by
  unfold FKColoredStrandSplice.PreservesTotalC
  rw [← supported.target.toSplice.target_totalC_eq_slotPairEqualCount,
    ← fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount]
  have htotal := sixVertexPairAtMostTwoCycleFineRelated_totalC
    ⟨supported.twoCycle, supported.fine.symm⟩
  simpa [fkColoredLoopPairingPairTotalC] using htotal.symm



noncomputable def SixVertexDegreeTwoSynchronizedSupportedSplitTarget.toFineRoutedKey
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (supported : SixVertexDegreeTwoSynchronizedSupportedSplitTarget seed) :
    FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) :=
  FKColoredFineTwoCycleUnitTransferRoutedKey.ofSlotColorInvariant
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    supported.target.pairing
    (Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)
    supported.target.slotColorInvariant
    supported.preservesTotalC
    supported.seamDelta_false
    supported.seamDelta_true
    supported.fine
    supported.twoCycle





structure SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) where
  branch : Bool → SixVertexDegreeTwoSynchronizedSupportedSplitTarget seed
  target_distinct :
    (branch false).target.toSplice.target ≠
      (branch true).target.toSplice.target

namespace SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets



noncomputable def key
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (paired : SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets seed)
    (choice : Bool) :
    FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) :=
  (paired.branch choice).toFineRoutedKey

@[simp] theorem key_splice
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (paired : SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets seed)
    (choice : Bool) :
    (paired.key choice).splice =
      (paired.branch choice).target.toSplice := by
  rfl




@[simp] theorem key_recovers_source
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (paired : SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets seed)
    (choice : Bool) :
    (paired.key choice).splice.symm.target =
      sixVertexDegreeTwoAlignedColoredSource homega heta hdegree :=
  (paired.key choice).toFKColoredUnitTransferRoutedKey.recover


theorem key_target_distinct
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (paired : SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets seed) :
    (paired.key false).splice.target ≠
      (paired.key true).splice.target := by
  simpa using paired.target_distinct

end SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets



structure SixVertexDegreeTwoSynchronizedSupportedExactBoundaryTarget
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) where
  target : SixVertexDegreeTwoSynchronizedExactBoundaryTarget seed
  seamDelta_false : target.colorSplice.seamDelta false = 1
  seamDelta_true : target.colorSplice.seamDelta true = -1
  fine :
    sixVertexHorizontalPairBoundedFineRowProfile
        (((target.colorSplice.target false).arrows.horizontal,
          (target.colorSplice.target true).arrows.horizontal)) =
      sixVertexHorizontalPairBoundedFineRowProfile
        (((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
          false).arrows.horizontal,
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
            true).arrows.horizontal))
  twoCycle :
    sixVertexPairAtMostTwoCycleRelated
      ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
          false).arrows,
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
          true).arrows)
      ((target.colorSplice.target false).arrows,
        (target.colorSplice.target true).arrows)



theorem
    SixVertexDegreeTwoSynchronizedSupportedExactBoundaryTarget.preservesTotalC
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (supported :
      SixVertexDegreeTwoSynchronizedSupportedExactBoundaryTarget seed) :
    supported.target.colorSplice.PreservesTotalC := by
  unfold FKColoredStrandSplice.PreservesTotalC
  rw [← supported.target.colorSplice.target_totalC_eq_slotPairEqualCount,
    ← fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount]
  have htotal := sixVertexPairAtMostTwoCycleFineRelated_totalC
    ⟨supported.twoCycle, supported.fine.symm⟩
  simpa [fkColoredLoopPairingPairTotalC] using htotal.symm



noncomputable def SixVertexDegreeTwoSynchronizedSupportedExactBoundaryTarget.toFineRoutedKey
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (supported : SixVertexDegreeTwoSynchronizedSupportedExactBoundaryTarget seed) :
    FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) :=
  FKColoredFineTwoCycleUnitTransferRoutedKey.ofSlotColorInvariant
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    supported.target.pairing
    (Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)
    supported.target.slotColorInvariant
    supported.preservesTotalC
    supported.seamDelta_false
    supported.seamDelta_true
    supported.fine
    supported.twoCycle


theorem sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_exists_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T) :
    (∃ i, sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed layer i =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer dart) ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        seed.splitStates := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    let occurrence : SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence
        seed :=
      (Fintype.equivFin
        (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)).symm i
    have hdart : occurrence.1 = dart := by
      cases layer
      · exact (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)).injective hi
      · apply (alignedBlackDartLayerSwap homega heta hdegree).injective
        exact (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)).injective hi
    rw [← hdart]
    exact occurrence.2
  · intro hdart
    let occurrence : SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence
        seed := ⟨dart, hdart⟩
    let i := Fintype.equivFin
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed) occurrence
    refine ⟨i, ?_⟩
    unfold sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)



theorem sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
      seed.splitStates) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card
          (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
        (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
        (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) =
      (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
        hdegree (!layer) dart) := by
  classical
  let occurrence : SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence
      seed := ⟨dart, hdart⟩
  let i := Fintype.equivFin
    (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed) occurrence
  have hkey (currentLayer : Bool) :
      sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed currentLayer i =
        sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
          currentLayer dart := by
    unfold sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)
  rw [← hkey layer, fkIndexedOccurrenceSlotEquiv_apply_key, hkey]



theorem sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply_of_not_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false
      seed.splitStates) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card
          (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
        (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
        (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) =
      (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
        hdegree layer dart) := by
  apply fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
  intro hexists
  exact hdart
    ((sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_exists_iff seed layer
      dart).mp hexists)



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.boundary_branchSwap_mem_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    doubledAlignedBlackDart homega heta hdegree false
        (doubledAlignedBranchSwap x) ∈
        doubledAlignedBoundarySegments homega heta hdegree false
          seed.splitStates ↔
      doubledAlignedBlackDart homega heta hdegree false x ∈
        doubledAlignedBoundarySegments homega heta hdegree false
          seed.splitStates := by
  rw [doubledAlignedBlackDart_mem_boundarySegments_iff,
    doubledAlignedBlackDart_mem_boundarySegments_iff]
  exact seed.branchSwap_mem_splitStates_iff x


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.selected
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) : Bool :=
  decide (x ∈ seed.splitStates)

@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    seed.selected (doubledAlignedBranchSwap x) = seed.selected x := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.selected
  apply Bool.decide_congr
  exact seed.branchSwap_mem_splitStates_iff x



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionBit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) : Bool :=
  seed.selected x !=
    seed.selected ((doubledAlignedFirstReturnPerm homega heta hdegree).symm x)



def SixVertexDegreeTwoSynchronizedHighChargeSeed.synchronizedAt
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (d : SixVertexOrientedDisagreementDart omega eta) : Prop :=
  seed.transitionBit (d, false) = seed.transitionBit (d, true)



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.selectedDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (d : SixVertexOrientedDisagreementDart omega eta) : Bool :=
  seed.selected (d, false)

@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_eq_selectedDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    seed.selected x = seed.selectedDart x.1 := by
  rcases x with ⟨d, branch⟩
  cases branch
  · rfl
  · exact seed.selected_branchSwap (d, false)



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.synchronizedAt_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (d : SixVertexOrientedDisagreementDart omega eta) :
    seed.synchronizedAt d ↔
      seed.selectedDart
          (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d) =
        seed.selectedDart
          (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.synchronizedAt
    SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionBit
    sixVertexDegreeTwoBranchPredecessor
  simp only [SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_eq_selectedDart]
  have hcurrent : seed.selectedDart d =
      seed.selectedDart d := rfl
  generalize hcur : seed.selectedDart d = current
  generalize hfalse : seed.selectedDart
      ((doubledAlignedFirstReturnPerm homega heta hdegree).symm
        (d, false)).1 = predecessorFalse
  generalize htrue : seed.selectedDart
      ((doubledAlignedFirstReturnPerm homega heta hdegree).symm
        (d, true)).1 = predecessorTrue
  cases current <;> cases predecessorFalse <;> cases predecessorTrue <;>
    simp_all



def SixVertexDegreeTwoSynchronizedHighChargeSeed.GloballySynchronized
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) : Prop :=
  ∀ d, seed.synchronizedAt d



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.unsynchronized_no_vertex_mask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (d : SixVertexOrientedDisagreementDart omega eta)
    (hunsync : ¬ seed.synchronizedAt d) (mask : Bool) :
    (mask != seed.transitionBit (d, false)) = true ∨
      (mask != seed.transitionBit (d, true)) = true := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.synchronizedAt at hunsync
  cases hfalse : seed.transitionBit (d, false) <;>
    cases htrue : seed.transitionBit (d, true) <;>
    cases mask <;> simp_all




theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.globalSynchronization_or_noGo
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.GloballySynchronized ∨
      ∃ d, ∀ mask,
        (mask != seed.transitionBit (d, false)) = true ∨
          (mask != seed.transitionBit (d, true)) = true := by
  classical
  by_cases hsync : seed.GloballySynchronized
  · exact Or.inl hsync
  · right
    rw [SixVertexDegreeTwoSynchronizedHighChargeSeed.GloballySynchronized,
      not_forall] at hsync
    obtain ⟨d, hd⟩ := hsync
    exact ⟨d, seed.unsynchronized_no_vertex_mask d hd⟩



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.selectedDart_eq_of_adj
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (hsync : seed.GloballySynchronized)
    {first second : SixVertexOrientedDisagreementDart omega eta}
    (hadj : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Adj
      first second) :
    seed.selectedDart first = seed.selectedDart second := by
  rcases hadj.2 with ⟨d, endpoints | endpoints⟩
  · rw [endpoints.1, endpoints.2]
    exact (seed.synchronizedAt_iff d).mp (hsync d)
  · rw [endpoints.2, endpoints.1]
    exact ((seed.synchronizedAt_iff d).mp (hsync d)).symm



theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.selectedDart_eq_of_reachable
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (hsync : seed.GloballySynchronized)
    {first second : SixVertexOrientedDisagreementDart omega eta}
    (hreachable :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Reachable
        first second) :
    seed.selectedDart first = seed.selectedDart second := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreachable
  induction hreachable with
  | refl => rfl
  | tail _ hadj ih =>
      exact ih.trans (seed.selectedDart_eq_of_adj hsync hadj)





theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.globalSynchronization_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.GloballySynchronized ↔
      ∀ first second : SixVertexOrientedDisagreementDart omega eta,
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
            first =
          (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
            second →
        seed.selectedDart first = seed.selectedDart second := by
  constructor
  · intro hsync first second hcomponent
    apply seed.selectedDart_eq_of_reachable hsync
    exact SimpleGraph.ConnectedComponent.exact hcomponent
  · intro hconstant d
    rw [seed.synchronizedAt_iff d]
    apply hconstant
    exact SimpleGraph.ConnectedComponent.sound
      (sixVertexDegreeTwoSynchronizedGraph_predecessors_reachable
        homega heta hdegree d)


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (v : T.Vertex) : Bool :=
  if hv : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 then
    let d := orientedDisagreementDartAtActiveVertex homega heta v hv
    let sigma := doubledAlignedFirstReturnPerm homega heta hdegree
    (seed.selected (d, false) != seed.selected (sigma.symm (d, false))) ||
      (seed.selected (d, true) != seed.selected (sigma.symm (d, true)))
  else false


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    seed.transitionVertex (doubledAlignedVertex x) =
      (seed.transitionBit (x.1, false) ||
        seed.transitionBit (x.1, true)) := by
  let v := doubledAlignedVertex x
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d x.1 rfl
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex
  rw [dif_pos hactive]
  change orientedDisagreementDartAtActiveVertex homega heta v hactive = x.1 at hd
  rw [hd]
  rfl



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex_eq_bit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (d : SixVertexOrientedDisagreementDart omega eta)
    (hsync : seed.synchronizedAt d) :
    seed.transitionVertex d.1.1.1 = seed.transitionBit (d, false) := by
  have h := seed.transitionVertex_active (d, false)
  change seed.transitionVertex d.1.1.1 = _ at h
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.synchronizedAt at hsync
  rw [h, hsync, Bool.or_self]


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.internalMismatchVertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (v : T.Vertex) : Bool :=
  if hv : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 then
    let d := orientedDisagreementDartAtActiveVertex homega heta v hv
    seed.selected (d, false) &&
      ((orientedDartAlignedRetie homega heta hdegree d).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree d).pairingQ)
  else false


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.internalMismatchVertex_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    seed.internalMismatchVertex (doubledAlignedVertex x) =
      (seed.selected x &&
        ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
          (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ)) := by
  let v := doubledAlignedVertex x
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d x.1 rfl
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.internalMismatchVertex
  rw [dif_pos hactive]
  change orientedDisagreementDartAtActiveVertex homega heta v hactive = x.1 at hd
  rw [hd]
  rcases x with ⟨dart, branch⟩
  cases branch
  · rfl
  · have hs : seed.selected (dart, false) = seed.selected (dart, true) := by
      simpa [doubledAlignedBranchSwap] using
        (seed.selected_branchSwap (dart, false)).symm
    dsimp only
    rw [hs]


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (_layer : Bool) (v : T.Vertex) : Bool :=
  seed.transitionVertex v || seed.internalMismatchVertex v



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    seed.retieMask layer (doubledAlignedVertex x) =
      ((seed.transitionBit (x.1, false) || seed.transitionBit (x.1, true)) ||
        (seed.selected x &&
          ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
            (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ))) := by
  rw [SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask,
    seed.transitionVertex_active x, seed.internalMismatchVertex_active x]



theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_eq_true_of_transition
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta)
    (htransition : seed.transitionBit x = true) :
    seed.retieMask layer (doubledAlignedVertex x) = true := by
  rw [seed.retieMask_active layer x]
  rcases x with ⟨dart, branch⟩
  cases branch
  · simp [htransition]
  · simp [htransition]



theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_eq_true_of_internal
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta)
    (hselected : seed.selected x = true)
    (hpairing :
      ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) = true) :
    seed.retieMask layer (doubledAlignedVertex x) = true := by
  rw [seed.retieMask_active layer x, hselected, hpairing]
  simp



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) : FKMedialLoopPairing T :=
  fkMedialTogglePairingMask
    (alignedRoutingLoopPairing homega heta hdegree layer)
    (seed.retieMask layer)


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (v : T.Vertex)
    (hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) :
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let transition := seed.transitionVertex v
    let internal := seed.internalMismatchVertex v
    seed.targetPairing layer v =
      if transition || internal then
        !(if layer then
          (orientedDartAlignedRetie homega heta hdegree d).pairingQ
        else (orientedDartAlignedRetie homega heta hdegree d).pairingP)
      else if layer then
        (orientedDartAlignedRetie homega heta hdegree d).pairingQ
      else (orientedDartAlignedRetie homega heta hdegree d).pairingP := by
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hsource := alignedRoutingPairing_eq_at_active
    homega heta hdegree layer v hactive
  change alignedRoutingLoopPairing homega heta hdegree layer v =
    (if layer then (orientedDartAlignedRetie homega heta hdegree d).pairingQ
      else (orientedDartAlignedRetie homega heta hdegree d).pairingP) at hsource
  rw [SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing,
    fkMedialTogglePairingMask, hsource]
  rfl



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.inputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  if seed.retieMask layer (doubledAlignedVertex x) &&
      (fkMedialVertexParity (doubledAlignedVertex x) == false) then
    doubledAlignedBranchSwap x else x


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.sourceReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (_seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  if layer then sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta
    hdegree x else doubledAlignedFirstReturnPerm homega heta hdegree x



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.sourceReturnState_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer
        (seed.sourceReturnState layer x) =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer x := by
  cases layer
  · simpa [SixVertexDegreeTwoSynchronizedHighChargeSeed.sourceReturnState,
      sixVertexDegreeTwoAlignedActiveColor] using
      (sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_false
        homega heta hdegree x).symm
  · let y := doubledAlignedFirstReturnPerm homega heta hdegree x
    let retie := orientedDartAlignedRetie homega heta hdegree y.1
    have h := sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_true
      homega heta hdegree x
    change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true x =
      if retie.pairingP = retie.pairingQ then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true y
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (doubledAlignedBranchSwap y) at h
    rw [SixVertexDegreeTwoSynchronizedHighChargeSeed.sourceReturnState,
      if_pos rfl, sixVertexDegreeTwoAlignedTrueFirstReturnState]
    change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
      (if retie.pairingP = retie.pairingQ then y
        else doubledAlignedBranchSwap y) = _
    by_cases heq : retie.pairingP = retie.pairingQ
    · rw [if_pos heq] at h ⊢
      exact h.symm
    · rw [if_neg heq] at h ⊢
      exact h.symm



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.outputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  if seed.retieMask layer (doubledAlignedVertex x) &&
      (fkMedialVertexParity (doubledAlignedVertex x) == true) then
    doubledAlignedBranchSwap x else x


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.activeReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  seed.outputState layer
    (seed.sourceReturnState layer (seed.inputState layer x))



@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_inputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    seed.selected (seed.inputState layer x) = seed.selected x := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.inputState
  split
  · exact seed.selected_branchSwap x
  · rfl


@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_outputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    seed.selected (seed.outputState layer x) = seed.selected x := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.outputState
  split
  · exact seed.selected_branchSwap x
  · rfl


@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_tauAdjusted
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    seed.selected
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      seed.selected x := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  by_cases heq : retie.pairingP = retie.pairingQ
  · simp [sixVertexDegreeTwoTauAdjustedState, retie, heq]
  · simpa [sixVertexDegreeTwoTauAdjustedState, retie, heq] using
      seed.selected_branchSwap x



@[simp] theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_sourceReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    seed.selected (seed.sourceReturnState layer x) =
      seed.selected (doubledAlignedFirstReturnPerm homega heta hdegree x) := by
  cases layer
  · rfl
  · exact seed.selected_tauAdjusted
      (doubledAlignedFirstReturnPerm homega heta hdegree x)




@[simp] theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_activeReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    seed.selected (seed.activeReturnState layer x) =
      seed.selected (doubledAlignedFirstReturnPerm homega heta hdegree
        (seed.inputState layer x)) := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.activeReturnState
  rw [seed.selected_outputState, seed.selected_sourceReturnState]



theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_activeReturnState_bne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    (seed.selected (seed.activeReturnState layer x) != seed.selected x) =
      seed.transitionBit
        (doubledAlignedFirstReturnPerm homega heta hdegree
          (seed.inputState layer x)) := by
  rw [seed.selected_activeReturnState]
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionBit
  rw [Equiv.symm_apply_apply, seed.selected_inputState]



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.firstReturn_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart) :
    let mask := seed.retieMask layer
    let swapped := fkMedialBlackDartMaskSwap mask dart
    (finiteFirstReturn
        (fkMedialBlackBoundaryPerm (seed.targetPairing layer))
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨dart, hactive⟩).1 =
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, (activeBlackDart_maskSwap_iff mask dart).mpr hactive⟩).1 := by
  classical
  let mask := seed.retieMask layer
  have hreturn := finiteFirstReturn_togglePairingMask_active
      (alignedRoutingLoopPairing homega heta hdegree layer) mask
      (fun d hd => by
        have hzero := (hdegree d.1.1).resolve_right hd
        have hnot : ¬ (sixVertexLocalDisagreementSides
            (sixVertexLocalIncomingPattern omega d.1.1)
            (sixVertexLocalIncomingPattern eta d.1.1)).card = 2 := by omega
        simp [mask, SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask,
          SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex,
          SixVertexDegreeTwoSynchronizedHighChargeSeed.internalMismatchVertex,
          hnot]) dart hactive
  simpa [SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing, mask]
    using hreturn



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.firstReturn_slot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta)
    (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv (seed.targetPairing layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    fkColoredBlackDartStrandSlotEquiv (seed.targetPairing layer)
        ((finiteFirstReturn
          (fkMedialBlackBoundaryPerm (seed.targetPairing layer))
          (activeBlackDart (omega := omega) (eta := eta))
          ⟨dart, hactive⟩).1) =
      (doubledAlignedVertex (seed.activeReturnState layer x),
        doubledAlignedSlot homega heta hdegree layer
          (seed.activeReturnState layer x)) := by
  classical
  let sourcePairing := alignedRoutingLoopPairing homega heta hdegree layer
  let mask := seed.retieMask layer
  let targetPairing := seed.targetPairing layer
  let input := seed.inputState layer x
  let returned := seed.sourceReturnState layer input
  let swapped := fkMedialBlackDartMaskSwap mask dart
  have hpairing : targetPairing =
      fkMedialTogglePairingMask sourcePairing mask := rfl
  have hdart : dart =
      (fkColoredBlackDartStrandSlotEquiv targetPairing).symm
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) := by
    apply (fkColoredBlackDartStrandSlotEquiv targetPairing).injective
    simpa [targetPairing] using hslot
  have hswapped : swapped =
      doubledAlignedBlackDart homega heta hdegree layer input := by
    dsimp only [swapped]
    rw [hdart, hpairing]
    exact fkMedialBlackDartMaskSwap_canonicalTargetState homega heta hdegree
      mask layer x
  have hswappedActive :
      activeBlackDart (omega := omega) (eta := eta) swapped :=
    (activeBlackDart_maskSwap_iff mask dart).mpr hactive
  have hstart :
      (⟨swapped, hswappedActive⟩ : {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d}) =
      doubledAlignedBlackDartEquiv homega heta hdegree layer input := by
    apply Subtype.ext
    exact hswapped
  have hsourceReturn :
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, hswappedActive⟩).1 =
      doubledAlignedBlackDart homega heta hdegree layer returned := by
    rw [hstart]
    cases layer
    · exact congrArg Subtype.val
        (doubledAlignedFirstReturnPerm_false_arrival homega heta hdegree input).symm
    · exact congrArg Subtype.val
        (sixVertexDegreeTwoAlignedTrueFirstReturn_arrival homega heta hdegree
          input)
  have htargetReturn := seed.firstReturn_active layer dart hactive
  change (finiteFirstReturn
      (fkMedialBlackBoundaryPerm targetPairing)
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨dart, hactive⟩).1 =
    (finiteFirstReturn
      (alignedBoundaryPerm homega heta hdegree layer)
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨swapped, hswappedActive⟩).1 at htargetReturn
  change fkColoredBlackDartStrandSlotEquiv targetPairing
      ((finiteFirstReturn
        (fkMedialBlackBoundaryPerm targetPairing)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨dart, hactive⟩).1) = _
  rw [htargetReturn, hsourceReturn, hpairing,
    fkColoredBlackDartStrandSlotEquiv_togglePairingMask]
  simp only [Equiv.trans_apply]
  have hcoordinate :
      fkColoredBlackDartStrandSlotEquiv sourcePairing
          (doubledAlignedBlackDart homega heta hdegree layer returned) =
        (doubledAlignedVertex returned,
          doubledAlignedSlot homega heta hdegree layer returned) :=
    fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _
  rw [hcoordinate,
    fkColoredParityMaskStrandSlotSwap_doubledAlignedState]
  rfl



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.targetBoundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) :
    fkColoredStrandSlotBoundaryPerm (seed.targetPairing layer) =
      (fkColoredParityMaskStrandSlotSwap (seed.retieMask layer) false).trans
        ((fkColoredStrandSlotBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree layer)).trans
          (fkColoredParityMaskStrandSlotSwap
            (seed.retieMask layer) true)) := by
  exact fkColoredStrandSlotBoundaryPerm_togglePairingMask _ _


@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing_recover
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) :
    fkMedialTogglePairingMask (seed.targetPairing layer)
        (seed.retieMask layer) =
      alignedRoutingLoopPairing homega heta hdegree layer := by
  exact fkMedialTogglePairingMask_self _ _


@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (v : T.Vertex)
    (hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0) :
    seed.retieMask layer v = false := by
  have hnot : ¬ (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 := by omega
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask,
    SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex,
    SixVertexDegreeTwoSynchronizedHighChargeSeed.internalMismatchVertex,
    hnot]



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (v : T.Vertex)
    (hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0) :
    seed.targetPairing layer v =
      alignedRoutingLoopPairing homega heta hdegree layer v := by
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing,
    fkMedialTogglePairingMask, seed.retieMask_inactive layer v hzero]



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedActiveColor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) : Bool :=
  fkColoredLayeredSlotColor
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    (seed.occurrenceEquiv
      (layer, doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x))




theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
            heta hdegree layer dart)) =
      if _hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
          false seed.splitStates then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
            heta hdegree (!layer) dart)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
            heta hdegree layer dart) := by
  classical
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
      false seed.splitStates
  · rw [dif_pos hdart]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply seed
        layer dart hdart)
  · rw [dif_neg hdart]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply_of_not_mem
        seed layer dart hdart)



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x)) =
      if _hx : x ∈ seed.splitStates then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree (!layer) x)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x) := by
  rw [← sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active
      homega heta hdegree layer x,
    seed.transportedColor_dart]
  have hmem := doubledAlignedBlackDart_mem_boundarySegments_iff
    homega heta hdegree false seed.splitStates x
  by_cases hx : x ∈ seed.splitStates
  · rw [dif_pos (hmem.mpr hx), dif_pos hx]
    simp
  · rw [dif_neg (fun hdart => hx (hmem.mp hdart)), dif_neg hx]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedActiveColor_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    seed.transportedActiveColor layer x =
      if _hx : x ∈ seed.splitStates then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree (!layer) x
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer x := by
  exact seed.transportedColor_active layer x



def SixVertexDegreeTwoSynchronizedHighChargeSeed.ActiveReturnColorInvariant
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) : Prop :=
  ∀ (layer : Bool) (x : DoubledAlignedState omega eta),
    seed.transportedActiveColor layer (seed.activeReturnState layer x) =
      seed.transportedActiveColor layer x



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_firstReturn
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (hreturn : seed.ActiveReturnColorInvariant)
    (layer : Bool) (x : DoubledAlignedState omega eta)
    (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv (seed.targetPairing layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    let arrival := (finiteFirstReturn
      (fkMedialBlackBoundaryPerm (seed.targetPairing layer))
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨dart, hactive⟩).1
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, fkColoredBlackDartStrandSlotEquiv
            (seed.targetPairing layer) arrival)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, fkColoredBlackDartStrandSlotEquiv
            (seed.targetPairing layer) dart)) := by
  dsimp only
  rw [seed.firstReturn_slot layer x dart hactive hslot, hslot]
  exact hreturn layer x



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_dart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : ¬ activeBlackDart (omega := omega) (eta := eta) dart) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
            heta hdegree layer dart)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) := by
  classical
  rw [seed.transportedColor_dart layer dart]
  split
  · have hcross :=
      sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq
        homega heta hdegree dart hinactive
    cases layer
    · exact hcross.symm
    · exact hcross
  · rfl




theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_falseBoundary_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : ¬ activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart)) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
            heta hdegree layer
            (alignedBoundaryPerm homega heta hdegree false dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
            heta hdegree layer dart)) := by
  classical
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hmem : next ∈ doubledAlignedBoundarySegments homega heta hdegree false
        seed.splitStates ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        seed.splitStates :=
    mem_doubledAlignedBoundarySegments_step_iff_of_inactive_arrival
      homega heta hdegree false seed.splitStates dart hinactive
  rw [seed.transportedColor_dart layer next,
    seed.transportedColor_dart layer dart]
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
      false seed.splitStates
  · have hnext : next ∈ doubledAlignedBoundarySegments homega heta hdegree
        false seed.splitStates := hmem.mpr hdart
    rw [dif_pos hnext, dif_pos hdart]
    exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
      homega heta hdegree (!layer) dart hinactive
  · have hnext : next ∉ doubledAlignedBoundarySegments homega heta hdegree
        false seed.splitStates := fun h => hdart (hmem.mp h)
    rw [dif_neg hnext, dif_neg hdart]
    exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
      homega heta hdegree layer dart hinactive


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.boundaryFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T) :
    FKMedialBlackDart T :=
  let input := sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree
    (seed.retieMask layer) false layer dart
  let arrival := alignedBoundaryPerm homega heta hdegree false input
  let common := if layer then
      (alignedBlackDartLayerSwap homega heta hdegree).symm arrival
    else arrival
  sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree
    (seed.retieMask layer) true layer common



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.boundaryFalseDart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : ¬ activeBlackDart (omega := omega) (eta := eta) dart)
    (hnext : ¬ activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart)) :
    seed.boundaryFalseDart layer dart =
      alignedBoundaryPerm homega heta hdegree false dart := by
  let mask := seed.retieMask layer
  have hzeroD := (hdegree dart.1.1).resolve_right hdart
  have hmaskD : mask dart.1.1 = false :=
    seed.retieMask_inactive layer dart.1.1 hzeroD
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hzeroNext := (hdegree next.1.1).resolve_right hnext
  have hmaskNext : mask next.1.1 = false :=
    seed.retieMask_inactive layer next.1.1 hzeroNext
  have hswapNext : alignedBlackDartLayerSwap homega heta hdegree next = next :=
    alignedBlackDartLayerSwap_inactive homega heta hdegree next hnext
  have hswapNextSymm :
      (alignedBlackDartLayerSwap homega heta hdegree).symm next = next := by
    apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    simpa [hswapNext]
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.boundaryFalseDart,
    sixVertexDegreeTwoAlignedFalseDartSlotSwap, mask, next, hmaskD,
    hmaskNext, hswapNextSymm]



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.targetBoundary_slotOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredStrandSlotBoundaryPerm (seed.targetPairing layer)
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
          layer dart) =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer (seed.boundaryFalseDart layer dart) := by
  rw [seed.targetBoundary layer]
  simp only [Equiv.trans_apply]
  rw [fkColoredParityMaskStrandSlotSwap_slotOfFalseDart,
    sixVertexDegreeTwoAlignedSourceBoundary_slotOfFalseDart,
    fkColoredParityMaskStrandSlotSwap_slotOfFalseDart]
  rfl



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.slotColorInvariant_of_falseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hfalseDart : ∀ (layer : Bool) (dart : FKMedialBlackDart T),
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (seed.occurrenceEquiv
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer (seed.boundaryFalseDart layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (seed.occurrenceEquiv
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      seed.targetPairing
      (Fintype.card
        (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed) := by
  intro slot
  rcases slot with ⟨layer, slot⟩
  let dart := sixVertexDegreeTwoAlignedFalseDartOfSlot homega heta hdegree
    layer slot
  have hslot := sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_inverse
    homega heta hdegree layer slot
  change sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
      layer dart = slot at hslot
  change fkColoredLayeredSlotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (seed.occurrenceEquiv
        (fkColoredLayeredStrandSlotBoundaryPerm seed.targetPairing
          (layer, slot))) = _
  rw [← hslot, fkColoredLayeredStrandSlotBoundaryPerm_apply,
    seed.targetBoundary_slotOfFalseDart layer dart]
  exact hfalseDart layer dart


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.colorTargetOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hfalseDart : ∀ (layer : Bool) (dart : FKMedialBlackDart T),
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (seed.occurrenceEquiv
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer (seed.boundaryFalseDart layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (seed.occurrenceEquiv
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    SixVertexDegreeTwoSynchronizedSplitColorTarget seed :=
  ⟨seed.targetPairing, seed.slotColorInvariant_of_falseDart hfalseDart⟩



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.slotColorInvariant_of_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hactive : ∀ (layer : Bool) (dart : FKMedialBlackDart T),
      activeBlackDart (omega := omega) (eta := eta) dart ∨
        activeBlackDart (omega := omega) (eta := eta)
          (alignedBoundaryPerm homega heta hdegree false dart) ->
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (seed.occurrenceEquiv
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer (seed.boundaryFalseDart layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (seed.occurrenceEquiv
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      seed.targetPairing
      (Fintype.card
        (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed) := by
  apply seed.slotColorInvariant_of_falseDart
  intro layer dart
  by_cases hdart : activeBlackDart (omega := omega) (eta := eta) dart
  · exact hactive layer dart (Or.inl hdart)
  · by_cases hnext : activeBlackDart (omega := omega) (eta := eta)
        (alignedBoundaryPerm homega heta hdegree false dart)
    · exact hactive layer dart (Or.inr hnext)
    · rw [seed.boundaryFalseDart_of_inactive layer dart hdart hnext]
      exact seed.transportedColor_falseBoundary_of_inactive layer dart hnext



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.colorTargetOfActive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hactive : ∀ (layer : Bool) (dart : FKMedialBlackDart T),
      activeBlackDart (omega := omega) (eta := eta) dart ∨
        activeBlackDart (omega := omega) (eta := eta)
          (alignedBoundaryPerm homega heta hdegree false dart) ->
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (seed.occurrenceEquiv
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer (seed.boundaryFalseDart layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (seed.occurrenceEquiv
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    SixVertexDegreeTwoSynchronizedSplitColorTarget seed :=
  ⟨seed.targetPairing, seed.slotColorInvariant_of_active hactive⟩


theorem sum_sixVertexDegreeTwoSynchronizedComponentCharge_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    (∑ component :
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component) = 2 := by
  classical
  unfold sixVertexDegreeTwoSynchronizedComponentCharge
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_ite_eq]
  have htotal := sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two homega heta
    hdegree middle homegaSector hetaSector hmiddle
  rw [← htotal]
  apply Finset.sum_congr
  · ext d
    simp
  · intro d hd
    rfl

theorem sixVertexDegreeTwoSynchronizedTotalComponentCharge_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    sixVertexDegreeTwoSynchronizedTotalComponentCharge homega heta hdegree =
      2 := by
  unfold sixVertexDegreeTwoSynchronizedTotalComponentCharge
  exact sum_sixVertexDegreeTwoSynchronizedComponentCharge_eq_two homega heta
    hdegree middle homegaSector hetaSector hmiddle



theorem sixVertexDegreeTwoSynchronizedComponent_predecessors_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
          (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d) =
        component ↔
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
          (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) =
        component := by
  have hreach := sixVertexDegreeTwoSynchronizedGraph_predecessors_reachable
    homega heta hdegree d
  have heq : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
        (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d) =
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
        (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) :=
    ConnectedComponent.sound hreach
  rw [heq]




theorem sixVertexDegreeTwoSynchronizedComponent_unit_or_fractional
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (∃ component :
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component = 1) \/
      (∀ component :
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component ≠ 1) := by
  classical
  by_cases h : ∃ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
    sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
      component = 1
  · exact Or.inl h
  · exact Or.inr (by
      intro component hone
      exact h ⟨component, hone⟩)



theorem sixVertexDegreeTwoSynchronizedComponent_halfFlow_charge_one
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    (∑ component :
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      (sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component : ℚ) * (1 / 2)) = 1 := by
  rw [← Finset.sum_mul]
  rw [← Int.cast_sum]
  rw [sum_sixVertexDegreeTwoSynchronizedComponentCharge_eq_two homega heta
    hdegree middle homegaSector hetaSector hmiddle]
  norm_num



theorem exists_sixVertexDegreeTwoSynchronizedComponentCharge_eq_one_of_le_one
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hle : ∀ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component ≤ 1) :
    ∃ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component = 1 := by
  classical
  by_contra hnone
  have hnonpos : ∀ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component ≤ 0 := by
    intro component
    have hne : sixVertexDegreeTwoSynchronizedComponentCharge homega heta
        hdegree component ≠ 1 := by
      intro hone
      exact hnone ⟨component, hone⟩
    have hbound := hle component
    omega
  have hsumNonpos : sixVertexDegreeTwoSynchronizedTotalComponentCharge homega
      heta hdegree ≤ 0 := by
    unfold sixVertexDegreeTwoSynchronizedTotalComponentCharge
    exact Finset.sum_nonpos (fun component _ => hnonpos component)
  rw [sixVertexDegreeTwoSynchronizedTotalComponentCharge_eq_two homega heta
    hdegree middle homegaSector hetaSector hmiddle] at hsumNonpos
  omega




theorem exists_sixVertexDegreeTwoSynchronizedComponentCharge_ge_two_of_no_unit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hnoUnit : ∀ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component ≠ 1) :
    ∃ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component := by
  classical
  by_contra hnone
  have hleOne : ∀ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component ≤ 1 := by
    intro component
    have hnot : ¬ 2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge homega
        heta hdegree component := by
      intro htwo
      exact hnone ⟨component, htwo⟩
    omega
  obtain ⟨component, hone⟩ :=
    exists_sixVertexDegreeTwoSynchronizedComponentCharge_eq_one_of_le_one
      homega heta hdegree middle homegaSector hetaSector hmiddle hleOne
  exact hnoUnit component hone





inductive SixVertexDegreeTwoSynchronizedReconnectionSeed
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) : Type
  | unit
      (component :
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
      (charge : sixVertexDegreeTwoSynchronizedComponentCharge homega heta
        hdegree component = 1)
  | split
      (component :
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
      (charge : 2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge homega heta
        hdegree component)
      (endpoints : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta
        hdegree component)



theorem sixVertexDegreeTwoSynchronizedReconnectionSeed_nonempty
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    Nonempty
      (SixVertexDegreeTwoSynchronizedReconnectionSeed homega heta hdegree) := by
  classical
  rcases sixVertexDegreeTwoSynchronizedComponent_unit_or_fractional
      homega heta hdegree with hunit | hnoUnit
  · obtain ⟨component, hcharge⟩ := hunit
    exact ⟨.unit component hcharge⟩
  · obtain ⟨component, hcharge⟩ :=
      exists_sixVertexDegreeTwoSynchronizedComponentCharge_ge_two_of_no_unit
        homega heta hdegree middle homegaSector hetaSector hmiddle hnoUnit
    exact ⟨.split component
      hcharge (sixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
        component hcharge)⟩



noncomputable def sixVertexDegreeTwoSynchronizedReconnectionSeed
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    SixVertexDegreeTwoSynchronizedReconnectionSeed homega heta hdegree :=
  Classical.choice
    (sixVertexDegreeTwoSynchronizedReconnectionSeed_nonempty homega heta
      hdegree middle homegaSector hetaSector hmiddle)

end

end StatMech.FrontierD
