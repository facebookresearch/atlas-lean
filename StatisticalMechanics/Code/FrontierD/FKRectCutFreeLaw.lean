/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCutSquareEmbedding
import Code.FK.EdgeConfigEventLaw
import Code.FK.Tilt










open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

open StatMech



abbrev FKRectCutClosedConfig (R : FKRectTorus) :=
  {omega : R.Configuration // FKRectCutClosedConfiguration R omega}

noncomputable instance instFintypeFKRectCutClosedConfig (R : FKRectTorus) :
    Fintype (FKRectCutClosedConfig R) := by
  unfold FKRectCutClosedConfig
  infer_instance



theorem mem_fkRectCutGraph_edgeSet_iff (R : FKRectTorus)
    (e : Sym2 R.Vertex) :
    e ∈ (fkRectCutGraph R).edgeSet ↔
      ∃ a : R.EdgeIndex,
        a ∉ fkRectTorusCutEdges R ∧ fkRectTorusIndexedEdge R a = e := by
  obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep e
  rw [SimpleGraph.mem_edgeSet, fkRectCutGraph_adj_iff]
  constructor
  · rintro ⟨htorus, hcut⟩
    obtain ⟨a, ha⟩ := htorus
    refine ⟨a, ?_, ha⟩
    intro hacut
    apply hcut
    rw [← ha, mem_fkRectTorusCutGraphEdges]
    exact hacut
  · rintro ⟨a, hacut, ha⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    intro hcut
    have hcut' : fkRectTorusIndexedEdge R a ∈
        fkRectTorusCutGraphEdges R := by
      simpa only [ha] using hcut
    exact hacut ((mem_fkRectTorusCutGraphEdges R a).1 hcut')



def fkRectCutClosedToEdgeConfig (R : FKRectTorus)
    (omega : FKRectCutClosedConfig R) :
    FK.ecz_ClosedOff (fkRectCutGraph R) :=
  ⟨fkRectFullGraphConfiguration R omega.1, by
    intro e he
    have hnotCutEdge : e ∉ (fkRectCutGraph R).edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using he
    by_cases htorus : e ∈ (fkRectTorusGraph R).edgeSet
    · obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 htorus
      have hacut : a ∈ fkRectTorusCutEdges R := by
        by_contra hnot
        apply hnotCutEdge
        exact (mem_fkRectCutGraph_edgeSet_iff R e).2 ⟨a, hnot, ha⟩
      rw [← ha, fkRectFullGraphConfiguration_indexedEdge]
      exact (fkRectCutClosedConfiguration_iff R omega.1).1 omega.2 a hacut
    · exact fkRectFullGraphConfiguration_eq_false_of_not_edge
        R omega.1 htorus⟩



def fkRectEdgeConfigToCutClosed (R : FKRectTorus)
    (sigma : FK.ecz_ClosedOff (fkRectCutGraph R)) :
    FKRectCutClosedConfig R :=
  ⟨fun a => sigma.1 (fkRectTorusIndexedEdge R a),
    (fkRectCutClosedConfiguration_iff R _).2 (by
      intro a hacut
      apply sigma.2
      intro hedge
      have hedgeSet : fkRectTorusIndexedEdge R a ∈
          (fkRectCutGraph R).edgeSet := by
        simpa only [SimpleGraph.mem_edgeFinset] using hedge
      obtain ⟨b, hb, hba⟩ :=
        (mem_fkRectCutGraph_edgeSet_iff R _).1 hedgeSet
      exact hb ((fkRectTorusIndexedEdge_injective R hba).symm ▸ hacut))⟩



def fkRectCutClosedEdgeConfigEquiv (R : FKRectTorus) :
    FKRectCutClosedConfig R ≃ FK.ecz_ClosedOff (fkRectCutGraph R) where
  toFun := fkRectCutClosedToEdgeConfig R
  invFun := fkRectEdgeConfigToCutClosed R
  left_inv omega := by
    apply Subtype.ext
    funext a
    exact fkRectFullGraphConfiguration_indexedEdge R omega.1 a
  right_inv sigma := by
    apply Subtype.ext
    funext e
    change fkRectFullGraphConfiguration R
        (fkRectEdgeConfigToCutClosed R sigma).1 e = sigma.1 e
    by_cases htorus : e ∈ (fkRectTorusGraph R).edgeSet
    · obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 htorus
      rw [← ha, fkRectFullGraphConfiguration_indexedEdge]
      rfl
    · rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ htorus]
      symm
      apply sigma.2 e
      intro hedge
      have hedgeSet : e ∈ (fkRectCutGraph R).edgeSet := by
        simpa only [SimpleGraph.mem_edgeFinset] using hedge
      obtain ⟨a, _, ha⟩ := (mem_fkRectCutGraph_edgeSet_iff R e).1 hedgeSet
      exact htorus ((mem_fkRectTorusGraph_edgeSet_iff R e).2 ⟨a, ha⟩)

@[simp] theorem fkRectCutClosedEdgeConfigEquiv_apply
    (R : FKRectTorus) (omega : FKRectCutClosedConfig R) :
    (fkRectCutClosedEdgeConfigEquiv R omega).1 =
      fkRectFullGraphConfiguration R omega.1 := rfl



theorem fkRectCut_openSub_eq (R : FKRectTorus)
    (omega : FKRectCutClosedConfig R) :
    FK.openSub (fkRectCutGraph R)
        (fkRectCutClosedEdgeConfigEquiv R omega).1 =
      fkRectOpenGraph R omega.1 := by
  rw [← fkOpenSub_fullGraphConfiguration R omega.1]
  apply SimpleGraph.ext
  ext x y
  simp only [FK.openSub_adj]
  constructor
  · rintro ⟨hcut, hopen⟩
    exact ⟨(fkRectCutGraph_adj_iff R x y).1 hcut |>.1, hopen⟩
  · rintro ⟨htorus, hopen⟩
    refine ⟨(fkRectCutGraph_adj_iff R x y).2 ⟨htorus, ?_⟩, hopen⟩
    intro hcut
    have hfalse :=
      fkRectFullGraphConfiguration_forceCut_eq_false_of_cutEdge
        R omega.1 hcut
    have hforce : fkRectForceCutClosed R omega.1 = omega.1 := omega.2
    rw [hforce] at hfalse
    rw [hfalse] at hopen
    exact Bool.noConfusion hopen



theorem fkRectCut_numClusters_eq (R : FKRectTorus)
    (omega : FKRectCutClosedConfig R) :
    FK.numClusters (fkRectCutGraph R)
        (fkRectCutClosedEdgeConfigEquiv R omega).1 =
      fkRectNumClusters R omega.1 := by
  unfold FK.numClusters fkRectNumClusters
  exact Fintype.card_congr (by rw [fkRectCut_openSub_eq R omega])



theorem fkOpenCount_eq_openSub_edgeFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (omega : ConfigSpace (Sym2 V)) :
    FK.openCount G omega = (FK.openSub G omega).edgeFinset.card := by
  unfold FK.openCount
  congr 1
  ext e
  rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeFinset]
  obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep e
  change G.Adj x y ∧ omega s(x, y) = true ↔
    (FK.openSub G omega).Adj x y
  rfl



theorem fkRectOpenGraph_edgeFinset_card (R : FKRectTorus)
    (omega : R.Configuration) :
    (fkRectOpenGraph R omega).edgeFinset.card =
      fkRectOpenEdgeCount R omega := by
  classical
  unfold fkRectOpenEdgeCount
  symm
  apply Finset.card_bij (fun a _ => fkRectTorusIndexedEdge R a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [SimpleGraph.mem_edgeFinset]
    obtain ⟨p, q⟩ := fkRectLiftedIndexedEdgeEnds R a
    have hproject := fkRectLiftedIndexedEdgeEnds_project R a
    rw [hproject, SimpleGraph.mem_edgeSet]
    exact ⟨a, ha, hproject⟩
  · intro a ha b hb hab
    exact fkRectTorusIndexedEdge_injective R hab
  · intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep e
    obtain ⟨a, ha, hedge⟩ := he
    refine ⟨a, ?_, hedge⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha



theorem fkRectCut_openCount_eq (R : FKRectTorus)
    (omega : FKRectCutClosedConfig R) :
    FK.openCount (fkRectCutGraph R)
        (fkRectCutClosedEdgeConfigEquiv R omega).1 =
      fkRectOpenEdgeCount R omega.1 := by
  rw [fkOpenCount_eq_openSub_edgeFinset_card]
  have hfin :
      (FK.openSub (fkRectCutGraph R)
          (fkRectCutClosedEdgeConfigEquiv R omega).1).edgeFinset =
        (fkRectOpenGraph R omega.1).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [fkRectCut_openSub_eq R omega]
  rw [hfin, fkRectOpenGraph_edgeFinset_card]




theorem fkRectCut_edgeProduct_critical_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : FKRectCutClosedConfig R) :
    FK.edgeProduct (fkRectCutGraph R) (fkRectCriticalP q)
        (fkRectCutClosedEdgeConfigEquiv R omega).1 =
      (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card *
        Real.sqrt q ^ fkRectOpenEdgeCount R omega.1 := by
  let sigma := (fkRectCutClosedEdgeConfigEquiv R omega).1
  let o := FK.openCount (fkRectCutGraph R) sigma
  let c := FK.closedCount (fkRectCutGraph R) sigma
  have hoc : o + c = (fkRectCutGraph R).edgeFinset.card :=
    FK.openCount_add_closedCount (fkRectCutGraph R) sigma
  have ho : o = fkRectOpenEdgeCount R omega.1 := by
    dsimp only [o, sigma]
    exact fkRectCut_openCount_eq R omega
  have hp := fkRectCriticalP_eq_sqrt_mul_one_sub hq
  rw [FK.edgeProduct_eq_pow]
  change fkRectCriticalP q ^ o * (1 - fkRectCriticalP q) ^ c = _
  calc
    fkRectCriticalP q ^ o * (1 - fkRectCriticalP q) ^ c =
        (Real.sqrt q * (1 - fkRectCriticalP q)) ^ o *
          (1 - fkRectCriticalP q) ^ c := by
            nth_rewrite 1 [hp]
            rfl
    _ = Real.sqrt q ^ o * (1 - fkRectCriticalP q) ^ o *
          (1 - fkRectCriticalP q) ^ c := by
          rw [mul_pow]
    _ =
        (1 - fkRectCriticalP q) ^ (o + c) * Real.sqrt q ^ o := by
          rw [pow_add]
          ring
    _ = (1 - fkRectCriticalP q) ^
          (fkRectCutGraph R).edgeFinset.card * Real.sqrt q ^ o := by
          rw [hoc]
    _ = _ := by
      rw [ho]



theorem fkRectCut_fkWeight_critical_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : FKRectCutClosedConfig R) :
    FK.fkWeight (fkRectCutGraph R) (fkRectCriticalP q) q
        (fkRectCutClosedEdgeConfigEquiv R omega).1 =
      (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card *
        fkRectCriticalReducedWeight R q omega.1 := by
  unfold FK.fkWeight fkRectCriticalReducedWeight
  rw [fkRectCut_edgeProduct_critical_eq R hq omega,
    fkRectCut_numClusters_eq R omega]
  ring


def fkRectCutClosedReducedEventWeight
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) : Real :=
  ∑ omega : FKRectCutClosedConfig R,
    A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) omega.1


def fkRectCutClosedReducedZ (R : FKRectTorus) (q : Real) : Real :=
  ∑ omega : FKRectCutClosedConfig R,
    fkRectCriticalReducedWeight R q omega.1

theorem fkRectCutClosedReducedEventWeight_univ
    (R : FKRectTorus) (q : Real) :
    fkRectCutClosedReducedEventWeight R q Set.univ =
      fkRectCutClosedReducedZ R q := by
  unfold fkRectCutClosedReducedEventWeight fkRectCutClosedReducedZ
  apply Finset.sum_congr rfl
  intro omega _
  rw [Set.indicator_of_mem (Set.mem_univ omega.1)]

theorem fkRectCutClosedReducedZ_pos
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    0 < fkRectCutClosedReducedZ R q := by
  unfold fkRectCutClosedReducedZ
  apply Finset.sum_pos
  · intro omega _
    exact fkRectCriticalReducedWeight_pos R hq omega.1
  · let omega : FKRectCutClosedConfig R :=
      ⟨fun _ => false, (fkRectCutClosedConfiguration_iff R _).2
        (fun _ _ => rfl)⟩
    exact ⟨omega, Finset.mem_univ omega⟩



theorem fkRect_cutClosed_indicatorReduced_sum
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) :
    (∑ eta : R.Configuration,
      {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A}.indicator
        (fun eta => fkRectCriticalReducedWeight R q eta) eta) =
      fkRectCutClosedReducedEventWeight R q A := by
  classical
  calc
    (∑ eta : R.Configuration,
      {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A}.indicator
        (fun eta => fkRectCriticalReducedWeight R q eta) eta) =
      ∑ eta : R.Configuration,
        if FKRectCutClosedConfiguration R eta then
          A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) eta
        else 0 := by
      apply Finset.sum_congr rfl
      intro eta _
      by_cases hc : FKRectCutClosedConfiguration R eta
      · by_cases hA : eta ∈ A <;> simp [hc, hA]
      · simp [hc]
    _ = ∑ eta ∈ (Finset.univ.filter
          (FKRectCutClosedConfiguration R)),
        A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) eta := by
      rw [Finset.sum_filter]
    _ = ∑ eta : FKRectCutClosedConfig R,
        A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) eta.1 := by
      exact Finset.sum_subtype _ (by simp) _
    _ = fkRectCutClosedReducedEventWeight R q A := rfl



theorem fkRectCriticalEventMass_cutClosed_inter_eq
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} =
      fkRectCutClosedReducedEventWeight R q A /
        fkRectCriticalReducedZ R q := by
  unfold fkRectCriticalEventMass fkRectCriticalRandomClusterProb
  calc
    (∑ eta : R.Configuration,
      {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A}.indicator
        (fun eta => fkRectCriticalReducedWeight R q eta /
          fkRectCriticalReducedZ R q) eta) =
      (∑ eta : R.Configuration,
        {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A}.indicator
          (fun eta => fkRectCriticalReducedWeight R q eta) eta) /
        fkRectCriticalReducedZ R q := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro eta _
      by_cases hmem : FKRectCutClosedConfiguration R eta ∧ eta ∈ A
      · have hset : eta ∈
            {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} := hmem
        rw [Set.indicator_of_mem hset, Set.indicator_of_mem hset]
      · have hset : eta ∉
            {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} := hmem
        rw [Set.indicator_of_notMem hset, Set.indicator_of_notMem hset,
          zero_div]
    _ = _ := by rw [fkRect_cutClosed_indicatorReduced_sum]



theorem fkRectCriticalCutFreeEventMass_eq_reduced
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) :
    fkRectCriticalCutFreeEventMass R q A =
      fkRectCutClosedReducedEventWeight R q A /
        fkRectCutClosedReducedZ R q := by
  unfold fkRectCriticalCutFreeEventMass
  rw [← fkRectCriticalEventMass_cutClosed_eq_closedMass,
    fkRectCriticalEventMass_cutClosed_inter_eq]
  have hden := fkRectCriticalEventMass_cutClosed_inter_eq
    R q Set.univ
  rw [show {eta : R.Configuration |
      FKRectCutClosedConfiguration R eta ∧ eta ∈ Set.univ} =
      {eta | FKRectCutClosedConfiguration R eta} by ext; simp,
    fkRectCutClosedReducedEventWeight_univ] at hden
  rw [hden]
  have htotal : fkRectCriticalReducedZ R q ≠ 0 :=
    (fkRectCriticalReducedZ_pos R
      (lt_of_lt_of_le zero_lt_one hq)).ne'
  have hcut : fkRectCutClosedReducedZ R q ≠ 0 :=
    (fkRectCutClosedReducedZ_pos R
      (lt_of_lt_of_le zero_lt_one hq)).ne'
  field_simp



def fkRectCutEdgeEvent (R : FKRectTorus)
    (A : Set R.Configuration) :
    Set (FK.ecz_ClosedOff (fkRectCutGraph R)) :=
  {sigma | ((fkRectCutClosedEdgeConfigEquiv R).symm sigma).1 ∈ A}



theorem fkRectCut_ecz_eventWeight_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) :
    FK.ecz_eventWeight (fkRectCutGraph R) (fkRectCriticalP q) q
        (fkRectCutEdgeEvent R A) =
      (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card *
        fkRectCutClosedReducedEventWeight R q A := by
  unfold FK.ecz_eventWeight fkRectCutClosedReducedEventWeight
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (fkRectCutClosedEdgeConfigEquiv R)
  intro omega
  by_cases hA : omega.1 ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (show fkRectCutClosedEdgeConfigEquiv R omega ∈
        fkRectCutEdgeEvent R A by simpa [fkRectCutEdgeEvent])]
    rw [fkRectCut_fkWeight_critical_eq R hq]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (show fkRectCutClosedEdgeConfigEquiv R omega ∉
        fkRectCutEdgeEvent R A by simpa [fkRectCutEdgeEvent])]
    simp

theorem fkRectCut_ecz_fkZEdge_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    FK.ecz_fkZEdge (fkRectCutGraph R) (fkRectCriticalP q) q =
      (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card *
        fkRectCutClosedReducedZ R q := by
  rw [← fkRectCutClosedReducedEventWeight_univ]
  simpa [fkRectCutEdgeEvent, FK.ecz_eventWeight, FK.ecz_fkZEdge] using
    fkRectCut_ecz_eventWeight_eq R hq (Set.univ : Set R.Configuration)




theorem fkRectCriticalCutFreeEventMass_eq_cutGraph
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) :
    fkRectCriticalCutFreeEventMass R q A =
      ∑ sigma : ConfigSpace (Sym2 R.Vertex),
        (FK.ecz_closeOff (fkRectCutGraph R) ⁻¹'
          fkRectCutEdgeEvent R A).indicator (fun _ => (1 : Real)) sigma *
          FK.fkProb (fkRectCutGraph R) (fkRectCriticalP q) q sigma := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [fkRectCriticalCutFreeEventMass_eq_reduced R hq A,
    FK.ecz_eventProb_eq]
  rw [fkRectCut_ecz_eventWeight_eq R hq0,
    fkRectCut_ecz_fkZEdge_eq R hq0]
  have hp1 : 0 < 1 - fkRectCriticalP q := by
    linarith [fkRectCriticalP_lt_one hq0]
  have hfactor :
      (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card ≠ 0 :=
    (pow_pos hp1 _).ne'
  field_simp

end

end StatMech.FrontierD
