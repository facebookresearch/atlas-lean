/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalCutPushforward
import Code.FrontierD.FKRectCutFreeLaw










open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

open StatMech


abbrev FKRectHorizontalCutClosedConfig (R : FKRectTorus) :=
  {omega : R.Configuration //
    FKRectHorizontalCutClosedConfiguration R omega}

noncomputable instance instFintypeFKRectHorizontalCutClosedConfig
    (R : FKRectTorus) : Fintype (FKRectHorizontalCutClosedConfig R) := by
  unfold FKRectHorizontalCutClosedConfig
  infer_instance


def fkRectHorizontalCutGraphEdges (R : FKRectTorus) :
    Finset (Sym2 R.Vertex) :=
  (fkRectHorizontalCutEdges R).image (fkRectTorusIndexedEdge R)

@[simp] theorem mem_fkRectHorizontalCutGraphEdges
    (R : FKRectTorus) (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge R a ∈ fkRectHorizontalCutGraphEdges R ↔
      a ∈ fkRectHorizontalCutEdges R := by
  classical
  unfold fkRectHorizontalCutGraphEdges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, hab⟩
    exact (fkRectTorusIndexedEdge_injective R hab).symm ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩



theorem fkRectFullGraphConfiguration_eq_false_of_horizontalCutEdge
    (R : FKRectTorus) (eta : FKRectHorizontalCutClosedConfig R)
    {e : Sym2 R.Vertex} (he : e ∈ fkRectHorizontalCutGraphEdges R) :
    fkRectFullGraphConfiguration R eta.1 e = false := by
  classical
  rw [fkRectHorizontalCutGraphEdges, Finset.mem_image] at he
  rcases he with ⟨a, ha, rfl⟩
  rw [fkRectFullGraphConfiguration_indexedEdge]
  exact eta.2 a ha


noncomputable def fkRectHorizontalCylinderGraph
    (R : FKRectTorus) : SimpleGraph R.Vertex :=
  SimpleGraph.fromEdgeSet
    ((fkRectTorusGraph R).edgeSet \
      (fkRectHorizontalCutGraphEdges R : Set (Sym2 R.Vertex)))

noncomputable instance instDecidableRelFKRectHorizontalCylinderGraph
    (R : FKRectTorus) : DecidableRel (fkRectHorizontalCylinderGraph R).Adj :=
  fun _ _ => Classical.dec _

theorem fkRectHorizontalCylinderGraph_adj_iff
    (R : FKRectTorus) (x y : R.Vertex) :
    (fkRectHorizontalCylinderGraph R).Adj x y ↔
      (fkRectTorusGraph R).Adj x y ∧
        s(x, y) ∉ fkRectHorizontalCutGraphEdges R := by
  rw [fkRectHorizontalCylinderGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨hedge, hcut⟩, _⟩
    exact ⟨(SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).1 hedge, hcut⟩
  · rintro ⟨hxy, hcut⟩
    exact ⟨⟨(SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).2 hxy,
      hcut⟩, hxy.ne⟩



theorem mem_fkRectHorizontalCylinderGraph_edgeSet_iff
    (R : FKRectTorus) (e : Sym2 R.Vertex) :
    e ∈ (fkRectHorizontalCylinderGraph R).edgeSet ↔
      ∃ a : R.EdgeIndex,
        a ∉ fkRectHorizontalCutEdges R ∧
          fkRectTorusIndexedEdge R a = e := by
  obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep e
  rw [SimpleGraph.mem_edgeSet, fkRectHorizontalCylinderGraph_adj_iff]
  constructor
  · rintro ⟨htorus, hcut⟩
    obtain ⟨a, ha⟩ := htorus
    refine ⟨a, ?_, ha⟩
    intro hacut
    apply hcut
    rw [← ha]
    exact (mem_fkRectHorizontalCutGraphEdges R a).2 hacut
  · rintro ⟨a, hacut, ha⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    intro hcut
    have hcut' : fkRectTorusIndexedEdge R a ∈
        fkRectHorizontalCutGraphEdges R := by
      simpa only [ha] using hcut
    exact hacut ((mem_fkRectHorizontalCutGraphEdges R a).1 hcut')



def fkRectHorizontalCutClosedToEdgeConfig (R : FKRectTorus)
    (omega : FKRectHorizontalCutClosedConfig R) :
    FK.ecz_ClosedOff (fkRectHorizontalCylinderGraph R) :=
  ⟨fkRectFullGraphConfiguration R omega.1, by
    intro e he
    have hnotCylinder : e ∉
        (fkRectHorizontalCylinderGraph R).edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using he
    by_cases htorus : e ∈ (fkRectTorusGraph R).edgeSet
    · obtain ⟨a, ha⟩ :=
        (mem_fkRectTorusGraph_edgeSet_iff R e).1 htorus
      have hacut : a ∈ fkRectHorizontalCutEdges R := by
        by_contra hnot
        apply hnotCylinder
        exact (mem_fkRectHorizontalCylinderGraph_edgeSet_iff R e).2
          ⟨a, hnot, ha⟩
      rw [← ha, fkRectFullGraphConfiguration_indexedEdge]
      exact omega.2 a hacut
    · exact fkRectFullGraphConfiguration_eq_false_of_not_edge
        R omega.1 htorus⟩


def fkRectEdgeConfigToHorizontalCutClosed (R : FKRectTorus)
    (sigma : FK.ecz_ClosedOff (fkRectHorizontalCylinderGraph R)) :
    FKRectHorizontalCutClosedConfig R :=
  ⟨fun a => sigma.1 (fkRectTorusIndexedEdge R a), by
    intro a hacut
    apply sigma.2
    intro hedge
    have hedgeSet : fkRectTorusIndexedEdge R a ∈
        (fkRectHorizontalCylinderGraph R).edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using hedge
    obtain ⟨b, hb, hba⟩ :=
      (mem_fkRectHorizontalCylinderGraph_edgeSet_iff R _).1 hedgeSet
    exact hb ((fkRectTorusIndexedEdge_injective R hba).symm ▸ hacut)⟩



def fkRectHorizontalCutClosedEdgeConfigEquiv (R : FKRectTorus) :
    FKRectHorizontalCutClosedConfig R ≃
      FK.ecz_ClosedOff (fkRectHorizontalCylinderGraph R) where
  toFun := fkRectHorizontalCutClosedToEdgeConfig R
  invFun := fkRectEdgeConfigToHorizontalCutClosed R
  left_inv omega := by
    apply Subtype.ext
    funext a
    exact fkRectFullGraphConfiguration_indexedEdge R omega.1 a
  right_inv sigma := by
    apply Subtype.ext
    funext e
    change fkRectFullGraphConfiguration R
        (fkRectEdgeConfigToHorizontalCutClosed R sigma).1 e = sigma.1 e
    by_cases htorus : e ∈ (fkRectTorusGraph R).edgeSet
    · obtain ⟨a, ha⟩ :=
        (mem_fkRectTorusGraph_edgeSet_iff R e).1 htorus
      rw [← ha, fkRectFullGraphConfiguration_indexedEdge]
      rfl
    · rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ htorus]
      symm
      apply sigma.2 e
      intro hedge
      have hedgeSet : e ∈
          (fkRectHorizontalCylinderGraph R).edgeSet := by
        simpa only [SimpleGraph.mem_edgeFinset] using hedge
      obtain ⟨a, _, ha⟩ :=
        (mem_fkRectHorizontalCylinderGraph_edgeSet_iff R e).1 hedgeSet
      exact htorus ((mem_fkRectTorusGraph_edgeSet_iff R e).2 ⟨a, ha⟩)

@[simp] theorem fkRectHorizontalCutClosedEdgeConfigEquiv_apply
    (R : FKRectTorus) (omega : FKRectHorizontalCutClosedConfig R) :
    (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 =
      fkRectFullGraphConfiguration R omega.1 := rfl



theorem fkRectHorizontalCylinder_openSub_eq
    (R : FKRectTorus) (omega : FKRectHorizontalCutClosedConfig R) :
    FK.openSub (fkRectHorizontalCylinderGraph R)
        (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 =
      fkRectOpenGraph R omega.1 := by
  rw [← fkOpenSub_fullGraphConfiguration R omega.1]
  apply SimpleGraph.ext
  ext x y
  simp only [FK.openSub_adj]
  constructor
  · rintro ⟨hcyl, hopen⟩
    exact ⟨(fkRectHorizontalCylinderGraph_adj_iff R x y).1 hcyl |>.1,
      hopen⟩
  · rintro ⟨htorus, hopen⟩
    refine ⟨(fkRectHorizontalCylinderGraph_adj_iff R x y).2
      ⟨htorus, ?_⟩, hopen⟩
    intro hcut
    have hfalse :=
      fkRectFullGraphConfiguration_eq_false_of_horizontalCutEdge
        R omega hcut
    rw [hfalse] at hopen
    exact Bool.noConfusion hopen


theorem fkRectHorizontalCylinder_numClusters_eq
    (R : FKRectTorus) (omega : FKRectHorizontalCutClosedConfig R) :
    FK.numClusters (fkRectHorizontalCylinderGraph R)
        (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 =
      fkRectNumClusters R omega.1 := by
  unfold FK.numClusters fkRectNumClusters
  exact Fintype.card_congr
    (by rw [fkRectHorizontalCylinder_openSub_eq R omega])


theorem fkRectHorizontalCylinder_openCount_eq
    (R : FKRectTorus) (omega : FKRectHorizontalCutClosedConfig R) :
    FK.openCount (fkRectHorizontalCylinderGraph R)
        (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 =
      fkRectOpenEdgeCount R omega.1 := by
  rw [fkOpenCount_eq_openSub_edgeFinset_card]
  have hfin :
      (FK.openSub (fkRectHorizontalCylinderGraph R)
          (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1).edgeFinset =
        (fkRectOpenGraph R omega.1).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [fkRectHorizontalCylinder_openSub_eq R omega]
  rw [hfin, fkRectOpenGraph_edgeFinset_card]



theorem fkRectHorizontalCylinder_fkWeight_critical_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : FKRectHorizontalCutClosedConfig R) :
    FK.fkWeight (fkRectHorizontalCylinderGraph R)
        (fkRectCriticalP q) q
        (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 =
      (1 - fkRectCriticalP q) ^
          (fkRectHorizontalCylinderGraph R).edgeFinset.card *
        fkRectCriticalReducedWeight R q omega.1 := by
  let sigma :=
    (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1
  let o := FK.openCount (fkRectHorizontalCylinderGraph R) sigma
  let c := FK.closedCount (fkRectHorizontalCylinderGraph R) sigma
  have hoc : o + c =
      (fkRectHorizontalCylinderGraph R).edgeFinset.card :=
    FK.openCount_add_closedCount
      (fkRectHorizontalCylinderGraph R) sigma
  have ho : o = fkRectOpenEdgeCount R omega.1 := by
    exact fkRectHorizontalCylinder_openCount_eq R omega
  have hp := fkRectCriticalP_eq_sqrt_mul_one_sub hq
  have hedgeProduct :
      FK.edgeProduct (fkRectHorizontalCylinderGraph R)
          (fkRectCriticalP q) sigma =
        (1 - fkRectCriticalP q) ^
            (fkRectHorizontalCylinderGraph R).edgeFinset.card *
          Real.sqrt q ^ fkRectOpenEdgeCount R omega.1 := by
    rw [FK.edgeProduct_eq_pow]
    change fkRectCriticalP q ^ o * (1 - fkRectCriticalP q) ^ c = _
    calc
      fkRectCriticalP q ^ o * (1 - fkRectCriticalP q) ^ c =
          (Real.sqrt q * (1 - fkRectCriticalP q)) ^ o *
            (1 - fkRectCriticalP q) ^ c := by
          nth_rewrite 1 [hp]
          rfl
      _ = Real.sqrt q ^ o * (1 - fkRectCriticalP q) ^ o *
            (1 - fkRectCriticalP q) ^ c := by rw [mul_pow]
      _ = (1 - fkRectCriticalP q) ^ (o + c) *
            Real.sqrt q ^ o := by
          rw [pow_add]
          ring
      _ = (1 - fkRectCriticalP q) ^
            (fkRectHorizontalCylinderGraph R).edgeFinset.card *
              Real.sqrt q ^ fkRectOpenEdgeCount R omega.1 := by
          rw [hoc, ho]
  unfold FK.fkWeight fkRectCriticalReducedWeight
  rw [hedgeProduct, fkRectHorizontalCylinder_numClusters_eq R omega]
  ring


def fkRectHorizontalCutClosedReducedEventWeight
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) : Real :=
  ∑ omega : FKRectHorizontalCutClosedConfig R,
    A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) omega.1


def fkRectHorizontalCutClosedReducedZ
    (R : FKRectTorus) (q : Real) : Real :=
  ∑ omega : FKRectHorizontalCutClosedConfig R,
    fkRectCriticalReducedWeight R q omega.1

theorem fkRectHorizontalCutClosedReducedEventWeight_univ
    (R : FKRectTorus) (q : Real) :
    fkRectHorizontalCutClosedReducedEventWeight R q Set.univ =
      fkRectHorizontalCutClosedReducedZ R q := by
  unfold fkRectHorizontalCutClosedReducedEventWeight
    fkRectHorizontalCutClosedReducedZ
  apply Finset.sum_congr rfl
  intro omega _
  rw [Set.indicator_of_mem (Set.mem_univ omega.1)]

theorem fkRectHorizontalCutClosedReducedZ_pos
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    0 < fkRectHorizontalCutClosedReducedZ R q := by
  unfold fkRectHorizontalCutClosedReducedZ
  apply Finset.sum_pos
  · intro omega _
    exact fkRectCriticalReducedWeight_pos R hq omega.1
  · let omega : FKRectHorizontalCutClosedConfig R :=
      ⟨fun _ => false, fun _ _ => rfl⟩
    exact ⟨omega, Finset.mem_univ omega⟩



theorem fkRect_horizontalCutClosed_indicatorReduced_sum
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) :
    (∑ eta : R.Configuration,
      {eta | FKRectHorizontalCutClosedConfiguration R eta ∧
        eta ∈ A}.indicator
        (fun eta => fkRectCriticalReducedWeight R q eta) eta) =
      fkRectHorizontalCutClosedReducedEventWeight R q A := by
  classical
  calc
    (∑ eta : R.Configuration,
      {eta | FKRectHorizontalCutClosedConfiguration R eta ∧
        eta ∈ A}.indicator
        (fun eta => fkRectCriticalReducedWeight R q eta) eta) =
      ∑ eta : R.Configuration,
        if FKRectHorizontalCutClosedConfiguration R eta then
          A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) eta
        else 0 := by
      apply Finset.sum_congr rfl
      intro eta _
      by_cases hc : FKRectHorizontalCutClosedConfiguration R eta
      · by_cases hA : eta ∈ A <;> simp [hc, hA]
      · simp [hc]
    _ = ∑ eta ∈ (Finset.univ.filter
          (FKRectHorizontalCutClosedConfiguration R)),
        A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) eta := by
      rw [Finset.sum_filter]
    _ = ∑ eta : FKRectHorizontalCutClosedConfig R,
        A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) eta.1 := by
      exact Finset.sum_subtype _ (by simp) _
    _ = fkRectHorizontalCutClosedReducedEventWeight R q A := rfl



theorem fkRectCriticalEventMass_horizontalCutClosed_inter_eq
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) :
    fkRectCriticalEventMass R q
        {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} =
      fkRectHorizontalCutClosedReducedEventWeight R q A /
        fkRectCriticalReducedZ R q := by
  unfold fkRectCriticalEventMass fkRectCriticalRandomClusterProb
  calc
    (∑ eta : R.Configuration,
      {eta | FKRectHorizontalCutClosedConfiguration R eta ∧
        eta ∈ A}.indicator
        (fun eta => fkRectCriticalReducedWeight R q eta /
          fkRectCriticalReducedZ R q) eta) =
      (∑ eta : R.Configuration,
        {eta | FKRectHorizontalCutClosedConfiguration R eta ∧
          eta ∈ A}.indicator
          (fun eta => fkRectCriticalReducedWeight R q eta) eta) /
        fkRectCriticalReducedZ R q := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro eta _
      by_cases hmem :
          FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A
      · have hset : eta ∈ {eta : R.Configuration |
            FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} := hmem
        rw [Set.indicator_of_mem hset, Set.indicator_of_mem hset]
      · have hset : eta ∉ {eta : R.Configuration |
            FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} := hmem
        rw [Set.indicator_of_notMem hset,
          Set.indicator_of_notMem hset, zero_div]
    _ = _ := by rw [fkRect_horizontalCutClosed_indicatorReduced_sum]



theorem fkRectCriticalHorizontalCutEventMass_eq_reduced
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (A : Set R.Configuration) :
    fkRectCriticalHorizontalCutEventMass R q A =
      fkRectHorizontalCutClosedReducedEventWeight R q A /
        fkRectHorizontalCutClosedReducedZ R q := by
  unfold fkRectCriticalHorizontalCutEventMass
  rw [← fkRectCriticalEventMass_horizontalCutClosed_eq_closedMass,
    fkRectCriticalEventMass_horizontalCutClosed_inter_eq]
  have hden := fkRectCriticalEventMass_horizontalCutClosed_inter_eq
    R q Set.univ
  rw [show {eta : R.Configuration |
      FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ Set.univ} =
      {eta | FKRectHorizontalCutClosedConfiguration R eta} by ext; simp,
    fkRectHorizontalCutClosedReducedEventWeight_univ] at hden
  rw [hden]
  have htotal : fkRectCriticalReducedZ R q ≠ 0 :=
    (fkRectCriticalReducedZ_pos R
      (lt_of_lt_of_le zero_lt_one hq)).ne'
  have hcyl : fkRectHorizontalCutClosedReducedZ R q ≠ 0 :=
    (fkRectHorizontalCutClosedReducedZ_pos R
      (lt_of_lt_of_le zero_lt_one hq)).ne'
  field_simp


def fkRectHorizontalCylinderEdgeEvent (R : FKRectTorus)
    (A : Set R.Configuration) :
    Set (FK.ecz_ClosedOff (fkRectHorizontalCylinderGraph R)) :=
  {sigma |
    ((fkRectHorizontalCutClosedEdgeConfigEquiv R).symm sigma).1 ∈ A}

theorem fkRectHorizontalCylinder_ecz_eventWeight_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) :
    FK.ecz_eventWeight (fkRectHorizontalCylinderGraph R)
        (fkRectCriticalP q) q
        (fkRectHorizontalCylinderEdgeEvent R A) =
      (1 - fkRectCriticalP q) ^
          (fkRectHorizontalCylinderGraph R).edgeFinset.card *
        fkRectHorizontalCutClosedReducedEventWeight R q A := by
  unfold FK.ecz_eventWeight
    fkRectHorizontalCutClosedReducedEventWeight
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (fkRectHorizontalCutClosedEdgeConfigEquiv R)
  intro omega
  by_cases hA : omega.1 ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (show
        fkRectHorizontalCutClosedEdgeConfigEquiv R omega ∈
          fkRectHorizontalCylinderEdgeEvent R A by
            simpa [fkRectHorizontalCylinderEdgeEvent])]
    rw [fkRectHorizontalCylinder_fkWeight_critical_eq R hq]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (show
        fkRectHorizontalCutClosedEdgeConfigEquiv R omega ∉
          fkRectHorizontalCylinderEdgeEvent R A by
            simpa [fkRectHorizontalCylinderEdgeEvent])]
    simp

theorem fkRectHorizontalCylinder_ecz_fkZEdge_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    FK.ecz_fkZEdge (fkRectHorizontalCylinderGraph R)
        (fkRectCriticalP q) q =
      (1 - fkRectCriticalP q) ^
          (fkRectHorizontalCylinderGraph R).edgeFinset.card *
        fkRectHorizontalCutClosedReducedZ R q := by
  rw [← fkRectHorizontalCutClosedReducedEventWeight_univ]
  simpa [fkRectHorizontalCylinderEdgeEvent, FK.ecz_eventWeight,
    FK.ecz_fkZEdge] using
      fkRectHorizontalCylinder_ecz_eventWeight_eq
        R hq (Set.univ : Set R.Configuration)



theorem fkRectCriticalHorizontalCutEventMass_eq_cylinderGraph
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (A : Set R.Configuration) :
    fkRectCriticalHorizontalCutEventMass R q A =
      ∑ sigma : ConfigSpace (Sym2 R.Vertex),
        (FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) ⁻¹'
          fkRectHorizontalCylinderEdgeEvent R A).indicator
            (fun _ => (1 : Real)) sigma *
          FK.fkProb (fkRectHorizontalCylinderGraph R)
            (fkRectCriticalP q) q sigma := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [fkRectCriticalHorizontalCutEventMass_eq_reduced R hq A,
    FK.ecz_eventProb_eq]
  rw [fkRectHorizontalCylinder_ecz_eventWeight_eq R hq0,
    fkRectHorizontalCylinder_ecz_fkZEdge_eq R hq0]
  have hp1 : 0 < 1 - fkRectCriticalP q := by
    linarith [fkRectCriticalP_lt_one hq0]
  have hfactor :
      (1 - fkRectCriticalP q) ^
          (fkRectHorizontalCylinderGraph R).edgeFinset.card ≠ 0 :=
    (pow_pos hp1 _).ne'
  field_simp

end

end StatMech.FrontierD
