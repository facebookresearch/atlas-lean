/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































































import Code.Percolation.Exploration
import Code.Percolation.SubcriticalDecay
import Code.Percolation.SubcriticalDecayFull
import Code.Percolation.DctDifferentialFull
import Code.Percolation.LastExit

open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal

namespace StatMech

namespace Percolation

open StatMech.Lattice









section AbstractWalk

variable {V : Type*} {G : SimpleGraph V}





theorem firstExitIndex {a b : V} (p : G.Walk a b) (D : Set V) [DecidablePred (· ∈ D)]
    (hb : b ∉ D) :
    ∃ j, j ≤ p.length ∧ p.getVert j ∉ D ∧ ∀ i, i < j → p.getVert i ∈ D := by
  classical
  set Tt : Finset ℕ := (Finset.range (p.length + 1)).filter (fun n => p.getVert n ∉ D) with hT
  have hLmem : p.length ∈ Tt := by
    rw [hT]; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [p.getVert_length]; exact hb⟩
  have hTne : Tt.Nonempty := ⟨p.length, hLmem⟩
  set j := Tt.min' hTne with hj
  have hjT : j ∈ Tt := Tt.min'_mem hTne
  rw [hT] at hjT
  simp only [Finset.mem_filter, Finset.mem_range] at hjT
  obtain ⟨hjle, hjD⟩ := hjT
  refine ⟨j, by omega, hjD, ?_⟩
  intro i hij
  by_contra hiD
  have hiT : i ∈ Tt := by
    rw [hT]; simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hiD⟩
  have := Tt.min'_le i hiT
  rw [← hj] at this; omega




theorem take_support_sub {a b : V} (p : G.Walk a b) (D : Set V) {j : ℕ}
    (hbefore : ∀ i, i < j → p.getVert i ∈ D) :
    ∀ z ∈ (p.take j).support, z ∈ D ∨ z = p.getVert j := by
  intro z hz
  rw [Walk.mem_support_iff_exists_getVert] at hz
  obtain ⟨k, hk, hkle⟩ := hz
  rw [Walk.take_getVert] at hk
  rw [Walk.take_length] at hkle
  by_cases hkj : k < j
  · left; rw [show min j k = k from by omega] at hk; rw [← hk]; exact hbefore k hkj
  · right; rw [show min j k = j from by omega] at hk; exact hk.symm






theorem exists_firstExit_induce {a b : V} (p : G.Walk a b) (D T : Set V)
    [DecidablePred (· ∈ D)] (ha : a ∈ T) (hb : b ∉ D)
    (hDinT : ∀ i, p.getVert i ∈ D → p.getVert i ∈ T)
    (hstep : ∀ i, i < p.length → p.getVert i ∈ D → p.getVert (i + 1) ∈ T) :
    ∃ (w : V) (hwT : w ∈ T), w ∉ D ∧
      Nonempty ((G.induce T).Walk ⟨a, ha⟩ ⟨w, hwT⟩) := by
  classical
  obtain ⟨j, hjle, hjD, hbefore⟩ := firstExitIndex p D hb
  have hwT : p.getVert j ∈ T := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, p.getVert_zero]; exact ha
    · have hprev : p.getVert (j - 1) ∈ D := hbefore (j - 1) (by omega)
      have hjlt : j - 1 < p.length := by omega
      have := hstep (j - 1) hjlt hprev
      rwa [show j - 1 + 1 = j from by omega] at this
  have hsupp : ∀ z ∈ (p.take j).support, z ∈ T := by
    intro z hz
    rcases take_support_sub p D hbefore z hz with hzD | hzeq
    · have hzmem := hz
      rw [Walk.mem_support_iff_exists_getVert] at hzmem
      obtain ⟨k, hk, _⟩ := hzmem
      rw [Walk.take_getVert] at hk
      rw [← hk]; exact hDinT (min j k) (hk ▸ hzD)
    · rw [hzeq]; exact hwT
  refine ⟨p.getVert j, hwT, hjD, ⟨?_⟩⟩
  exact ((p.take j).induce T hsupp).copy rfl rfl

end AbstractWalk



variable {d : ℕ}




theorem adj_box_step {m : ℕ} {x z : Site d} (hx : x ∈ box d m)
    (hadj : (hypercubicLattice d).Adj x z) : z ∈ box d (m + 1) := by
  rw [hypercubicLattice_adj] at hadj
  intro i
  have hxi : (x i).natAbs ≤ m := hx i
  have hdiff : (z i - x i).natAbs ≤ 1 := by
    have hle : (z i - x i).natAbs ≤ ∑ j, (x j - z j).natAbs := by
      have hcongr : (∑ j, (x j - z j).natAbs) = ∑ j, (z j - x j).natAbs := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Int.natAbs_neg, neg_sub]
      rw [hcongr]
      exact Finset.single_le_sum (f := fun j => (z j - x j).natAbs)
        (by intros; positivity) (Finset.mem_univ i)
    omega
  have htri : (z i).natAbs ≤ (x i).natAbs + (z i - x i).natAbs := by
    have heq : z i = x i + (z i - x i) := by ring
    calc (z i).natAbs = (x i + (z i - x i)).natAbs := by rw [← heq]
      _ ≤ (x i).natAbs + (z i - x i).natAbs := Int.natAbs_add_le _ _
  omega


noncomputable def boxFinsetOC (d n : ℕ) : Finset (Site d) := (box_finite d n).toFinset

@[simp]
theorem mem_boxFinsetOC {d n : ℕ} {x : Site d} : x ∈ boxFinsetOC d n ↔ x ∈ box d n := by
  simp [boxFinsetOC]









def offClusterBoxCrossing (d : ℕ) (C : Set (Site d)) (y : Site d) (n : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ z, z ∉ box d (n - 1) ∧ ∃ (hy : y ∈ box d n \ C) (hz : z ∈ box d n \ C),
    ConnectedWithin d ω (box d n \ C) ⟨y, hy⟩ ⟨z, hz⟩






theorem extract_box (ω : ConfigSpace (Sym2 (Site d))) (C : Set (Site d)) (y v : Site d) (n : ℕ)
    (hn : 1 ≤ n) (hyC : y ∉ C) (hvC : v ∉ C)
    (hybox : y ∈ box d n) (hvbox : v ∉ box d (n - 1))
    (hconn : ConnectedWithin d ω {z | z ∉ C} ⟨y, hyC⟩ ⟨v, hvC⟩) :
    ∃ (z : Site d) (hz : z ∈ box d n \ C), z ∉ box d (n - 1) ∧
      ConnectedWithin d ω (box d n \ C) ⟨y, hybox, hyC⟩ ⟨z, hz⟩ := by
  classical
  obtain ⟨w⟩ := hconn
  set G := openSubgraph d ω with hG
  have hw' : (G.induce {z : Site d | z ∉ C}).Walk ⟨y, hyC⟩ ⟨v, hvC⟩ := w
  set e := (SimpleGraph.Embedding.induce (G := G) {z : Site d | z ∉ C}) with he
  set p : G.Walk y v := (hw'.map e.toHom).copy rfl rfl with hp
  have hpC : ∀ i, p.getVert i ∉ C := by
    intro i
    have hgv : (p.getVert i) = ((hw'.getVert i : {z : Site d | z ∉ C}) : Site d) := by
      rw [hp, SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.getVert_map]; rfl
    rw [hgv]; exact (hw'.getVert i).2
  have hyT : y ∈ box d n \ C := ⟨hybox, hyC⟩
  have hDinT : ∀ i, p.getVert i ∈ box d (n - 1) → p.getVert i ∈ box d n \ C :=
    fun i hi => ⟨box_mono d (by omega) hi, hpC i⟩
  have hstep : ∀ i, i < p.length → p.getVert i ∈ box d (n - 1) →
      p.getVert (i + 1) ∈ box d n \ C := by
    intro i hi hiD
    have hadj' : (hypercubicLattice d).Adj (p.getVert i) (p.getVert (i + 1)) :=
      (p.adj_getVert_succ hi).1
    refine ⟨?_, hpC (i + 1)⟩
    have := adj_box_step hiD hadj'; rwa [show n - 1 + 1 = n from by omega] at this
  obtain ⟨z, hzT, hzD, ⟨ww⟩⟩ :=
    exists_firstExit_induce p (box d (n - 1)) (box d n \ C) hyT hvbox hDinT hstep
  exact ⟨z, hzT, hzD, ⟨ww⟩⟩







theorem connWithinR_congr (R : Set (Site d)) {a b : Site d} (ha : a ∈ R) (hb : b ∈ R)
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ x ∈ R, ∀ z ∈ R, ω s(x, z) = ω' s(x, z)) :
    ConnectedWithin d ω R ⟨a, ha⟩ ⟨b, hb⟩ ↔ ConnectedWithin d ω' R ⟨a, ha⟩ ⟨b, hb⟩ := by
  have hG : openSubgraphInduce d ω R = openSubgraphInduce d ω' R := by
    apply SimpleGraph.ext
    ext aa bb
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    rw [h aa aa.2 bb bb.2]
  unfold ConnectedWithin
  rw [hG]




noncomputable def boxOffCEdges (d : ℕ) (C : Set (Site d)) (n : ℕ) :
    Finset (Sym2 (Site d)) := by
  classical
  exact (edgesWithinFinset (boxFinsetOC d n)).filter (fun e => ∀ z ∈ e, z ∉ C)

theorem mem_boxOffCEdges {C : Set (Site d)} {n : ℕ} {x z : Site d}
    (hx : x ∈ box d n) (hxC : x ∉ C) (hz : z ∈ box d n) (hzC : z ∉ C) :
    s(x, z) ∈ boxOffCEdges d C n := by
  classical
  unfold boxOffCEdges
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [mem_edgesWithinFinset]
    exact ⟨x, mem_boxFinsetOC.mpr hx, z, mem_boxFinsetOC.mpr hz, rfl⟩
  · intro w hw
    rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> assumption



theorem agree_boxOffC {C : Set (Site d)} {n : ℕ} {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ (boxOffCEdges d C n : Set (Sym2 (Site d))), ω e = ω' e)
    {x z : Site d} (hx : x ∈ box d n \ C) (hz : z ∈ box d n \ C) :
    ω s(x, z) = ω' s(x, z) := by
  apply hagree
  rw [Finset.mem_coe]
  exact mem_boxOffCEdges hx.1 hx.2 hz.1 hz.2



theorem offClusterBoxCrossing_congr {C : Set (Site d)} {y : Site d} {n : ℕ}
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ (boxOffCEdges d C n : Set (Sym2 (Site d))), ω e = ω' e) :
    offClusterBoxCrossing d C y n ω ↔ offClusterBoxCrossing d C y n ω' := by
  have key : ∀ (η η' : ConfigSpace (Sym2 (Site d))),
      (∀ e ∈ (boxOffCEdges d C n : Set (Sym2 (Site d))), η e = η' e) →
      offClusterBoxCrossing d C y n η → offClusterBoxCrossing d C y n η' := by
    intro η η' hag hηcross
    obtain ⟨z, hzbox, hy, hz, hconn⟩ := hηcross
    refine ⟨z, hzbox, hy, hz, ?_⟩
    rw [← connWithinR_congr (box d n \ C) hy hz (fun x hx w hw => agree_boxOffC hag hx hw)]
    exact hconn
  exact ⟨key ω ω' hagree, key ω' ω (fun e he => (hagree e he).symm)⟩







theorem offClusterBoxCrossing_dependsOn (C : Set (Site d)) (y : Site d) (n : ℕ) :
    DependsOn ({ω | offClusterBoxCrossing d C y n ω}.indicator (fun _ => (1 : ℝ)))
      (boxOffCEdges d C n : Set (Sym2 (Site d))) := by
  intro ω ω' h
  have hiff : (ω ∈ {ω | offClusterBoxCrossing d C y n ω}) ↔
      (ω' ∈ {ω | offClusterBoxCrossing d C y n ω}) := by
    simp only [Set.mem_setOf_eq]
    exact offClusterBoxCrossing_congr (fun e he => h e he)
  by_cases hmem : ω ∈ {ω | offClusterBoxCrossing d C y n ω}
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun hc => hmem (hiff.mpr hc))]






theorem disjoint_boxOffC_incident (K S : Finset (Site d)) (n : ℕ) :
    Disjoint (boxOffCEdges d (K : Set (Site d)) n) (incidentWithinFinset K S) := by
  classical
  rw [Finset.disjoint_left]
  intro e he hinc
  unfold boxOffCEdges at he
  rw [Finset.mem_filter] at he
  obtain ⟨_, hnotinK⟩ := he
  rw [mem_incidentWithinFinset] at hinc
  obtain ⟨x, hxK, _, _, rfl⟩ := hinc
  exact hnotinK x (by rw [Sym2.mem_iff]; left; rfl) hxK


theorem boundaryEdge_notMem_boxOffC (K : Finset (Site d)) (x y : Site d) (n : ℕ)
    (hxK : x ∈ K) : s(x, y) ∉ boxOffCEdges d (K : Set (Site d)) n := by
  classical
  unfold boxOffCEdges
  rw [Finset.mem_filter]
  rintro ⟨_, hnotinK⟩
  exact hnotinK x (by rw [Sym2.mem_iff]; left; rfl) (by simpa using hxK)





theorem disjoint_boxOffC_incidentUnion (K S : Finset (Site d)) (x y : Site d) (n : ℕ)
    (hxK : x ∈ K) :
    Disjoint (incidentWithinFinset K S ∪ {s(x, y)}) (boxOffCEdges d (K : Set (Site d)) n) := by
  classical
  rw [Finset.disjoint_union_left]
  refine ⟨(disjoint_boxOffC_incident K S n).symm, ?_⟩
  rw [Finset.disjoint_singleton_left]
  exact boundaryEdge_notMem_boxOffC K x y n hxK





theorem dependsOn_inter {E : Type*} {A B : Set (ConfigSpace E)} {T U : Set E}
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) T)
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) U) :
    DependsOn ((A ∩ B).indicator (fun _ => (1 : ℝ))) (T ∪ U) := by
  have hrw : (A ∩ B).indicator (fun _ => (1 : ℝ))
      = fun ω => A.indicator (fun _ => (1 : ℝ)) ω * B.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω; rw [← Set.inter_indicator_mul]; simp
  rw [hrw]
  intro ω ω' h
  simp only
  rw [hA (fun e he => h e (Or.inl he)), hB (fun e he => h e (Or.inr he))]

















theorem offCluster_factor (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (K : Finset (Site d)) (x y : Site d) (n : ℕ)
    (hxK : x ∈ K) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
          ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
          ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω})
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
            ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
        * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
            {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω} := by
  have hA : DependsOn ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
        ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}).indicator (fun _ => (1 : ℝ)))
      ((incidentWithinFinset K S : Set (Sym2 (Site d))) ∪ ({s(x, y)} : Set (Sym2 (Site d)))) :=
    dependsOn_inter (clusterEvent_dependsOn hoS) (boundaryOpen_dependsOn (K : Set (Site d)) x y)
  refine indep_cylinder_inf p hp _ _ (incidentWithinFinset K S ∪ {s(x, y)})
    (boxOffCEdges d (K : Set (Site d)) n) ?_ ?_ (offClusterBoxCrossing_dependsOn _ _ _)
  · exact disjoint_boxOffC_incidentUnion K S x y n hxK
  · rw [Finset.coe_union, Finset.coe_singleton]
    exact hA







theorem offClusterBox_subset_crossingFrom (C : Set (Site d)) (y : Site d) (n : ℕ) :
    {ω | offClusterBoxCrossing d C y n ω} ⊆ crossingEventFrom d y n := by
  intro ω hω
  obtain ⟨z, hzbox, _, _, hconn⟩ := hω
  exact ⟨z, hconn.connected, hzbox⟩










theorem offClusterBox_crossProb_le (p : ℝ≥0) (hp : p ≤ 1) (C : Set (Site d)) (y : Site d)
    {L m n : ℕ} (hy : y ∈ box d L) (hmLn : m + L ≤ n) (hm : 1 ≤ m) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        {ω | offClusterBoxCrossing d C y n ω}
      ≤ crossProb d p hp m := by
  calc (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          {ω | offClusterBoxCrossing d C y n ω}
      ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (crossingEventFrom d y n) :=
        measureReal_mono (offClusterBox_subset_crossingFrom C y n)
    _ ≤ crossProb d p hp m := crossProbFrom_le p hp y hy hmLn hm














theorem crossingEvent_lastExit_boxsubset (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hSbox : (S : Set (Site d)) ⊆ box d (n - 1)) :
    crossingEvent d n ⊆
      ⋃ (K : Finset (Site d)), ⋃ (x : Site d), ⋃ (y : Site d),
        (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
          ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}
          ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω}) := by
  intro ω hω
  obtain ⟨v, hconn, hv⟩ := hω
  set C := clusterWithin d ω (S : Set (Site d)) (origin d) with hC
  have hoC : origin d ∈ C := ⟨hoS, hoS, connectedWithin_refl ω _ ⟨origin d, hoS⟩⟩
  have hCsub : C ⊆ (S : Set (Site d)) := fun z hz => hz.1
  have hvC : v ∉ C := fun hvc => hv (hSbox (hCsub hvc))
  have hCfin : C.Finite := (S.finite_toSet).subset hCsub
  set K := hCfin.toFinset with hK
  have hKC : (K : Set (Site d)) = C := by simp [hK]
  obtain ⟨x, y, hx, hy, hopen, hwithin⟩ := lattice_lastExit ω C (origin d) v hoC hvC hconn
  have hxbox : x ∈ box d (n - 1) := hSbox (hCsub hx)
  have hadj : (hypercubicLattice d).Adj x y := hopen.1
  have hybox : y ∈ box d n := by
    have := adj_box_step hxbox hadj
    rwa [show n - 1 + 1 = n from by omega] at this
  obtain ⟨z, hz, _hzbox, hzconn⟩ := extract_box ω C y v n hn hy hvC hybox hv hwithin
  simp only [Set.mem_iUnion]
  refine ⟨K, x, y, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · show clusterWithin d ω (S : Set (Site d)) (origin d) = (K : Set (Site d))
    rw [hKC]
  · show boundaryOpen d (K : Set (Site d)) x y ω
    rw [hKC]; exact ⟨hx, hy, hopen⟩
  · show offClusterBoxCrossing d (K : Set (Site d)) y n ω
    rw [hKC]
    exact ⟨z, _hzbox, ⟨hybox, hy⟩, hz, hzconn⟩






















end Percolation

end StatMech
