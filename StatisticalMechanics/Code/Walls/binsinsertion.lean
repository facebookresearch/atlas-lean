/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Walls.bcl2close
import Code.Walls.bcorcorridors
import Code.Walls.bc117mergeproof
import Code.IsingFK.HisingBoxClose

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK

namespace StatMech.Walls

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000













theorem bins_cluster_subset_of_openClosed (ω : ConfigSpace (Sym2 (Site 2)))
    {a : Site 2} {S : Set (Site 2)} (ha : a ∈ S)
    (hclosed : ∀ u v : Site 2, u ∈ S → IsOpenEdge 2 (removeSite 0 ω) u v → v ∈ S) :
    cluster 2 (removeSite 0 ω) a ⊆ S := by
  intro y hy
  obtain ⟨w⟩ := (hy : (openSubgraph 2 (removeSite 0 ω)).Reachable a y)
  exact bpt2_walk_invariant ω hclosed w ha








theorem bins_precursor_of_sides (ω : ConfigSpace (Sym2 (Site 2))) (a₁ a₂ a₃ : Site 2)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
      (hypercubicLattice 2).Adj 0 a₃)
    (S₁ S₂ S₃ : Set (Site 2))
    (ha : a₁ ∈ S₁ ∧ a₂ ∈ S₂ ∧ a₃ ∈ S₃)
    (hd : Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃)
    (hc : (∀ u v : Site 2, u ∈ S₁ → IsOpenEdge 2 (removeSite 0 ω) u v → v ∈ S₁) ∧
      (∀ u v : Site 2, u ∈ S₂ → IsOpenEdge 2 (removeSite 0 ω) u v → v ∈ S₂) ∧
      (∀ u v : Site 2, u ∈ S₃ → IsOpenEdge 2 (removeSite 0 ω) u v → v ∈ S₃))
    (hinf : (cluster 2 (removeSite 0 ω) a₁).Infinite ∧
      (cluster 2 (removeSite 0 ω) a₂).Infinite ∧
      (cluster 2 (removeSite 0 ω) a₃).Infinite) :
    ω ∈ NeighborTrifPrecursor 2 a₁ a₂ a₃ := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hd12, hd13, hd23⟩ := hd
  obtain ⟨hc1, hc2, hc3⟩ := hc
  have hsub1 : cluster 2 (removeSite 0 ω) a₁ ⊆ S₁ :=
    bins_cluster_subset_of_openClosed ω ha1 hc1
  have hsub2 : cluster 2 (removeSite 0 ω) a₂ ⊆ S₂ :=
    bins_cluster_subset_of_openClosed ω ha2 hc2
  have hsub3 : cluster 2 (removeSite 0 ω) a₃ ⊆ S₃ :=
    bins_cluster_subset_of_openClosed ω ha3 hc3
  refine ⟨hne, hadj, hinf, ?_, ?_, ?_⟩
  · intro hconn; exact (Set.disjoint_left.mp hd12) (hsub1 (mem_cluster.mpr hconn)) ha2
  · intro hconn; exact (Set.disjoint_left.mp hd13) (hsub1 (mem_cluster.mpr hconn)) ha3
  · intro hconn; exact (Set.disjoint_left.mp hd23) (hsub2 (mem_cluster.mpr hconn)) ha3











def bins_ExtPred (u₁ u₂ u₃ : Site 2) (ρ : ConfigSpace (Sym2 (Site 2))) : Prop :=
  ((cluster 2 ρ u₁).Infinite ∧ (cluster 2 ρ u₂).Infinite ∧ (cluster 2 ρ u₃).Infinite) ∧
    (cluster 2 ρ u₁ ≠ cluster 2 ρ u₂ ∧ cluster 2 ρ u₁ ≠ cluster 2 ρ u₃ ∧
      cluster 2 ρ u₂ ≠ cluster 2 ρ u₃)




def bins_ExtEvent (I : Finset (Sym2 (Site 2))) (u₁ u₂ u₃ : Site 2) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | bins_ExtPred u₁ u₂ u₃ (removeSite 0 (bpt2_closeI I ω))}




theorem bins_ExtEvent_dependsOn (I : Finset (Sym2 (Site 2))) (u₁ u₂ u₃ : Site 2) :
    DependsOn (bins_ExtEvent I u₁ u₂ u₃) ((↑I : Set (Sym2 (Site 2)))ᶜ) := by
  intro ω ω' hag
  change bins_ExtPred u₁ u₂ u₃ (removeSite 0 (bpt2_closeI I ω))
      ↔ bins_ExtPred u₁ u₂ u₃ (removeSite 0 (bpt2_closeI I ω'))
  rw [bpt2_removeSite_closeI_congr I hag]


theorem bins_measurable_closeI (I : Finset (Sym2 (Site 2))) :
    Measurable (fun ω : ConfigSpace (Sym2 (Site 2)) ↦ bpt2_closeI I ω) := by
  apply measurable_pi_lambda
  intro e
  unfold bpt2_closeI
  by_cases he : e ∈ I
  · simp [he]
  · simp only [he, if_false]
    exact measurable_pi_apply e




theorem bins_ExtEvent_measurable (I : Finset (Sym2 (Site 2))) (u₁ u₂ u₃ : Site 2) :
    MeasurableSet (bins_ExtEvent I u₁ u₂ u₃) := by
  let f : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)) :=
    fun ω ↦ removeSite 0 (bpt2_closeI I ω)
  have hf : Measurable f := (measurable_removeSite 0).comp (bins_measurable_closeI I)
  have hinf : ∀ u : Site 2, MeasurableSet {ω | (cluster 2 (f ω) u).Infinite} := by
    intro u
    exact hf (measurableSet_clusterInfinite u)
  have hconn : ∀ u v : Site 2, MeasurableSet {ω | Connected 2 (f ω) u v} := by
    intro u v
    exact hf (measurableSet_connected u v)
  have heq : bins_ExtEvent I u₁ u₂ u₃ =
      (({ω | (cluster 2 (f ω) u₁).Infinite} ∩
        {ω | (cluster 2 (f ω) u₂).Infinite}) ∩
        {ω | (cluster 2 (f ω) u₃).Infinite}) ∩
      ((({ω | Connected 2 (f ω) u₁ u₂}ᶜ) ∩
        ({ω | Connected 2 (f ω) u₁ u₃}ᶜ)) ∩
        ({ω | Connected 2 (f ω) u₂ u₃}ᶜ)) := by
    ext ω
    simp only [bins_ExtEvent, bins_ExtPred, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_compl_iff, f]
    constructor
    · rintro ⟨⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩
      exact ⟨⟨⟨hi1, hi2⟩, hi3⟩,
        ⟨⟨fun hc ↦ hd12 (cluster_eq_of_connected hc),
          fun hc ↦ hd13 (cluster_eq_of_connected hc)⟩,
          fun hc ↦ hd23 (cluster_eq_of_connected hc)⟩⟩
    · rintro ⟨⟨⟨hi1, hi2⟩, hi3⟩, ⟨⟨hd12, hd13⟩, hd23⟩⟩
      exact ⟨⟨hi1, hi2, hi3⟩,
        fun h ↦ hd12 (mem_cluster.mp (by rw [h]; exact self_mem_cluster _ u₂)),
        fun h ↦ hd13 (mem_cluster.mp (by rw [h]; exact self_mem_cluster _ u₃)),
        fun h ↦ hd23 (mem_cluster.mp (by rw [h]; exact self_mem_cluster _ u₃))⟩
  rw [heq]
  exact (((hinf u₁).inter (hinf u₂)).inter (hinf u₃)).inter
    ((((hconn u₁ u₂).compl).inter ((hconn u₁ u₃).compl)).inter
      ((hconn u₂ u₃).compl))





theorem bins_exists_ExtEvent_pos_of_cover (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ)
    (I : Finset (Sym2 (Site 2)))
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n))
    (hcover : threeMeetBox 2 n ⊆
      ⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2, bins_ExtEvent I u₁ u₂ u₃) :
    ∃ u₁ u₂ u₃ : Site 2,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (bins_ExtEvent I u₁ u₂ u₃) := by
  let μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hu : μ (⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2,
      bins_ExtEvent I u₁ u₂ u₃) = 0 := by
    refine measure_iUnion_null fun u₁ ↦ measure_iUnion_null fun u₂ ↦
      measure_iUnion_null fun u₃ ↦ ?_
    exact hcon u₁ u₂ u₃
  have hz : μ (threeMeetBox 2 n) = 0 :=
    le_antisymm ((measure_mono hcover).trans_eq hu) bot_le
  apply (ne_of_gt hpos)
  simpa [μ] using hz









theorem bins_openSubgraph_closeTouch_eq_removeBox (n : ℕ)
    (ω : ConfigSpace (Sym2 (Site 2))) :
    openSubgraph 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω)) =
      openSubgraph 2 (removeSites (boxFinset 2 n) ω) := by
  ext x y
  simp only [openSubgraph_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    unfold removeSite bpt2_closeI at hopen
    unfold removeSites
    have htouch : s(x,y) ∈ bondFinsetTouch 2 n ↔ x ∈ box 2 n ∨ y ∈ box 2 n := by
      rw [hbx_mem_bondFinsetTouch_iff]
      simp only [hadj, true_and]
    have hsite : (∃ t ∈ boxFinset 2 n, t ∈ s(x,y)) ↔ x ∈ box 2 n ∨ y ∈ box 2 n := by
      simp only [Sym2.mem_iff, mem_boxFinset]
      aesop
    by_cases h0 : (0 : Site 2) ∈ s(x,y)
    · simp [h0] at hopen
    · simp only [h0, if_false] at hopen
      by_cases ht : x ∈ box 2 n ∨ y ∈ box 2 n
      · rw [if_pos (htouch.mpr ht)] at hopen
        contradiction
      · rw [if_neg (fun h ↦ ht (hsite.mp h))]
        rw [if_neg (fun h ↦ ht (htouch.mp h))] at hopen
        exact hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    unfold removeSites at hopen
    unfold removeSite bpt2_closeI
    have htouch : s(x,y) ∈ bondFinsetTouch 2 n ↔ x ∈ box 2 n ∨ y ∈ box 2 n := by
      rw [hbx_mem_bondFinsetTouch_iff]
      simp only [hadj, true_and]
    have hsite : (∃ t ∈ boxFinset 2 n, t ∈ s(x,y)) ↔ x ∈ box 2 n ∨ y ∈ box 2 n := by
      simp only [Sym2.mem_iff, mem_boxFinset]
      aesop
    by_cases ht : x ∈ box 2 n ∨ y ∈ box 2 n
    · rw [if_pos (hsite.mpr ht)] at hopen
      contradiction
    · have h0 : (0 : Site 2) ∉ s(x,y) := by
        intro h
        rw [Sym2.mem_iff] at h
        rcases h with h | h <;> subst_vars <;> apply ht <;> simp [mem_box]
      rw [if_neg h0, if_neg (fun h ↦ ht (htouch.mp h))]
      rw [if_neg (fun h ↦ ht (hsite.mp h))] at hopen
      exact hopen


theorem bins_cluster_closeTouch_eq_removeBox (n : ℕ)
    (ω : ConfigSpace (Sym2 (Site 2))) (u : Site 2) :
    cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω)) u =
      cluster 2 (removeSites (boxFinset 2 n) ω) u := by
  ext z
  change (openSubgraph 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω))).Reachable u z ↔
    (openSubgraph 2 (removeSites (boxFinset 2 n) ω)).Reachable u z
  rw [bins_openSubgraph_closeTouch_eq_removeBox]




theorem bins_threeMeetBox_subset_iUnion_ExtEvent_touch (n : ℕ) :
    threeMeetBox 2 n ⊆
      ⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2,
        bins_ExtEvent (bondFinsetTouch 2 n) u₁ u₂ u₃ := by
  intro ω hω
  obtain ⟨_, x₁, x₂, x₃, _, _, _, hi1, hi2, hi3, hd12, hd13, hd23⟩ := hω
  let T := boxFinset 2 n
  obtain ⟨u₁, hc1, _, hu1⟩ := bc117_boxAvoiding_external_infinite ω hi1 T
  obtain ⟨u₂, hc2, _, hu2⟩ := bc117_boxAvoiding_external_infinite ω hi2 T
  obtain ⟨u₃, hc3, _, hu3⟩ := bc117_boxAvoiding_external_infinite ω hi3 T
  have hcut12 : cluster 2 (removeSites T ω) u₁ ≠ cluster 2 (removeSites T ω) u₂ := by
    intro h
    have hc : Connected 2 (removeSites T ω) u₁ u₂ := mem_cluster.mp (by
      rw [h]
      exact self_mem_cluster _ u₂)
    have hc' : Connected 2 ω u₁ u₂ := connected_mono (daep_removeSites_le T ω) hc
    exact hd12 (cluster_eq_of_connected (hc1.trans (hc'.trans hc2.symm)))
  have hcut13 : cluster 2 (removeSites T ω) u₁ ≠ cluster 2 (removeSites T ω) u₃ := by
    intro h
    have hc : Connected 2 (removeSites T ω) u₁ u₃ := mem_cluster.mp (by
      rw [h]
      exact self_mem_cluster _ u₃)
    have hc' : Connected 2 ω u₁ u₃ := connected_mono (daep_removeSites_le T ω) hc
    exact hd13 (cluster_eq_of_connected (hc1.trans (hc'.trans hc3.symm)))
  have hcut23 : cluster 2 (removeSites T ω) u₂ ≠ cluster 2 (removeSites T ω) u₃ := by
    intro h
    have hc : Connected 2 (removeSites T ω) u₂ u₃ := mem_cluster.mp (by
      rw [h]
      exact self_mem_cluster _ u₃)
    have hc' : Connected 2 ω u₂ u₃ := connected_mono (daep_removeSites_le T ω) hc
    exact hd23 (cluster_eq_of_connected (hc2.trans (hc'.trans hc3.symm)))
  refine Set.mem_iUnion.mpr ⟨u₁, Set.mem_iUnion.mpr ⟨u₂, Set.mem_iUnion.mpr ⟨u₃, ?_⟩⟩⟩
  change bins_ExtPred u₁ u₂ u₃
    (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω))
  unfold bins_ExtPred
  rw [bins_cluster_closeTouch_eq_removeBox,
    bins_cluster_closeTouch_eq_removeBox, bins_cluster_closeTouch_eq_removeBox]
  simpa [T] using ⟨⟨hu1, hu2, hu3⟩, hcut12, hcut13, hcut23⟩



theorem bins_exists_ExtEvent_touch_pos (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n)) :
    ∃ u₁ u₂ u₃ : Site 2,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (bins_ExtEvent (bondFinsetTouch 2 n) u₁ u₂ u₃) :=
  bins_exists_ExtEvent_pos_of_cover p hp1 n (bondFinsetTouch 2 n) hpos
    (bins_threeMeetBox_subset_iUnion_ExtEvent_touch n)


def bins_ShellExtEvent (n : ℕ) (v₁ v₂ v₃ u₁ u₂ u₃ : Site 2) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | (v₁ ∈ box 2 n ∧ (hypercubicLattice 2).Adj v₁ u₁) ∧
    (v₂ ∈ box 2 n ∧ (hypercubicLattice 2).Adj v₂ u₂) ∧
    (v₃ ∈ box 2 n ∧ (hypercubicLattice 2).Adj v₃ u₃) ∧
    ω ∈ bins_ExtEvent (bondFinsetTouch 2 n) u₁ u₂ u₃}

theorem bins_ShellExtEvent_dependsOn (n : ℕ) (v₁ v₂ v₃ u₁ u₂ u₃ : Site 2) :
    DependsOn (bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃)
      ((↑(bondFinsetTouch 2 n) : Set (Sym2 (Site 2)))ᶜ) := by
  intro ω ω' hag
  simp only [bins_ShellExtEvent, Set.mem_setOf_eq]
  have hExt := (bins_ExtEvent_dependsOn (bondFinsetTouch 2 n) u₁ u₂ u₃) ω ω' hag
  tauto

theorem bins_ShellExtEvent_measurable (n : ℕ) (v₁ v₂ v₃ u₁ u₂ u₃ : Site 2) :
    MeasurableSet (bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃) := by
  by_cases h : (v₁ ∈ box 2 n ∧ (hypercubicLattice 2).Adj v₁ u₁) ∧
      (v₂ ∈ box 2 n ∧ (hypercubicLattice 2).Adj v₂ u₂) ∧
      (v₃ ∈ box 2 n ∧ (hypercubicLattice 2).Adj v₃ u₃)
  · have heq : bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃ =
        bins_ExtEvent (bondFinsetTouch 2 n) u₁ u₂ u₃ := by
      ext ω
      simp only [bins_ShellExtEvent, Set.mem_setOf_eq]
      constructor
      · exact fun h' ↦ h'.2.2.2
      · intro h'
        exact ⟨h.1, h.2.1, h.2.2, h'⟩
    rw [heq]
    exact bins_ExtEvent_measurable _ _ _ _
  · have heq : bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃ = ∅ := by
      ext ω
      simp only [bins_ShellExtEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      tauto
    rw [heq]
    exact MeasurableSet.empty



theorem bins_threeMeetBox_subset_iUnion_ShellExtEvent (n : ℕ) :
    threeMeetBox 2 n ⊆
      ⋃ v₁ : Site 2, ⋃ v₂ : Site 2, ⋃ v₃ : Site 2,
      ⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2,
        bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃ := by
  intro ω hω
  obtain ⟨_, x₁, x₂, x₃, hx1, hx2, hx3, hi1, hi2, hi3, hd12, hd13, hd23⟩ := hω
  have inAround {x : Site 2} (hx : x ∈ box 2 n) : x ∈ bc61_boxAround 2 n 0 := by
    rw [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl, mem_boxFinset]
    exact hx
  obtain ⟨u₁, ⟨v₁, hv1, ha1⟩, hu1, hc1⟩ :=
    bc117_attach_of_meetsBox hi1 (inAround hx1) rfl
  obtain ⟨u₂, ⟨v₂, hv2, ha2⟩, hu2, hc2⟩ :=
    bc117_attach_of_meetsBox hi2 (inAround hx2) rfl
  obtain ⟨u₃, ⟨v₃, hv3, ha3⟩, hu3, hc3⟩ :=
    bc117_attach_of_meetsBox hi3 (inAround hx3) rfl
  have hv1' : v₁ ∈ box 2 n := by
    rwa [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl, mem_boxFinset] at hv1
  have hv2' : v₂ ∈ box 2 n := by
    rwa [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl, mem_boxFinset] at hv2
  have hv3' : v₃ ∈ box 2 n := by
    rwa [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl, mem_boxFinset] at hv3
  have hu1' : (cluster 2 (removeSites (boxFinset 2 n) ω) u₁).Infinite := by
    rwa [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl] at hu1
  have hu2' : (cluster 2 (removeSites (boxFinset 2 n) ω) u₂).Infinite := by
    rwa [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl] at hu2
  have hu3' : (cluster 2 (removeSites (boxFinset 2 n) ω) u₃).Infinite := by
    rwa [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl] at hu3
  have hcut12 : cluster 2 (removeSites (boxFinset 2 n) ω) u₁ ≠
      cluster 2 (removeSites (boxFinset 2 n) ω) u₂ := by
    intro h
    have hc : Connected 2 (removeSites (boxFinset 2 n) ω) u₁ u₂ := mem_cluster.mp (by
      rw [h]; exact self_mem_cluster _ u₂)
    have hc' := connected_mono (daep_removeSites_le (boxFinset 2 n) ω) hc
    exact hd12 (by rw [hc1, hc2]; exact cluster_eq_of_connected hc')
  have hcut13 : cluster 2 (removeSites (boxFinset 2 n) ω) u₁ ≠
      cluster 2 (removeSites (boxFinset 2 n) ω) u₃ := by
    intro h
    have hc : Connected 2 (removeSites (boxFinset 2 n) ω) u₁ u₃ := mem_cluster.mp (by
      rw [h]; exact self_mem_cluster _ u₃)
    have hc' := connected_mono (daep_removeSites_le (boxFinset 2 n) ω) hc
    exact hd13 (by rw [hc1, hc3]; exact cluster_eq_of_connected hc')
  have hcut23 : cluster 2 (removeSites (boxFinset 2 n) ω) u₂ ≠
      cluster 2 (removeSites (boxFinset 2 n) ω) u₃ := by
    intro h
    have hc : Connected 2 (removeSites (boxFinset 2 n) ω) u₂ u₃ := mem_cluster.mp (by
      rw [h]; exact self_mem_cluster _ u₃)
    have hc' := connected_mono (daep_removeSites_le (boxFinset 2 n) ω) hc
    exact hd23 (by rw [hc2, hc3]; exact cluster_eq_of_connected hc')
  refine Set.mem_iUnion.mpr ⟨v₁, Set.mem_iUnion.mpr ⟨v₂, Set.mem_iUnion.mpr ⟨v₃,
    Set.mem_iUnion.mpr ⟨u₁, Set.mem_iUnion.mpr ⟨u₂, Set.mem_iUnion.mpr ⟨u₃, ?_⟩⟩⟩⟩⟩⟩
  refine ⟨⟨hv1', ha1.1⟩, ⟨hv2', ha2.1⟩, ⟨hv3', ha3.1⟩, ?_⟩
  change bins_ExtPred u₁ u₂ u₃
    (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω))
  unfold bins_ExtPred
  rw [bins_cluster_closeTouch_eq_removeBox,
    bins_cluster_closeTouch_eq_removeBox, bins_cluster_closeTouch_eq_removeBox]
  exact ⟨⟨hu1', hu2', hu3'⟩, hcut12, hcut13, hcut23⟩


theorem bins_exists_ShellExtEvent_pos (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n)) :
    ∃ v₁ v₂ v₃ u₁ u₂ u₃ : Site 2,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃) := by
  let μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hu : μ (⋃ v₁ : Site 2, ⋃ v₂ : Site 2, ⋃ v₃ : Site 2,
      ⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2,
      bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃) = 0 := by
    refine measure_iUnion_null fun v₁ ↦ measure_iUnion_null fun v₂ ↦
      measure_iUnion_null fun v₃ ↦ measure_iUnion_null fun u₁ ↦
      measure_iUnion_null fun u₂ ↦ measure_iUnion_null fun u₃ ↦ ?_
    exact hcon v₁ v₂ v₃ u₁ u₂ u₃
  have hz : μ (threeMeetBox 2 n) = 0 := le_antisymm
    ((measure_mono (bins_threeMeetBox_subset_iUnion_ShellExtEvent n)).trans_eq hu) bot_le
  apply (ne_of_gt hpos)
  simpa [μ] using hz







def bins_NineMeetBox (n : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | numInfiniteClusters 2 ω = ⊤ ∧ ∃ x : Fin 9 → Site 2,
    (∀ i, x i ∈ box 2 n ∧ (cluster 2 ω (x i)).Infinite) ∧
    ∀ i j, i ≠ j → cluster 2 ω (x i) ≠ cluster 2 ω (x j)}


theorem bins_iEqTop_subset_iUnion_NineMeetBox :
    {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤}
      ⊆ ⋃ n, bins_NineMeetBox n := by
  intro ω htop
  have hInf : (infiniteClusters 2 ω).Infinite :=
    Set.encard_eq_top_iff.mp htop
  let emb : ℕ ↪ (infiniteClusters 2 ω) :=
    @Infinite.natEmbedding (infiniteClusters 2 ω) (Set.Infinite.to_subtype hInf)
  let C : Fin 9 → Set (Site 2) := fun i ↦ (emb i.val).1
  have hCmem (i : Fin 9) : C i ∈ infiniteClusters 2 ω := (emb i.val).2
  have hC (i : Fin 9) : (C i).Infinite ∧ ∃ x, C i = cluster 2 ω x := by
    simpa [infiniteClusters] using hCmem i
  let x : Fin 9 → Site 2 := fun i ↦ Classical.choose (hC i).2
  have hxC (i : Fin 9) : C i = cluster 2 ω (x i) := Classical.choose_spec (hC i).2
  obtain ⟨n, hn⟩ := Lattice.finite_subset_box (Set.range x) (Set.finite_range x)
  refine Set.mem_iUnion.mpr ⟨n, htop, x, ?_, ?_⟩
  · intro i
    refine ⟨hn ⟨i, rfl⟩, ?_⟩
    rw [← hxC i]
    exact (hC i).1
  · intro i j hij heq
    have hCeq : C i = C j := by rw [hxC i, hxC j, heq]
    have hemb : emb i.val = emb j.val := Subtype.ext hCeq
    have hijval : i.val = j.val := emb.injective hemb
    exact hij (Fin.ext hijval)


theorem bins_exists_NineMeetBox_pos (p : ℝ≥0) (hp1 : p ≤ 1)
    (htop : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω | numInfiniteClusters 2 ω = ⊤}) :
    ∃ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (bins_NineMeetBox n) := by
  let μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hu : μ (⋃ n, bins_NineMeetBox n) = 0 := measure_iUnion_null hcon
  have hz : μ {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} = 0 :=
    le_antisymm ((measure_mono bins_iEqTop_subset_iUnion_NineMeetBox).trans_eq hu) bot_le
  apply (ne_of_gt htop)
  simpa [μ] using hz


def bins_NineShellEvent (n : ℕ) (v u : Fin 9 → Site 2) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | (∀ i, v i ∈ box 2 n ∧ (hypercubicLattice 2).Adj (v i) (u i)) ∧
    (∀ i, (cluster 2
      (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω)) (u i)).Infinite) ∧
    ∀ i j, i ≠ j →
      cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω)) (u i) ≠
      cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω)) (u j)}


theorem bins_NineMeetBox_subset_iUnion_NineShellEvent (n : ℕ) :
    bins_NineMeetBox n ⊆
      ⋃ v : Fin 9 → Site 2, ⋃ u : Fin 9 → Site 2, bins_NineShellEvent n v u := by
  intro ω hω
  obtain ⟨_, x, hx, hdist⟩ := hω
  have inAround (i : Fin 9) : x i ∈ bc61_boxAround 2 n 0 := by
    rw [bc61_boxAround_zero, show boxFinsetBK 2 n = boxFinset 2 n by rfl, mem_boxFinset]
    exact (hx i).1
  have hatt (i : Fin 9) : ∃ a : Site 2,
      (∃ b ∈ bc61_boxAround 2 n 0, (openSubgraph 2 ω).Adj b a) ∧
      (cluster 2 (removeSites (bc61_boxAround 2 n 0) ω) a).Infinite ∧
      cluster 2 ω (x i) = cluster 2 ω a :=
    bc117_attach_of_meetsBox (hx i).2 (inAround i) rfl
  let u : Fin 9 → Site 2 := fun i ↦ Classical.choose (hatt i)
  have hu (i : Fin 9) := Classical.choose_spec (hatt i)
  let v : Fin 9 → Site 2 := fun i ↦ Classical.choose (hu i).1
  have hv (i : Fin 9) := Classical.choose_spec (hu i).1
  have hvbox (i : Fin 9) : v i ∈ box 2 n := by
    exact bc61_mem_boxAround_zero.mp (hv i).1
  have huinf (i : Fin 9) :
      (cluster 2 (removeSites (boxFinset 2 n) ω) (u i)).Infinite := by
    change (cluster 2 (removeSites (boxFinset 2 n) ω)
      (Classical.choose (hatt i))).Infinite
    have hT : bc61_boxAround 2 n 0 = boxFinset 2 n := by
      rw [bc61_boxAround_zero]
      rfl
    simpa only [hT] using (hu i).2.1
  have hcut (i j : Fin 9) (hij : i ≠ j) :
      cluster 2 (removeSites (boxFinset 2 n) ω) (u i) ≠
      cluster 2 (removeSites (boxFinset 2 n) ω) (u j) := by
    intro h
    have hc : Connected 2 (removeSites (boxFinset 2 n) ω) (u i) (u j) := mem_cluster.mp (by
      rw [h]
      exact self_mem_cluster _ (u j))
    have hc' : Connected 2 ω (u i) (u j) :=
      connected_mono (daep_removeSites_le (boxFinset 2 n) ω) hc
    apply hdist i j hij
    rw [(hu i).2.2, (hu j).2.2]
    exact cluster_eq_of_connected hc'
  refine Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨u, ?_⟩⟩
  refine ⟨fun i ↦ ⟨hvbox i, (hv i).2.1⟩, ?_, ?_⟩
  · intro i
    rw [bins_cluster_closeTouch_eq_removeBox]
    exact huinf i
  · intro i j hij
    rw [bins_cluster_closeTouch_eq_removeBox, bins_cluster_closeTouch_eq_removeBox]
    exact hcut i j hij


theorem bins_exists_NineShellEvent_pos (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (bins_NineMeetBox n)) :
    ∃ (v u : Fin 9 → Site 2),
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (bins_NineShellEvent n v u) := by
  let μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hu : μ (⋃ v : Fin 9 → Site 2, ⋃ u : Fin 9 → Site 2,
      bins_NineShellEvent n v u) = 0 := by
    refine measure_iUnion_null fun v ↦ measure_iUnion_null fun u ↦ hcon v u
  have hz : μ (bins_NineMeetBox n) = 0 := le_antisymm
    ((measure_mono (bins_NineMeetBox_subset_iUnion_NineShellEvent n)).trans_eq hu) bot_le
  apply (ne_of_gt hpos)
  simpa [μ] using hz



theorem bins_exists_NineShellEvent_pos_of_threeMeetBox
    (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (threeMeetBox 2 n)) :
    ∃ (m : ℕ) (v u : Fin 9 → Site 2),
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (bins_NineShellEvent m v u) := by
  have htop : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} :=
    lt_of_lt_of_le hpos (measure_mono (fun _ h ↦ h.1))
  obtain ⟨m, hm⟩ := bins_exists_NineMeetBox_pos p hp1 htop
  obtain ⟨v, u, hvu⟩ := bins_exists_NineShellEvent_pos p hp1 m hm
  exact ⟨m, v, u, hvu⟩


def bins_outSide (n : ℕ) (u : Site 2) : Fin 4 :=
  if u 0 = (n : ℤ) + 1 then 0
  else if u 0 = -((n : ℤ) + 1) then 1
  else if u 1 = (n : ℤ) + 1 then 2
  else 3



theorem bins_outside_neighbor_side {n : ℕ} {v u : Site 2}
    (hv : v ∈ box 2 n) (hadj : (hypercubicLattice 2).Adj v u) (hu : u ∉ box 2 n) :
    u 0 = (n : ℤ) + 1 ∨ u 0 = -((n : ℤ) + 1) ∨
      u 1 = (n : ℤ) + 1 ∨ u 1 = -((n : ℤ) + 1) := by
  rw [mem_box] at hv hu
  simp only [not_forall, not_le] at hu
  obtain ⟨q, hq⟩ := hu
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have hv0 := hv 0
  have hv1 := hv 1
  fin_cases q
  · change n < (u 0).natAbs at hq
    by_cases hsign : 0 ≤ u 0
    · have hq' : (n : ℤ) < (u 0).natAbs := by exact_mod_cast hq
      rw [Int.natAbs_of_nonneg hsign] at hq'
      left
      omega
    · have hq' : (n : ℤ) < (u 0).natAbs := by exact_mod_cast hq
      rw [Int.ofNat_natAbs_of_nonpos (by omega)] at hq'
      right; left
      omega
  · change n < (u 1).natAbs at hq
    by_cases hsign : 0 ≤ u 1
    · have hq' : (n : ℤ) < (u 1).natAbs := by exact_mod_cast hq
      rw [Int.natAbs_of_nonneg hsign] at hq'
      right; right; left
      omega
    · have hq' : (n : ℤ) < (u 1).natAbs := by exact_mod_cast hq
      rw [Int.ofNat_natAbs_of_nonpos (by omega)] at hq'
      right; right; right
      omega


theorem bins_v_coord_of_outSide {n : ℕ} {v u : Site 2}
    (hv : v ∈ box 2 n) (hadj : (hypercubicLattice 2).Adj v u) (hu : u ∉ box 2 n) :
    (bins_outSide n u = 0 → v 0 = (n : ℤ)) ∧
    (bins_outSide n u = 1 → v 0 = -(n : ℤ)) ∧
    (bins_outSide n u = 2 → v 1 = (n : ℤ)) ∧
    (bins_outSide n u = 3 → v 1 = -(n : ℤ)) := by
  have hs := bins_outside_neighbor_side hv hadj hu
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  unfold bins_outSide
  split_ifs with hR hL hT <;> simp_all <;> omega



theorem bins_u_coord_of_outSide {n : ℕ} {v u : Site 2}
    (hv : v ∈ box 2 n) (hadj : (hypercubicLattice 2).Adj v u) (hu : u ∉ box 2 n) :
    (bins_outSide n u = 0 → u 0 = (n : ℤ) + 1 ∧ u 1 = v 1) ∧
    (bins_outSide n u = 1 → u 0 = -((n : ℤ) + 1) ∧ u 1 = v 1) ∧
    (bins_outSide n u = 2 → u 0 = v 0 ∧ u 1 = (n : ℤ) + 1) ∧
    (bins_outSide n u = 3 → u 0 = v 0 ∧ u 1 = -((n : ℤ) + 1)) := by
  have hs := bins_outside_neighbor_side hv hadj hu
  have hc := bins_v_coord_of_outSide hv hadj hu
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  unfold bins_outSide at hc ⊢
  split_ifs with hR hL hT <;> simp_all <;> omega



theorem bins_NineShellEvent_three_same_side {n : ℕ} {v u : Fin 9 → Site 2}
    {ω : ConfigSpace (Sym2 (Site 2))} (hE : ω ∈ bins_NineShellEvent n v u) :
    ∃ i j k : Fin 9, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      v i ≠ v j ∧ v i ≠ v k ∧ v j ≠ v k ∧
      ((v i 0 = (n : ℤ) ∧ v j 0 = (n : ℤ) ∧ v k 0 = (n : ℤ)) ∨
       (v i 0 = -(n : ℤ) ∧ v j 0 = -(n : ℤ) ∧ v k 0 = -(n : ℤ)) ∨
       (v i 1 = (n : ℤ) ∧ v j 1 = (n : ℤ) ∧ v k 1 = (n : ℤ)) ∨
       (v i 1 = -(n : ℤ) ∧ v j 1 = -(n : ℤ) ∧ v k 1 = -(n : ℤ))) := by
  obtain ⟨hgeom, hinf, hdist⟩ := hE
  have huout (i : Fin 9) : u i ∉ box 2 n := by
    have hi : (cluster 2 (removeSites (boxFinset 2 n) ω) (u i)).Infinite := by
      rw [← bins_cluster_closeTouch_eq_removeBox]
      exact hinf i
    exact fun h ↦ stac_infiniteCluster_notMem (boxFinset 2 n) ω hi (mem_boxFinset.mpr h)
  let side : Fin 9 → Fin 4 := fun i ↦ bins_outSide n (u i)
  obtain ⟨s, hs⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := side) (n := 2) (by decide)
  let F := Finset.univ.filter (fun i ↦ side i = s)
  have hF : 2 < F.card := by simpa [F] using hs
  obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ F.card by omega)
  obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp htcard
  have hiF : i ∈ F := ht (by simp)
  have hjF : j ∈ F := ht (by simp)
  have hkF : k ∈ F := ht (by simp)
  have hi : side i = s := by simpa [F] using hiF
  have hj : side j = s := by simpa [F] using hjF
  have hk : side k = s := by simpa [F] using hkF
  have huij : u i ≠ u j := by
    intro h
    exact hdist i j hij (by rw [h])
  have huik : u i ≠ u k := by
    intro h
    exact hdist i k hik (by rw [h])
  have hujk : u j ≠ u k := by
    intro h
    exact hdist j k hjk (by rw [h])
  have vinj : ∀ {a b : Fin 9}, side a = side b → u a ≠ u b → v a ≠ v b := by
    intro a b hab huab hvab
    apply huab
    have ha := bins_u_coord_of_outSide (hgeom a).1 (hgeom a).2 (huout a)
    have hb := bins_u_coord_of_outSide (hgeom b).1 (hgeom b).2 (huout b)
    have hab' : bins_outSide n (u a) = bins_outSide n (u b) := by simpa [side] using hab
    generalize hsa : bins_outSide n (u a) = sa
    fin_cases sa
    · have hsb : bins_outSide n (u b) = 0 := hab'.symm.trans hsa
      have ha0 := ha.1 hsa
      have hb0 := hb.1 hsb
      ext q
      fin_cases q
      · change u a 0 = u b 0
        rw [ha0.1, hb0.1]
      · change u a 1 = u b 1
        rw [ha0.2, hb0.2, congrFun hvab 1]
    · have hsb : bins_outSide n (u b) = 1 := hab'.symm.trans hsa
      have ha1 := ha.2.1 hsa
      have hb1 := hb.2.1 hsb
      ext q
      fin_cases q
      · change u a 0 = u b 0
        rw [ha1.1, hb1.1]
      · change u a 1 = u b 1
        rw [ha1.2, hb1.2, congrFun hvab 1]
    · have hsb : bins_outSide n (u b) = 2 := hab'.symm.trans hsa
      have ha2 := ha.2.2.1 hsa
      have hb2 := hb.2.2.1 hsb
      ext q
      fin_cases q
      · change u a 0 = u b 0
        rw [ha2.1, hb2.1, congrFun hvab 0]
      · change u a 1 = u b 1
        rw [ha2.2, hb2.2]
    · have hsb : bins_outSide n (u b) = 3 := hab'.symm.trans hsa
      have ha3 := ha.2.2.2 hsa
      have hb3 := hb.2.2.2 hsb
      ext q
      fin_cases q
      · change u a 0 = u b 0
        rw [ha3.1, hb3.1, congrFun hvab 0]
      · change u a 1 = u b 1
        rw [ha3.2, hb3.2]
  have hvij : v i ≠ v j := vinj (hi.trans hj.symm) huij
  have hvik : v i ≠ v k := vinj (hi.trans hk.symm) huik
  have hvjk : v j ≠ v k := vinj (hj.trans hk.symm) hujk
  refine ⟨i, j, k, hij, hik, hjk, hvij, hvik, hvjk, ?_⟩
  have hci := bins_v_coord_of_outSide (hgeom i).1 (hgeom i).2 (huout i)
  have hcj := bins_v_coord_of_outSide (hgeom j).1 (hgeom j).2 (huout j)
  have hck := bins_v_coord_of_outSide (hgeom k).1 (hgeom k).2 (huout k)
  fin_cases s
  · left
    exact ⟨hci.1 (by simpa [side] using hi), hcj.1 (by simpa [side] using hj),
      hck.1 (by simpa [side] using hk)⟩
  · right; left
    exact ⟨hci.2.1 (by simpa [side] using hi), hcj.2.1 (by simpa [side] using hj),
      hck.2.1 (by simpa [side] using hk)⟩
  · right; right; left
    exact ⟨hci.2.2.1 (by simpa [side] using hi),
      hcj.2.2.1 (by simpa [side] using hj), hck.2.2.1 (by simpa [side] using hk)⟩
  · right; right; right
    exact ⟨hci.2.2.2 (by simpa [side] using hi),
      hcj.2.2.2 (by simpa [side] using hj), hck.2.2.2 (by simpa [side] using hk)⟩





theorem bins_routePackage_of_corridors (p : ℝ≥0) (hp1 : p ≤ 1) (m : ℕ)
    (u₁ u₂ u₃ : Site 2) (I : Finset (Sym2 (Site 2)))
    (hu₁ : u₁ ≠ ![0, 0]) (hu₂ : u₂ ≠ ![0, 0]) (hu₃ : u₃ ≠ ![0, 0])
    (hC : bcor_Corridors m u₁ u₂ u₃)
    (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (bins_ExtEvent I u₁ u₂ u₃))
    (hpattern : ∀ a₁ a₂ a₃ : Site 2,
      ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
        (hypercubicLattice 2).Adj 0 a₃) →
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) →
      ∃ η₀ : ConfigSpace ↥I,
        cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ bins_ExtEvent I u₁ u₂ u₃
          ⊆ NeighborTrifPrecursor 2 a₁ a₂ a₃) :
    ∃ (η₀ : ConfigSpace ↥I) (a₁ a₂ a₃ : Site 2)
      (X : Set (ConfigSpace (Sym2 (Site 2)))),
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
        (hypercubicLattice 2).Adj 0 a₃) ∧
      MeasurableSet X ∧ DependsOn X ((↑I : Set (Sym2 (Site 2)))ᶜ) ∧
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 X ∧
      cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ X
        ⊆ NeighborTrifPrecursor 2 a₁ a₂ a₃ := by
  obtain ⟨a₁, a₂, a₃, hadj, hne⟩ := bcor_firstSteps m hu₁ hu₂ hu₃ hC
  obtain ⟨η₀, hgeo⟩ := hpattern a₁ a₂ a₃ hadj hne
  exact ⟨η₀, a₁, a₂, a₃, bins_ExtEvent I u₁ u₂ u₃,
    hne, hadj, bins_ExtEvent_measurable I u₁ u₂ u₃,
    bins_ExtEvent_dependsOn I u₁ u₂ u₃, hXpos, hgeo⟩
















def bins_Route (p : ℝ≥0) (hp1 : p ≤ 1) : Prop :=
  ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) →
    ∃ (I : Finset (Sym2 (Site 2))) (η₀ : ConfigSpace ↥I) (a₁ a₂ a₃ : Site 2)
      (X : Set (ConfigSpace (Sym2 (Site 2)))),
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
        (hypercubicLattice 2).Adj 0 a₃) ∧
      MeasurableSet X ∧ DependsOn X ((↑I : Set (Sym2 (Site 2)))ᶜ) ∧
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 X ∧
      cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ X ⊆ NeighborTrifPrecursor 2 a₁ a₂ a₃






theorem bins_hroute_of_route (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hres : bins_Route p hp1) :
    ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) →
      ∃ a₁ a₂ a₃ : Site 2,
        0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
  intro n hn
  obtain ⟨I, η₀, a₁, a₂, a₃, X, hne, hadj, hXmeas, hXdep, hXpos, hgeo⟩ := hres n hn
  refine ⟨a₁, a₂, a₃, ?_⟩
  have hindep := bfc2_indep_finite_cofinite p hp1 I
    (bcl_cylinder_measurable I η₀) hXmeas (bcl_cylinder_dependsOn I η₀) hXdep
  exact bdec_precursorPos_of_decoupled p hp1 hp0 hplt a₁ a₂ a₃ I η₀ X hindep hXpos hgeo





theorem bins_bk (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hres : bins_Route p hp1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          {ω | numInfiniteClusters 2 ω ≤ 1} = 1 :=
  bfx_bk_of_route (by norm_num) p hp1 hp0 (bins_hroute_of_route p hp1 hp0 hplt hres)



theorem bins_bk_atLeastTwo (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hres : bins_Route p hp1) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  (bins_bk p hp1 hp0 hplt hres).2.1

end StatMech.Walls
