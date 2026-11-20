/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationCycleExponent










namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising

theorem ons_finsuppAntidiag_finsetExponent_le
    {I E : Type*} [DecidableEq I] [DecidableEq E]
    (T : Finset I) (S : Finset E) (g : I →₀ E →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i : I} (hi : i ∈ T) (edge : E) :
    g i edge ≤ if edge ∈ S then 1 else 0 := by
  have hsum := (Finset.mem_finsuppAntidiag.mp hg).1
  have hle : g i edge ≤ (∑ j ∈ T, g j) edge := by
    rw [Finsupp.finsetSum_apply]
    exact Finset.single_le_sum
      (fun j _ ↦ Nat.zero_le (g j edge)) hi
  rw [hsum, ons_finsetExponent_apply] at hle
  exact hle

theorem ons_finsuppAntidiag_finsetExponent_component
    {I E : Type*} [DecidableEq I] [DecidableEq E]
    (T : Finset I) (S : Finset E) (g : I →₀ E →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i : I} (hi : i ∈ T) :
    g i = ons_finsetExponent (g i).support := by
  ext edge
  rw [ons_finsetExponent_apply]
  by_cases hedge : edge ∈ (g i).support
  · rw [if_pos hedge]
    have hpos : 0 < g i edge := Finsupp.mem_support_iff.mp hedge |> Nat.pos_of_ne_zero
    have hle := ons_finsuppAntidiag_finsetExponent_le T S g hg hi edge
    by_cases hedgeS : edge ∈ S
    · rw [if_pos hedgeS] at hle
      omega
    · rw [if_neg hedgeS] at hle
      omega
  · rw [if_neg hedge]
    exact Finsupp.notMem_support_iff.mp hedge

theorem ons_finsuppAntidiag_finsetExponent_support_subset
    {I E : Type*} [DecidableEq I] [DecidableEq E]
    (T : Finset I) (S : Finset E) (g : I →₀ E →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i : I} (hi : i ∈ T) :
    (g i).support ⊆ S := by
  intro edge hedge
  have hle := ons_finsuppAntidiag_finsetExponent_le T S g hg hi edge
  by_contra hedgeS
  rw [if_neg hedgeS] at hle
  have hpos : 0 < g i edge := Finsupp.mem_support_iff.mp hedge |> Nat.pos_of_ne_zero
  omega

theorem ons_finsuppAntidiag_finsetExponent_support_disjoint
    {I E : Type*} [DecidableEq I] [DecidableEq E]
    (T : Finset I) (S : Finset E) (g : I →₀ E →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i j : I} (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j) :
    Disjoint (g i).support (g j).support := by
  rw [Finset.disjoint_left]
  intro edge hei hej
  have hsum := (Finset.mem_finsuppAntidiag.mp hg).1
  have hiOne : g i edge = 1 := by
    rw [ons_finsuppAntidiag_finsetExponent_component T S g hg hi,
      ons_finsetExponent_apply, if_pos hei]
  have hjOne : g j edge = 1 := by
    rw [ons_finsuppAntidiag_finsetExponent_component T S g hg hj,
      ons_finsetExponent_apply, if_pos hej]
  have htwo : 2 ≤ (∑ k ∈ T, g k) edge := by
    rw [Finsupp.finsetSum_apply]
    calc
      2 = g i edge + g j edge := by rw [hiOne, hjOne]
      _ = ∑ k ∈ ({i, j} : Finset I), g k edge := by
        simp [hij]
      _ ≤ ∑ k ∈ T, g k edge :=
        Finset.sum_le_sum_of_subset (by
          intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact hi
          · exact hj)
  rw [hsum, ons_finsetExponent_apply] at htwo
  split at htwo <;> omega

theorem ons_finsuppAntidiag_finsetExponent_support_cover
    {I E : Type*} [DecidableEq I] [DecidableEq E]
    (T : Finset I) (S : Finset E) (g : I →₀ E →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S)) :
    S = T.biUnion (fun i ↦ (g i).support) := by
  apply Finset.ext
  intro edge
  constructor
  · intro hedge
    rw [Finset.mem_biUnion]
    have hsum := congrArg (fun m : E →₀ ℕ ↦ m edge)
      (Finset.mem_finsuppAntidiag.mp hg).1
    have hsum' : ∑ i ∈ T, g i edge = 1 := by
      calc
        (∑ i ∈ T, g i edge) = (∑ i ∈ T, g i) edge :=
          (Finsupp.finsetSum_apply T (fun i ↦ g i) edge).symm
        _ = ons_finsetExponent S edge := hsum
        _ = 1 := by rw [ons_finsetExponent_apply, if_pos hedge]
    by_contra hnone
    push Not at hnone
    have hzero : ∑ i ∈ T, g i edge = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact Finsupp.notMem_support_iff.mp (hnone i hi)
    omega
  · intro hedge
    rw [Finset.mem_biUnion] at hedge
    obtain ⟨i, hi, hedge⟩ := hedge
    exact ons_finsuppAntidiag_finsetExponent_support_subset
      T S g hg hi hedge

theorem ons_decFormalLogCoeff_squarefree_cycle_of_ne_zero
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    (hne : ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)
      (ons_finsetExponent S) ≠ 0) :
    ∃ (root : ons_Dart L)
      (q : (ons_decGraph L).Walk root root),
      q.IsCycle ∧ q.snd = ons_dartRev L root ∧
      q.edges.toFinset = S ∧
      ons_decFormalLogCoeff L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)
          (ons_finsetExponent S) =
        (ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) := by
  rcases ons_decFormalLogCoeff_squarefree_cases L a b S with hzero | hex
  · exact (hne hzero).elim
  · obtain ⟨r, d, hd, hcoeff⟩ := hex
    have hddata := (ons_mem_decSquarefreeLoopFinset L a b S d).mp hd
    let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) d hddata.2
    let q := ons_decLoopWalk L d hvalid
    have hq : q.IsCycle :=
      ons_decLoopWalk_isCycle_of_squarefree L d hvalid S hddata.1
    have hsnd : q.snd = ons_dartRev L (d 0) :=
      ons_decLoopWalk_snd L d hvalid
    have hedges : q.edges.toFinset = S :=
      ons_decLoopWalk_edges_toFinset_of_squarefree
        L d hvalid S hddata.1
    exact ⟨d 0, q, hq, hsnd, hedges, by
      simpa only [q, hvalid] using hcoeff⟩



theorem ons_isCycles_cycle_edges_eq_of_common_vertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcyc : G.IsCycles) {u v : V}
    (p : G.Walk u u) (q : G.Walk v v)
    (hp : p.IsCycle) (hq : q.IsCycle)
    {x : V} (hxp : x ∈ p.toSubgraph.verts)
    (hxq : x ∈ q.toSubgraph.verts) :
    p.edges.toFinset = q.edges.toFinset := by
  have hpclosed : ∀ y ∈ p.toSubgraph.verts, ∀ z,
      G.Adj y z → p.toSubgraph.Adj y z := by
    intro y hy z hyz
    exact (hp.adj_toSubgraph_iff_of_isCycles hcyc hy z).mpr hyz
  have hqclosed : ∀ y ∈ q.toSubgraph.verts, ∀ z,
      G.Adj y z → q.toSubgraph.Adj y z := by
    intro y hy z hyz
    exact (hq.adj_toSubgraph_iff_of_isCycles hcyc hy z).mpr hyz
  obtain ⟨cp, hcp⟩ :=
    p.toSubgraph_connected.exists_verts_eq_connectedComponentSupp hpclosed
  obtain ⟨cq, hcq⟩ :=
    q.toSubgraph_connected.exists_verts_eq_connectedComponentSupp hqclosed
  have hxcp : x ∈ cp.supp := hcp ▸ hxp
  have hxcq : x ∈ cq.supp := hcq ▸ hxq
  have hc : cp = cq := by
    have hpRoot := (cp.mem_supp_iff x).mp hxcp
    have hqRoot := (cq.mem_supp_iff x).mp hxcq
    exact hpRoot.symm.trans hqRoot
  have hverts : p.toSubgraph.verts = q.toSubgraph.verts := by
    rw [hcp, hc, hcq]
  ext edge
  induction edge using Sym2.inductionOn with
  | _ y z =>
      simp only [List.mem_toFinset]
      rw [← p.mem_edges_toSubgraph, ← q.mem_edges_toSubgraph]
      constructor
      · intro hyz
        have hyq : y ∈ q.toSubgraph.verts := hverts ▸ hyz.fst_mem
        exact (hq.adj_toSubgraph_iff_of_isCycles hcyc hyq z).mpr
          hyz.adj_sub
      · intro hyz
        have hyp : y ∈ p.toSubgraph.verts := hverts.symm ▸ hyz.fst_mem
        exact (hp.adj_toSubgraph_iff_of_isCycles hcyc hyp z).mpr
          hyz.adj_sub

theorem ons_cycle_edges_eq_decomposition_piece
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ x, G.degree x ≤ 3)
    (S : Finset (Sym2 V)) (hS : S ∈ evenSubgraphs G)
    {I : Type*} [Fintype I] [DecidableEq I]
    (base : I → V) (p : (i : I) → G.Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i ↦ (p i).edges.toFinset))
    {root : V} (q : G.Walk root root) (hq : q.IsCycle)
    (hqsub : q.edges.toFinset ⊆ S) :
    ∃ i : I, q.edges.toFinset = (p i).edges.toFinset := by
  let H := ons_edgeSubgraph S
  have hdata := hS
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  have hHedges : H.edgeSet = (S : Set (Sym2 V)) := by
    simpa [H] using ons_edgeSubgraph_edgeSet G S hdata.1
  have hHcycles : H.IsCycles := by
    simpa [H] using ons_isCycles_of_trivalent_even G hdeg S hS
  have hqNonempty : q.edges.toFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hedges : q.edges = [] :=
      (List.toFinset_eq_empty_iff q.edges).mp hempty
    exact hq.not_nil (SimpleGraph.Walk.edges_eq_nil.mp hedges)
  obtain ⟨edge, hedgeq⟩ := hqNonempty
  have hedgeS : edge ∈ S := hqsub hedgeq
  rw [hcover, Finset.mem_biUnion] at hedgeS
  obtain ⟨i, _, hedgei⟩ := hedgeS
  let qH : H.Walk root root := q.transfer H (by
    intro e he
    rw [hHedges]
    exact hqsub (List.mem_toFinset.mpr he))
  have hpiSub : (p i).edges.toFinset ⊆ S := by
    intro e he
    rw [hcover, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, he⟩
  let pH : H.Walk (base i) (base i) := (p i).transfer H (by
    intro e he
    rw [hHedges]
    exact hpiSub (List.mem_toFinset.mpr he))
  have hqH : qH.IsCycle := by
    exact hq.transfer _
  have hpH : pH.IsCycle := by
    exact (hp i).transfer _
  obtain ⟨x, y⟩ := edge
  have hedgeqList : s(x, y) ∈ q.edges := List.mem_toFinset.mp hedgeq
  have hedgeiList : s(x, y) ∈ (p i).edges := List.mem_toFinset.mp hedgei
  have hxq : x ∈ qH.toSubgraph.verts := by
    rw [SimpleGraph.Walk.mem_verts_toSubgraph]
    have hx : x ∈ q.support := q.fst_mem_support_of_mem_edges hedgeqList
    simpa [qH, SimpleGraph.Walk.support_transfer] using hx
  have hxp : x ∈ pH.toSubgraph.verts := by
    rw [SimpleGraph.Walk.mem_verts_toSubgraph]
    have hx : x ∈ (p i).support :=
      (p i).fst_mem_support_of_mem_edges hedgeiList
    simpa [pH, SimpleGraph.Walk.support_transfer] using hx
  have heq := ons_isCycles_cycle_edges_eq_of_common_vertex
    hHcycles qH pH hqH hpH hxq hxp
  refine ⟨i, ?_⟩
  calc
    q.edges.toFinset = qH.edges.toFinset := by
      rw [show qH.edges = q.edges from
        SimpleGraph.Walk.edges_transfer q _]
    _ = pH.edges.toFinset := heq
    _ = (p i).edges.toFinset := by
      rw [show pH.edges = (p i).edges from
        SimpleGraph.Walk.edges_transfer (p i) _]

theorem ons_decFormalLogCoeff_antidiag_component
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    (hS : S ∈ evenSubgraphs (ons_decGraph L))
    {I : Type*} [Fintype I] [DecidableEq I]
    (base : I → ons_Dart L)
    (p : (i : I) → (ons_decGraph L).Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i ↦ (p i).edges.toFinset))
    {K : Type*} [DecidableEq K] (T : Finset K)
    (g : K →₀ ons_DecEdge L →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i : K} (hi : i ∈ T)
    (hne : ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) (g i) ≠ 0) :
    ∃ j : I,
      (g i).support = (p j).edges.toFinset ∧
      ons_decFormalLogCoeff L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) (g i) =
        (ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges (p j))) : ℂ) := by
  have hcomponent :=
    ons_finsuppAntidiag_finsetExponent_component T S g hg hi
  have hcoeffEq : ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) (g i) =
      ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_finsetExponent (g i).support) :=
    congrArg (ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)) hcomponent
  have hne' : ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)
      (ons_finsetExponent (g i).support) ≠ 0 := by
    intro hzero
    exact hne (hcoeffEq.trans hzero)
  obtain ⟨root, q, hq, hsnd, hqedges, hqcoeff⟩ :=
    ons_decFormalLogCoeff_squarefree_cycle_of_ne_zero
      L a b (g i).support hne'
  have hqsub : q.edges.toFinset ⊆ S := by
    rw [hqedges]
    exact ons_finsuppAntidiag_finsetExponent_support_subset
      T S g hg hi
  obtain ⟨j, hjedges⟩ := ons_cycle_edges_eq_decomposition_piece
    (ons_decGraph L) (ons_decGraph_degree_le_three L)
    S hS base p hp hcover q hq hqsub
  have hsupport : (g i).support = (p j).edges.toFinset := by
    rw [← hqedges, hjedges]
  have horiginal : ons_walkOriginalEdges q =
      ons_walkOriginalEdges (p j) :=
    ons_walkOriginalEdges_eq_of_edges_toFinset_eq q (p j) hjedges
  refine ⟨j, hsupport, ?_⟩
  calc
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) (g i) =
        ons_decFormalLogCoeff L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)
          (ons_finsetExponent (g i).support) := hcoeffEq
    _ = (ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) := hqcoeff
    _ = (ons_spinCharacter a b
          (ons_evenHomology L
            (ons_walkOriginalEdges (p j))) : ℂ) := by rw [horiginal]

theorem ons_cycle_edges_toFinset_nonempty
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    p.edges.toFinset.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hedges : p.edges = [] :=
    (List.toFinset_eq_empty_iff p.edges).mp hempty
  exact hp.not_nil (SimpleGraph.Walk.edges_eq_nil.mp hedges)

theorem ons_cycle_decomposition_edgeSet_injective
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} (base : I → V)
    (p : (i : I) → G.Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle)
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ (p i).edges.toFinset)) :
    Function.Injective (fun i ↦ (p i).edges.toFinset) := by
  intro i j hij
  change (p i).edges.toFinset = (p j).edges.toFinset at hij
  by_contra hne
  have hd := hdisj (Finset.mem_univ i) (Finset.mem_univ j) hne
  change Disjoint (p i).edges.toFinset (p j).edges.toFinset at hd
  rw [hij] at hd
  have hempty : (p j).edges.toFinset = ∅ := disjoint_self.mp hd
  exact (ons_cycle_edges_toFinset_nonempty (p j) (hp j)).ne_empty hempty

noncomputable def ons_decComponentSeries
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {I : Type*} [Fintype I]
    (base : I → ons_Dart L)
    (p : (i : I) → (ons_decGraph L).Walk (base i) (base i)) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  ∑ i : I, MvPowerSeries.monomial
    (ons_finsetExponent (p i).edges.toFinset)
    (ons_spinCharacter a b
      (ons_evenHomology L (ons_walkOriginalEdges (p i))) : ℂ)

theorem ons_decComponentSeries_coeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {I : Type*} [Fintype I]
    (base : I → ons_Dart L)
    (p : (i : I) → (ons_decGraph L).Walk (base i) (base i))
    (m : ons_DecEdge L →₀ ℕ) :
    MvPowerSeries.coeff m (ons_decComponentSeries L a b base p) =
      ∑ i : I, if ons_finsetExponent (p i).edges.toFinset = m then
        (ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges (p i))) : ℂ)
      else 0 := by
  classical
  unfold ons_decComponentSeries
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MvPowerSeries.coeff_monomial]
  by_cases heq : ons_finsetExponent (p i).edges.toFinset = m
  · rw [if_pos heq.symm, if_pos heq]
  · rw [if_neg (Ne.symm heq), if_neg heq]

theorem ons_decComponentSeries_coeff_piece
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {I : Type*} [Fintype I] [DecidableEq I]
    (base : I → ons_Dart L)
    (p : (i : I) → (ons_decGraph L).Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle)
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ (p i).edges.toFinset)) (j : I) :
    MvPowerSeries.coeff (ons_finsetExponent (p j).edges.toFinset)
        (ons_decComponentSeries L a b base p) =
      (ons_spinCharacter a b
        (ons_evenHomology L (ons_walkOriginalEdges (p j))) : ℂ) := by
  classical
  rw [ons_decComponentSeries_coeff]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro i hij
    rw [if_neg]
    intro heq
    apply hij
    apply ons_cycle_decomposition_edgeSet_injective base p hp hdisj
    exact ons_finsetExponent_injective heq

theorem ons_decFormalLog_coeff_eq_componentSeries_of_antidiag
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    (hS : S ∈ evenSubgraphs (ons_decGraph L))
    {I : Type*} [Fintype I] [DecidableEq I]
    (base : I → ons_Dart L)
    (p : (i : I) → (ons_decGraph L).Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i ↦ (p i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ (p i).edges.toFinset))
    {K : Type*} [DecidableEq K] (T : Finset K)
    (g : K →₀ ons_DecEdge L →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i : K} (hi : i ∈ T) :
    MvPowerSeries.coeff (g i)
        (ons_decFormalLog L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) =
      MvPowerSeries.coeff (g i)
        (ons_decComponentSeries L a b base p) := by
  change ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) (g i) = _
  have hcomponent :=
    ons_finsuppAntidiag_finsetExponent_component T S g hg hi
  by_cases hexists : ∃ j : I,
      (g i).support = (p j).edges.toFinset
  · obtain ⟨j, hj⟩ := hexists
    have hgi : g i = ons_finsetExponent (p j).edges.toFinset := by
      calc
        g i = ons_finsetExponent (g i).support := hcomponent
        _ = ons_finsetExponent (p j).edges.toFinset := congrArg _ hj
    rw [hgi, ons_decFormalLogCoeff_unrooted_cycle (p j) (hp j) a b]
    exact (ons_decComponentSeries_coeff_piece
      L a b base p hp hdisj j).symm
  · have hleft : ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) (g i) = 0 := by
      by_contra hne
      obtain ⟨j, hj, _⟩ := ons_decFormalLogCoeff_antidiag_component
        L a b S hS base p hp hcover T g hg hi hne
      exact hexists ⟨j, hj⟩
    have hright : MvPowerSeries.coeff (g i)
        (ons_decComponentSeries L a b base p) = 0 := by
      rw [ons_decComponentSeries_coeff]
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg]
      intro heq
      apply hexists
      refine ⟨j, ?_⟩
      apply ons_finsetExponent_injective
      calc
        ons_finsetExponent (g i).support = g i := hcomponent.symm
        _ = ons_finsetExponent (p j).edges.toFinset := heq.symm
    rw [hleft, hright]

theorem ons_decFormalLog_pow_coeff_eq_componentSeries
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    (hS : S ∈ evenSubgraphs (ons_decGraph L))
    {I : Type*} [Fintype I] [DecidableEq I]
    (base : I → ons_Dart L)
    (p : (i : I) → (ons_decGraph L).Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i ↦ (p i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ (p i).edges.toFinset))
    (n : ℕ) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        ((ons_decFormalLog L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) ^ n) =
      MvPowerSeries.coeff (ons_finsetExponent S)
        ((ons_decComponentSeries L a b base p) ^ n) := by
  classical
  rw [MvPowerSeries.coeff_pow, MvPowerSeries.coeff_pow]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  exact ons_decFormalLog_coeff_eq_componentSeries_of_antidiag
    L a b S hS base p hp hcover hdisj (Finset.range n) g hg hi

theorem ons_finsetExponent_biUnion_eq_sum
    {E I : Type*} [DecidableEq E] [Fintype I] [DecidableEq I]
    (S : Finset E) (piece : I → Finset E)
    (hcover : S = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint piece) :
    ons_finsetExponent S = ∑ i, ons_finsetExponent (piece i) := by
  classical
  rw [hcover]
  unfold ons_finsetExponent
  rw [Finset.sum_biUnion hdisj]

theorem ons_sum_finsetExponent_eq_iff_bijective
    {E I : Type*} [DecidableEq E] [Fintype I] [DecidableEq I]
    (S : Finset E) (piece : I → Finset E)
    (hcover : S = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint piece)
    (hnonempty : ∀ i, (piece i).Nonempty) (n : ℕ) (f : Fin n → I) :
    (∑ k, ons_finsetExponent (piece (f k))) = ons_finsetExponent S ↔
      Function.Bijective f := by
  classical
  constructor
  · intro hsum
    constructor
    · intro x y hxy
      by_contra hne
      obtain ⟨edge, hedge⟩ := hnonempty (f x)
      have hedgeS : edge ∈ S := by
        rw [hcover, Finset.mem_biUnion]
        exact ⟨f x, Finset.mem_univ _, hedge⟩
      have hxOne : ons_finsetExponent (piece (f x)) edge = 1 := by
        rw [ons_finsetExponent_apply, if_pos hedge]
      have hyMem : edge ∈ piece (f y) := hxy ▸ hedge
      have hyOne : ons_finsetExponent (piece (f y)) edge = 1 := by
        rw [ons_finsetExponent_apply, if_pos hyMem]
      have htwo : 2 ≤ ∑ k, ons_finsetExponent (piece (f k)) edge := by
        calc
          2 = ons_finsetExponent (piece (f x)) edge +
              ons_finsetExponent (piece (f y)) edge := by rw [hxOne, hyOne]
          _ = ∑ k ∈ ({x, y} : Finset (Fin n)),
              ons_finsetExponent (piece (f k)) edge := by
            rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
          _ ≤ ∑ k, ons_finsetExponent (piece (f k)) edge :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have hsumEval := congrArg (fun m : E →₀ ℕ ↦ m edge) hsum
      simp only [Finsupp.finsetSum_apply] at hsumEval
      rw [hsumEval, ons_finsetExponent_apply, if_pos hedgeS] at htwo
      omega
    · intro j
      by_contra hj
      have hmiss : ∀ k, f k ≠ j := by
        intro k hkj
        exact hj ⟨k, hkj⟩
      obtain ⟨edge, hedge⟩ := hnonempty j
      have hedgeS : edge ∈ S := by
        rw [hcover, Finset.mem_biUnion]
        exact ⟨j, Finset.mem_univ _, hedge⟩
      have hzero : ∑ k, ons_finsetExponent (piece (f k)) edge = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [ons_finsetExponent_apply, if_neg]
        intro hedgeFk
        exact (Finset.disjoint_left.mp
          (hdisj (Finset.mem_univ _) (Finset.mem_univ _) (hmiss k)))
          hedgeFk hedge
      have hsumEval := congrArg (fun m : E →₀ ℕ ↦ m edge) hsum
      simp only [Finsupp.finsetSum_apply] at hsumEval
      rw [hzero, ons_finsetExponent_apply, if_pos hedgeS] at hsumEval
      omega
  · intro hf
    calc
      (∑ k, ons_finsetExponent (piece (f k))) =
          ∑ i, ons_finsetExponent (piece i) :=
        hf.sum_comp (fun i ↦ ons_finsetExponent (piece i))
      _ = ons_finsetExponent S :=
        (ons_finsetExponent_biUnion_eq_sum S piece hcover hdisj).symm

theorem ons_decComponentSeries_pow_coeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    {I : Type*} [Fintype I] [DecidableEq I]
    (base : I → ons_Dart L)
    (p : (i : I) → (ons_decGraph L).Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i ↦ (p i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ (p i).edges.toFinset)) (n : ℕ) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        ((ons_decComponentSeries L a b base p) ^ n) =
      if n = Fintype.card I then
        (n.factorial : ℂ) *
          ∏ i, (ons_spinCharacter a b
            (ons_evenHomology L (ons_walkOriginalEdges (p i))) : ℂ)
      else 0 := by
  classical
  let exponent : I → ons_DecEdge L →₀ ℕ :=
    fun i ↦ ons_finsetExponent (p i).edges.toFinset
  let character : I → ℂ := fun i ↦
    (ons_spinCharacter a b
      (ons_evenHomology L (ons_walkOriginalEdges (p i))) : ℂ)
  have hnonempty : ∀ i, ((p i).edges.toFinset).Nonempty :=
    fun i ↦ ons_cycle_edges_toFinset_nonempty (p i) (hp i)
  have hexponent (f : Fin n → I) :
      (∑ k, exponent (f k)) = ons_finsetExponent S ↔
        Function.Bijective f := by
    exact ons_sum_finsetExponent_eq_iff_bijective S
      (fun i ↦ (p i).edges.toFinset) hcover hdisj hnonempty n f
  have hprod (f : Fin n → I) :
      (∏ k, MvPowerSeries.monomial (exponent (f k)) (character (f k))) =
        MvPowerSeries.monomial (∑ k, exponent (f k))
          (∏ k, character (f k)) := by
    simpa using MvPowerSeries.prod_monomial
      (fun k ↦ exponent (f k)) (fun k ↦ character (f k)) Finset.univ
  have hsumForm :
      MvPowerSeries.coeff (ons_finsetExponent S)
          ((ons_decComponentSeries L a b base p) ^ n) =
        ∑ f : Fin n → I,
          if Function.Bijective f then ∏ k, character (f k) else 0 := by
    unfold ons_decComponentSeries
    change MvPowerSeries.coeff (ons_finsetExponent S)
      ((∑ i, MvPowerSeries.monomial (exponent i) (character i)) ^ n) = _
    rw [Fintype.sum_pow, map_sum]
    apply Finset.sum_congr rfl
    intro f hf
    rw [hprod, MvPowerSeries.coeff_monomial]
    rw [if_congr (by simpa only [eq_comm] using hexponent f) rfl rfl]
  rw [hsumForm]
  by_cases hn : n = Fintype.card I
  · rw [if_pos hn, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hcardEq : Fintype.card (Fin n) = Fintype.card I := by
      simpa using hn
    let e : Fin n ≃ I := Fintype.equivOfCardEq hcardEq
    have hcardBij :
        Fintype.card {f : Fin n → I // Function.Bijective f} =
          n.factorial := by
      calc
        Fintype.card {f : Fin n → I // Function.Bijective f} =
            Fintype.card (Fin n ≃ I) :=
          Fintype.card_congr Equiv.bijectiveEquiv
        _ = (Fintype.card (Fin n)).factorial := Fintype.card_equiv e
        _ = n.factorial := by simp
    have hcardFilter :
        #{f : Fin n → I | Function.Bijective f} = n.factorial := by
      rw [← Fintype.card_subtype]
      exact hcardBij
    calc
      (∑ f : Fin n → I with Function.Bijective f,
          ∏ k, character (f k)) =
          ∑ f : Fin n → I with Function.Bijective f,
            ∏ i, character i := by
        apply Finset.sum_congr rfl
        intro f hf
        exact (Finset.mem_filter.mp hf).2.prod_comp character
      _ = (n.factorial : ℂ) * ∏ i, character i := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardFilter]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro f hf
    rw [if_neg]
    intro hbij
    apply hn
    have hcard := Fintype.card_congr (Equiv.ofBijective f hbij)
    simpa using hcard

theorem ons_decComponentSeries_hasSubst
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {I : Type*} [Fintype I]
    (base : I → ons_Dart L)
    (p : (i : I) → (ons_decGraph L).Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle) :
    PowerSeries.HasSubst (ons_decComponentSeries L a b base p) := by
  classical
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff,
    ons_decComponentSeries_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg]
  intro heq
  apply (ons_cycle_edges_toFinset_nonempty (p i) (hp i)).ne_empty
  apply ons_finsetExponent_injective
  simpa [ons_finsetExponent] using heq

theorem ons_decFormalRoot_coeff_eq_componentExp
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    (hS : S ∈ evenSubgraphs (ons_decGraph L))
    {I : Type*} [Fintype I] [DecidableEq I]
    (base : I → ons_Dart L)
    (p : (i : I) → (ons_decGraph L).Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i ↦ (p i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ (p i).edges.toFinset)) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) =
      MvPowerSeries.coeff (ons_finsetExponent S)
        (PowerSeries.subst (ons_decComponentSeries L a b base p)
          (PowerSeries.exp ℂ)) := by
  classical
  unfold ons_decFormalRoot
  rw [PowerSeries.coeff_subst
      (ons_decFormalLog_hasSubst L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)),
    PowerSeries.coeff_subst
      (ons_decComponentSeries_hasSubst L a b base p hp)]
  apply finsum_congr
  intro n
  rw [ons_decFormalLog_pow_coeff_eq_componentSeries
    L a b S hS base p hp hcover hdisj n]

theorem ons_decComponentExp_coeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    {I : Type*} [Fintype I] [DecidableEq I]
    (base : I → ons_Dart L)
    (p : (i : I) → (ons_decGraph L).Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i ↦ (p i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ (p i).edges.toFinset)) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (PowerSeries.subst (ons_decComponentSeries L a b base p)
          (PowerSeries.exp ℂ)) =
      ∏ i, (ons_spinCharacter a b
        (ons_evenHomology L (ons_walkOriginalEdges (p i))) : ℂ) := by
  classical
  rw [PowerSeries.coeff_subst
    (ons_decComponentSeries_hasSubst L a b base p hp)]
  rw [finsum_eq_single _ (Fintype.card I)]
  · rw [ons_decComponentSeries_pow_coeff
      L a b S base p hp hcover hdisj, if_pos rfl]
    simp only [PowerSeries.coeff_exp, smul_eq_mul]
    rw [one_div, map_inv₀, map_natCast]
    have hfac : ((Fintype.card I).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (Fintype.card I)
    field_simp
  · intro n hn
    rw [ons_decComponentSeries_pow_coeff
      L a b S base p hp hcover hdisj, if_neg hn, smul_zero]

theorem ons_decFormalRoot_coeff_evenSubgraph
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (D : ons_DecoratedEvenSubgraph L) :
    MvPowerSeries.coeff (ons_finsetExponent D.1)
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) =
      (ons_spinCharacter a b
        (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ) := by
  classical
  obtain ⟨I, hI, hdecI, base, p, hp, hcover, hedgeDisj, hvertDisj⟩ :=
    ons_decoratedSpinTerm_cycle_decomposition L D
  letI : Fintype I := hI
  letI : DecidableEq I := hdecI
  rw [ons_decFormalRoot_coeff_eq_componentExp
    L a b D.1 D.2 base p hp hcover hedgeDisj]
  rw [ons_decComponentExp_coeff
    L a b D.1 base p hp hcover hedgeDisj]
  let homology : I → Fin 2 × Fin 2 := fun i ↦
    ons_evenHomology L (ons_walkOriginalEdges (p i))
  have hisotropic : ∀ i ∈ (Finset.univ : Finset I),
      ∀ j ∈ (Finset.univ : Finset I), i ≠ j →
        ons_homologyIntersection (homology i) (homology j) = 0 := by
    intro i hi j hj hij
    exact ons_decCycles_originalHomology_isotropic
      L (p i) (p j) (hp i) (hp j) (hvertDisj hi hj hij)
  have hcharacter := ons_spinCharacter_sum_of_pairwise_intersection_zero
    a b Finset.univ homology hisotropic
  have hhomology :
      ons_evenHomology L (ons_originalEdgesOfDecorated L D) =
        ∑ i, homology i := by
    simpa only [homology, ons_walkOriginalEdges, ons_walkExternalEdges] using
      ons_originalHomology_biUnion D
        (fun i ↦ (p i).edges.toFinset) hcover hedgeDisj
  calc
    (∏ i, (ons_spinCharacter a b
        (ons_evenHomology L (ons_walkOriginalEdges (p i))) : ℂ)) =
        (ons_spinCharacter a b (∑ i, homology i) : ℂ) := by
      exact_mod_cast hcharacter.symm
    _ = (ons_spinCharacter a b
        (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ) := by
      rw [hhomology]

theorem ons_evenSubgraphs_biUnion_of_pairwiseDisjoint
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset I) (piece : I → Finset (Sym2 V))
    (hdisj : (T : Set I).PairwiseDisjoint piece)
    (hpiece : ∀ i ∈ T, piece i ∈ evenSubgraphs G) :
    T.biUnion piece ∈ evenSubgraphs G := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simpa using (show (∅ : Finset (Sym2 V)) ∈ evenSubgraphs G from by
        rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.empty_subset _, isEvenSubgraph_empty⟩)
  | @insert i T hi ih =>
      have hiPiece := hpiece i (by simp)
      have hTPiece : ∀ j ∈ T, piece j ∈ evenSubgraphs G := by
        intro j hj
        exact hpiece j (by simp [hj])
      have hdisjT : (T : Set I).PairwiseDisjoint piece := by
        intro j hj k hk hjk
        exact hdisj (by simp [hj]) (by simp [hk]) hjk
      have hrest := ih hdisjT hTPiece
      have hidisj : Disjoint (piece i) (T.biUnion piece) := by
        rw [Finset.disjoint_left]
        intro edge hei herest
        rw [Finset.mem_biUnion] at herest
        obtain ⟨j, hj, hej⟩ := herest
        have hij : i ≠ j := by
          intro hij
          subst j
          exact hi hj
        exact (Finset.disjoint_left.mp
          (hdisj (by simp) (by simp [hj]) hij)) hei hej
      rw [Finset.biUnion_insert]
      rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hiPiece
      rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hrest
      rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.union_subset hiPiece.1 hrest.1, ?_⟩
      rw [← Finset.symmDiff_eq_union hidisj]
      exact isEvenSubgraph_symmDiff hiPiece.2 hrest.2

theorem ons_decFormalRoot_coeff_squarefree_eq_zero_of_not_even
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    (hS : S ∉ evenSubgraphs (ons_decGraph L)) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
  classical
  unfold ons_decFormalRoot
  rw [PowerSeries.coeff_subst
    (ons_decFormalLog_hasSubst L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b))]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  apply smul_eq_zero.mpr
  right
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro g hg
  by_contra hprod
  apply hS
  let support : ℕ → Finset (ons_DecEdge L) := fun i ↦ (g i).support
  have hpiece : ∀ i ∈ Finset.range n,
      support i ∈ evenSubgraphs (ons_decGraph L) := by
    intro i hi
    have hcoeffNe : MvPowerSeries.coeff (g i)
        (ons_decFormalLog L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) ≠ 0 := by
      intro hzero
      apply hprod
      exact Finset.prod_eq_zero hi hzero
    have hcomponent :=
      ons_finsuppAntidiag_finsetExponent_component
        (Finset.range n) S g hg hi
    change ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) (g i) ≠ 0 at hcoeffNe
    rw [hcomponent] at hcoeffNe
    obtain ⟨root, q, hq, hsnd, hqedges, hcoeff⟩ :=
      ons_decFormalLogCoeff_squarefree_cycle_of_ne_zero
        L a b (support i) hcoeffNe
    rw [← hqedges]
    exact ons_cycle_edges_evenSubgraph (ons_decGraph L) q hq
  have hpair : ((Finset.range n : Finset ℕ) : Set ℕ).PairwiseDisjoint
      support := by
    intro i hi j hj hij
    exact ons_finsuppAntidiag_finsetExponent_support_disjoint
      (Finset.range n) S g hg hi hj hij
  have hunion := ons_evenSubgraphs_biUnion_of_pairwiseDisjoint
    (ons_decGraph L) (Finset.range n) support hpair hpiece
  rw [← ons_finsuppAntidiag_finsetExponent_support_cover
    (Finset.range n) S g hg] at hunion
  exact hunion

theorem ons_decoratedSpinPolynomial_coeff_finsetExponent_of_not_even
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    (hS : S ∉ evenSubgraphs (ons_decGraph L)) :
    MvPolynomial.coeff (ons_finsetExponent S)
        (ons_decoratedSpinPolynomial L a b) = 0 := by
  classical
  unfold ons_decoratedSpinPolynomial
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro D hD
  rw [MvPolynomial.coeff_monomial, if_neg]
  intro heq
  apply hS
  have hsets : S = D.1 := ons_finsetExponent_injective heq.symm
  simpa [hsets] using D.2

theorem ons_decFormalRoot_coeff_finsetExponent
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L)) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) =
      MvPowerSeries.coeff (ons_finsetExponent S)
        (ons_decoratedSpinPolynomial L a b :
          MvPowerSeries (ons_DecEdge L) ℂ) := by
  classical
  by_cases hS : S ∈ evenSubgraphs (ons_decGraph L)
  · let D : ons_DecoratedEvenSubgraph L := ⟨S, hS⟩
    rw [show S = D.1 from rfl,
      ons_decFormalRoot_coeff_evenSubgraph L a b D,
      MvPolynomial.coeff_coe,
      ons_decoratedSpinPolynomial_coeff L a b D]
  · rw [ons_decFormalRoot_coeff_squarefree_eq_zero_of_not_even
      L a b S hS,
      MvPolynomial.coeff_coe,
      ons_decoratedSpinPolynomial_coeff_finsetExponent_of_not_even
        L a b S hS]

def ons_IsSquarefreeExponent {E : Type*} (m : E →₀ ℕ) : Prop :=
  ∀ edge, m edge ≤ 1

theorem ons_eq_finsetExponent_support_of_squarefree
    {E : Type*} [DecidableEq E] (m : E →₀ ℕ)
    (hm : ons_IsSquarefreeExponent m) :
    m = ons_finsetExponent m.support := by
  ext edge
  rw [ons_finsetExponent_apply]
  by_cases hedge : edge ∈ m.support
  · rw [if_pos hedge]
    have hpos : 0 < m edge :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hedge)
    have hle := hm edge
    omega
  · rw [if_neg hedge]
    exact Finsupp.notMem_support_iff.mp hedge

theorem ons_decoratedSpinPolynomial_coeff_eq_zero_of_not_squarefree
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (m : ons_DecEdge L →₀ ℕ)
    (hm : ¬ ons_IsSquarefreeExponent m) :
    MvPowerSeries.coeff m
        (ons_decoratedSpinPolynomial L a b :
          MvPowerSeries (ons_DecEdge L) ℂ) = 0 := by
  classical
  rw [MvPolynomial.coeff_coe]
  unfold ons_decoratedSpinPolynomial
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro D hD
  rw [MvPolynomial.coeff_monomial, if_neg]
  intro heq
  apply hm
  intro edge
  rw [← heq, ons_finsetExponent_apply]
  split <;> omega

theorem ons_decoratedFormalKacWardIdentity_of_nonsquarefree_zero
    (L : ℕ) [Fact (2 < L)]
    (hnonsquare : ∀ (a b : Fin 2) (m : ons_DecEdge L →₀ ℕ),
      ¬ ons_IsSquarefreeExponent m →
      MvPowerSeries.coeff m
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) = 0) :
    ons_decoratedFormalKacWardIdentity L := by
  intro a b
  ext m
  by_cases hm : ons_IsSquarefreeExponent m
  · rw [ons_eq_finsetExponent_support_of_squarefree m hm]
    exact ons_decFormalRoot_coeff_finsetExponent L a b m.support
  · rw [hnonsquare a b m hm,
      ons_decoratedSpinPolynomial_coeff_eq_zero_of_not_squarefree
        L a b m hm]

end StatMech.Onsager
