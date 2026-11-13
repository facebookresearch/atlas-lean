/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardTrivalentFormalAssembly














open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

open StatMech.Onsager

universe u


noncomputable def kwGraphLoopWalk
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hvalid : ∀ k, G.DartAdj (loop k) (loop (k + 1))) :
    G.Walk (loop 0).fst (loop 0).fst := by
  let darts := List.ofFn loop
  have hdarts : darts ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_ofFn]
    exact NeZero.pos n
  have hclosed : List.IsChain G.DartAdj (darts ++ [loop 0]) := by
    exact StatMech.Onsager.ons_isChain_closed_ofFn_mk loop hvalid
  have hchain : List.IsChain G.DartAdj darts := by
    have := hclosed.dropLast
    simpa [darts] using this
  let walk := SimpleGraph.Walk.ofDarts darts hdarts hchain
  refine walk.copy ?_ ?_
  · change (darts.head hdarts).fst = (loop 0).fst
    simp only [darts, List.head_ofFn]
    congr 2
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    have hlast := hvalid (Fin.last m)
    change (darts.getLast hdarts).snd = (loop 0).fst
    simpa only [darts, List.getLast_ofFn, Nat.succ_sub_one,
      Fin.last_add_one] using hlast

@[simp] theorem kwGraphLoopWalk_darts
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hvalid : ∀ k, G.DartAdj (loop k) (loop (k + 1))) :
    (kwGraphLoopWalk G loop hvalid).darts = List.ofFn loop := by
  unfold kwGraphLoopWalk
  simp

@[simp] theorem kwGraphLoopWalk_edges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hvalid : ∀ k, G.DartAdj (loop k) (loop (k + 1))) :
    (kwGraphLoopWalk G loop hvalid).edges =
      (List.ofFn loop).map SimpleGraph.Dart.edge := by
  rw [SimpleGraph.Walk.edges, kwGraphLoopWalk_darts]



theorem kwGraphLoopWalk_edgeCount
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hvalid : ∀ k, G.DartAdj (loop k) (loop (k + 1))) :
    Multiset.toFinsupp
        ((kwGraphLoopWalk G loop hvalid).edges : Multiset (Sym2 V)) =
      kwGraphLoopExponent G loop := by
  ext edge
  rw [Multiset.toFinsupp_apply, kwGraphLoopWalk_edges]
  unfold kwGraphLoopExponent
  rw [Finsupp.finsetSum_apply]
  have hcount : ∀ l : List G.Dart,
      List.count edge (l.map SimpleGraph.Dart.edge) =
        (l.map fun dart => if dart.edge = edge then 1 else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons dart rest ih =>
        by_cases h : dart.edge = edge
        · simp [h, ih, add_comm]
        · have h' : edge ≠ dart.edge := Ne.symm h
          simp [h, ih]
  rw [Multiset.coe_count, hcount, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  simp [Finsupp.single_apply]



theorem kwGraphLoopWalk_isTrail_and_edges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hvalid : ∀ k, G.DartAdj (loop k) (loop (k + 1)))
    (S : Finset (Sym2 V))
    (hexponent : kwGraphLoopExponent G loop = ons_finsetExponent S) :
    (kwGraphLoopWalk G loop hvalid).IsTrail ∧
      (kwGraphLoopWalk G loop hvalid).edges.toFinset = S := by
  let p := kwGraphLoopWalk G loop hvalid
  have hcount : Multiset.toFinsupp (p.edges : Multiset (Sym2 V)) =
      ons_finsetExponent S := by
    rw [kwGraphLoopWalk_edgeCount G loop hvalid, hexponent]
  have htrail : p.IsTrail := by
    rw [SimpleGraph.Walk.isTrail_def]
    apply List.nodup_iff_count_le_one.mpr
    intro edge
    have hedge := DFunLike.congr_fun hcount edge
    rw [Multiset.toFinsupp_apply, ons_finsetExponent_apply] at hedge
    rw [Multiset.coe_count] at hedge
    split at hedge <;> omega
  refine ⟨htrail, ?_⟩
  apply ons_finsetExponent_injective
  rw [ons_finsetExponent_toFinset_eq_edgeCount p.edges htrail.edges_nodup]
  exact hcount



theorem kwGraphLoop_valid_of_scalar_ne_zero
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hscalar : kwGraphLoopScalar G phase loop ≠ 0) :
    ∀ k, G.DartAdj (loop k) (loop (k + 1)) := by
  intro k
  have hfactor : kwGraphTransition G (fun _ ↦ 1) phase
      (loop k) (loop (k + 1)) ≠ 0 := by
    intro hzero
    apply hscalar
    unfold kwGraphLoopScalar
    exact Finset.prod_eq_zero (Finset.mem_univ k) hzero
  unfold kwGraphTransition at hfactor
  by_contra hadj
  have hcondition : ¬((loop k).snd = (loop (k + 1)).fst ∧
      (loop k).edge ≠ (loop (k + 1)).edge) := by
    intro h
    exact hadj h.1
  rw [if_neg hcondition] at hfactor
  exact hfactor rfl


theorem kw_closedTrail_isCycle_of_degree_le_three
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {root : V} (p : G.Walk root root) (hp : p.IsTrail)
    (hne : p ≠ .nil) (hdeg : ∀ vertex, G.degree vertex ≤ 3) :
    p.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨hp, hne, List.nodup_iff_count_le_one.mpr ?_⟩
  intro vertex
  have hcount := ons_closed_walk_count_incident_edges p vertex
  have hle : p.edges.countP (fun edge ↦ vertex ∈ edge) ≤
      G.degree vertex := by
    let F := p.edges.toFinset
    have hFsub : F ⊆ G.edgeFinset := by
      intro edge hedge
      rw [SimpleGraph.mem_edgeFinset]
      exact p.edges_subset_edgeSet (List.mem_toFinset.mp hedge)
    have hcountF :
        p.edges.countP (fun edge ↦ vertex ∈ edge) =
          StatMech.Ising.incCount F vertex := by
      calc
        p.edges.countP (fun edge ↦ vertex ∈ edge) =
            (p.edges.filter (fun edge ↦ vertex ∈ edge)).length :=
          List.countP_eq_length_filter
        _ = (p.edges.filter
              (fun edge ↦ vertex ∈ edge)).toFinset.card :=
          (List.toFinset_card_of_nodup
            (hp.edges_nodup.filter (fun edge ↦ vertex ∈ edge))).symm
        _ = StatMech.Ising.incCount F vertex := by
          unfold StatMech.Ising.incCount F
          congr 1
          ext edge
          simp
    rw [hcountF]
    classical
    rw [← SimpleGraph.card_incidenceFinset_eq_degree]
    unfold StatMech.Ising.incCount
    apply Finset.card_le_card
    intro edge hedge
    rw [Finset.mem_filter] at hedge
    rw [SimpleGraph.mem_incidenceFinset]
    refine ⟨?_, hedge.2⟩
    have hedgeG : edge ∈ G.edgeFinset := hFsub hedge.1
    rw [SimpleGraph.mem_edgeFinset] at hedgeG
    exact hedgeG
  have hdegree := hdeg vertex
  omega



theorem kwGraphFormalLogCoeff_squarefree_cycle_of_ne_zero
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (S : Finset (Sym2 V))
    (hne : kwGraphFormalLogCoeff G phase (ons_finsetExponent S) ≠ 0) :
    ∃ (root : V) (p : G.Walk root root),
      p.IsCycle ∧ p.edges.toFinset = S := by
  classical
  unfold kwGraphFormalLogCoeff at hne
  have houter : ∑ r ∈ Finset.range
      (ons_finsuppTotalDegree (ons_finsetExponent S)),
      (∑ loop : Fin (r + 1) → G.Dart,
        if kwGraphLoopExponent G loop = ons_finsetExponent S then
          kwGraphLoopScalar G phase loop else 0) / ((r : ℂ) + 1) ≠ 0 := by
    intro hzero
    apply hne
    rw [hzero]
    ring
  obtain ⟨r, hr, hrne⟩ := Finset.exists_ne_zero_of_sum_ne_zero houter
  have hinner : (∑ loop : Fin (r + 1) → G.Dart,
      if kwGraphLoopExponent G loop = ons_finsetExponent S then
        kwGraphLoopScalar G phase loop else 0) ≠ 0 := by
    intro hzero
    apply hrne
    rw [hzero, zero_div]
  obtain ⟨loop, _, hloop⟩ := Finset.exists_ne_zero_of_sum_ne_zero hinner
  by_cases hexponent : kwGraphLoopExponent G loop = ons_finsetExponent S
  · have hscalar : kwGraphLoopScalar G phase loop ≠ 0 := by
      simpa [hexponent] using hloop
    let hvalid := kwGraphLoop_valid_of_scalar_ne_zero G phase loop hscalar
    let p := kwGraphLoopWalk G loop hvalid
    have hpdata := kwGraphLoopWalk_isTrail_and_edges
      G loop hvalid S hexponent
    have hpne : p ≠ .nil := by
      intro hp
      have hdarts := kwGraphLoopWalk_darts G loop hvalid
      rw [show kwGraphLoopWalk G loop hvalid = p from rfl, hp] at hdarts
      have hlen := congrArg List.length hdarts
      simp at hlen
    have hpcycle : p.IsCycle :=
      kw_closedTrail_isCycle_of_degree_le_three G p hpdata.1 hpne hdeg
    exact ⟨loop 0 |>.fst, p, hpcycle, hpdata.2⟩
  · simp [hexponent] at hloop



theorem kwGraphUnitCycleLog_iff_cycleCoeff_of_degree_le_three
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3) :
    KWGraphUnitCycleLog G phase ↔
      ∀ {root : V} (p : G.Walk root root), p.IsCycle →
        kwGraphFormalLogCoeff G phase
          (ons_finsetExponent p.edges.toFinset) = 1 := by
  constructor
  · exact fun hunit ↦ hunit.1
  · intro hcycle
    exact ⟨hcycle,
      kwGraphFormalLogCoeff_squarefree_cycle_of_ne_zero G phase hdeg⟩



theorem kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleCoeff
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hcycle : ∀ {root : V} (p : G.Walk root root), p.IsCycle →
      kwGraphFormalLogCoeff G embedding.turnPhase
        (ons_finsetExponent p.edges.toFinset) = 1) :
    kwGraphFormalRoot G embedding.turnPhase =
      kwGraphFormalEvenPolynomial G := by
  apply kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_unitCycleLog
    G embedding
  · exact (kwGraphUnitCycleLog_iff_cycleCoeff_of_degree_le_three
      G embedding.turnPhase hdeg).2 hcycle
  · exact hdeg



theorem kw_straightLineGraph_detWalkRoot_eq_evenPolynomial_of_cycleCoeff
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hcycle : ∀ {root : V} (p : G.Walk root root), p.IsCycle →
      kwGraphFormalLogCoeff G embedding.turnPhase
        (ons_finsetExponent p.edges.toFinset) = 1)
    (weight : Sym2 V → ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    StatMech.Onsager.ons_detWalkRoot
        (kwGraphTransition G weight embedding.turnPhase) =
      kwEvenPolynomial G weight := by
  apply kw_straightLineGraph_detWalkRoot_eq_evenPolynomial_of_unitCycleLog
    G embedding
  · exact (kwGraphUnitCycleLog_iff_cycleCoeff_of_degree_le_three
      G embedding.turnPhase hdeg).2 hcycle
  · exact hdeg
  · exact hq
  · exact hentry
  · exact hcard



theorem kacWard_straightLine_trivalent_of_cycleCoeff
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hcycle : ∀ {root : V} (p : G.Walk root root), p.IsCycle →
      kwGraphFormalLogCoeff G embedding.turnPhase
        (ons_finsetExponent p.edges.toFinset) = 1)
    (weight : Sym2 V → ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 := by
  apply kacWard_straightLine_trivalent_of_unitCycleLog G embedding
  · exact (kwGraphUnitCycleLog_iff_cycleCoeff_of_degree_le_three
      G embedding.turnPhase hdeg).2 hcycle
  · exact hdeg
  · exact hq
  · exact hentry
  · exact hcard

end StatMech.FrontierA
