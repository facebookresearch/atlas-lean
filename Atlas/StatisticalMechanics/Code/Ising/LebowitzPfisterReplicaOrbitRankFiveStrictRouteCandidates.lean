/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute










namespace StatMech.Ising

noncomputable section

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveStrictRouteCandidatesDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _




theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (c : Copy (lpReplicaCurrentGraph G sites)
      (z.toAggregate G sites q).2.2.2.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites
      (lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q
        (z.toAggregate G sites q))) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    let K := Finset.univ \ {c}
    let E := endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
    K.card = 4 ∧
      StatMech.Sharpness.RandomCurrent.sources E K =
        lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k ∧
      K.biUnion (fun e => (E e).toFinset) =
        lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k ∧
      ∀ x ∈ lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k,
        ∃! e, e ∈ K ∧ x ∈ (E e).toFinset := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let K := Finset.univ \ {c}
  let E := endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hKcard : K.card = 4 :=
    lpReplicaOffdiagDecoratedSource_card_erase_copy_rankFive
      G sites q hcard a.2.2.2 c
  have hsources : StatMech.Sharpness.RandomCurrent.sources E K =
      lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k :=
    lpReplicaOffdiagDecoratedSource_sources_erase_seamCopy
      G sites q a.2.2.2 c hc
  have htight :
      (StatMech.Sharpness.RandomCurrent.sources E K).card =
        2 * K.card := by
    rw [hsources, card_lpReplicaTripleSeamGhostSource sites hsite
      hij hik hjk, hKcard]
  have hsupport : K.biUnion (fun e => (E e).toFinset) =
      lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k :=
    (randomCurrent_endpointSupport_eq_sources_of_card_eq_two_mul
      E K htight).trans hsources
  refine ⟨hKcard, hsources, hsupport, ?_⟩
  intro x hx
  apply randomCurrent_existsUnique_copy_of_mem_endpointSupport_of_card_eq_two_mul
    E K htight
  rw [hsupport]
  exact hx



noncomputable def
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    Copy (lpReplicaCurrentGraph G sites)
      (z.toAggregate G sites q).2.2.2.1.1.1 :=
  Classical.choose
    (lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy
      G sites hsite q (z.toAggregate G sites q))

@[simp] theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy_edge
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z).1.1 =
      lpReplicaCurrentSeamEdge sites
        (lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q
          (z.toAggregate G sites q)) :=
  Classical.choose_spec
    (lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy
      G sites hsite q (z.toAggregate G sites q))



noncomputable def
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    Finset (Copy (lpReplicaCurrentGraph G sites)
      (z.toAggregate G sites q).2.2.2.1.1.1) := by
  classical
  let a := z.toAggregate G sites q
  let c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z
  exact Finset.univ.filter fun d =>
    d ∈ Finset.univ \ {c} ∧
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
        endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
        endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
      ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag

theorem
    mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : Copy (lpReplicaCurrentGraph G sites)
      (z.toAggregate G sites q).2.2.2.1.1.1) :
    d ∈ lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z ↔
      let a := z.toAggregate G sites q
      let c :=
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
          G sites hsite q z
      d ∈ Finset.univ \ {c} ∧
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
          endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
          endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
        ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag := by
  classical
  simp only [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates,
    Finset.mem_filter, Finset.mem_univ, true_and]

set_option maxHeartbeats 2000000 in


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_nonempty
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z).Nonempty := by
  classical
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z
  have hc : c.1.1 = lpReplicaCurrentSeamEdge sites k :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy_edge
      G sites hsite q z
  have hpm :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy
      G sites hsite q hcard z c hc
  dsimp only at hpm
  let K := Finset.univ \ {c}
  let E := endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  obtain ⟨hKcard, _hsources, hsupport, hunique⟩ := hpm
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hunmarked :=
    LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement
      G sites hsite hij q hcard z.2.2.2.1 z.2.2.2.2
  obtain ⟨d, hdK, hd0, hd1, hddiag⟩ :=
    lpReplica_fourCopyTripleMatching_exists_strictPhysicalRoute
      G sites hsite hij hik hjk a.2.2.2.1.1.1 K hKcard hsupport hunique
        (fun e _ => hunmarked.2.1 e) (fun e _ => hunmarked.2.2 e)
  refine ⟨d, ?_⟩
  rw [mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff]
  exact ⟨hdK, hd0, hd1, hddiag⟩

set_option maxHeartbeats 2000000 in



theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictRouteData_of_candidate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : Copy (lpReplicaCurrentGraph G sites)
      (z.toAggregate G sites q).2.2.2.1.1.1)
    (hd : d ∈
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    ∃ route : LPReplicaAggregateRankFiveStrictRouteData G sites q a k,
      route.c =
          lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
            G sites hsite q z ∧
        route.d = d := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z
  have hc : c.1.1 = lpReplicaCurrentSeamEdge sites k :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy_edge
      G sites hsite q z
  have hd' :=
    (mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
      G sites hsite q z d).mp hd
  dsimp only at hd'
  obtain ⟨hdK, hd0, hd1, hddiag⟩ := hd'
  have hpm :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy
      G sites hsite q hcard z c hc
  dsimp only at hpm
  let K := Finset.univ \ {c}
  let E := endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  obtain ⟨_hKcard, _hsources, hsupport, hunique⟩ := hpm
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  obtain ⟨u, v, hu, hv, huv, hfold⟩ :=
    lpReplica_strictPhysicalRoute_folded_labels G sites hsite
      hij hik hjk a.2.2.2.1.1.1 K hsupport d hdK hd0 hd1 hddiag
  have hl := lpReplicaThirdOfThree_spec hij hik hjk hu hv huv
  have hdisc :=
    lpReplica_partialReflect_strictMatchingRoute_ghost_disconnected
      G sites hsite a.2.2.2.1.1.1 K
        (lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k) d hdK
        hsupport hunique
        (lpReplicaCurrentGhost0_mem_tripleSeamGhostSource
          sites a.1 a.2.1 k)
        (lpReplicaCurrentGhost1_mem_tripleSeamGhostSource
          sites a.1 a.2.1 k)
        huv hfold
  refine ⟨{
    c := c
    d := d
    u := u
    v := v
    hc := hc
    hdK := hdK
    hu := hu
    hv := hv
    huv := huv
    hfold := hfold
    hl := hl
    hdisc := hdisc
  }, rfl, rfl⟩


noncomputable def
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    LPReplicaAggregateRankFiveStrictRouteData G sites q a k := by
  dsimp only
  exact Classical.choose
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictRouteData_of_candidate
      G sites hsite q hcard z d.1 d.2)

theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_c
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z d).c =
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
          G sites hsite q z := by
  exact (Classical.choose_spec
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictRouteData_of_candidate
      G sites hsite q hcard z d.1 d.2)).1

theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_d
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z d).d = d.1 := by
  exact (Classical.choose_spec
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictRouteData_of_candidate
      G sites hsite q hcard z d.1 d.2)).2



theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_pos
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    0 < (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z).card :=
  Finset.card_pos.mpr
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_nonempty
      G sites hsite q hcard z)

set_option maxHeartbeats 2000000 in



theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_le_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z).card ≤ 2 := by
  classical
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z
  have hc : c.1.1 = lpReplicaCurrentSeamEdge sites k :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy_edge
      G sites hsite q z
  have hpm :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy
      G sites hsite q hcard z c hc
  dsimp only at hpm
  let K := Finset.univ \ {c}
  let E := endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  obtain ⟨hKcard, _hsources, _hsupport, hunique⟩ := hpm
  have hg0 := lpReplicaCurrentGhost0_mem_tripleSeamGhostSource
    (V := V) sites a.1 a.2.1 k
  have hg1 := lpReplicaCurrentGhost1_mem_tripleSeamGhostSource
    (V := V) sites a.1 a.2.1 k
  obtain ⟨c0, hc0, _hc0unique⟩ := hunique lpReplicaCurrentGhost0 hg0
  obtain ⟨c1, hc1, _hc1unique⟩ := hunique lpReplicaCurrentGhost1 hg1
  have hc01 : c0 ≠ c1 := by
    intro h
    subst c1
    have he0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ E c0 :=
      Sym2.mem_toFinset.mp hc0.2
    have he1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ E c0 :=
      Sym2.mem_toFinset.mp hc1.2
    have hedge : c0.1.1 =
        s((lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
          lpReplicaCurrentGhost1) :=
      sym2_eq_mk_of_mem_of_mem_of_ne he0 he1 (by
        simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])
    have hgraph := SimpleGraph.mem_edgeFinset.mp c0.1.2
    rw [hedge] at hgraph
    simpa [lpReplicaCurrentGraph, lpReplicaCurrentRel,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hgraph
  let ghosts : Finset (Copy (lpReplicaCurrentGraph G sites)
      a.2.2.2.1.1.1) := {c0, c1}
  have hghostsK : ghosts ⊆ K := by
    intro e he
    simp only [ghosts, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hc0.1
    · exact hc1.1
  have hcandidateSub :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
          G sites hsite q z ⊆ K \ ghosts := by
    intro d hd
    have hd' :=
      (mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
        G sites hsite q z d).mp hd
    dsimp only at hd'
    apply Finset.mem_sdiff.mpr
    refine ⟨hd'.1, ?_⟩
    simp only [ghosts, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hdc0
      subst d
      exact hd'.2.1 (Sym2.mem_toFinset.mp hc0.2)
    · intro hdc1
      subst d
      exact hd'.2.2.1 (Sym2.mem_toFinset.mp hc1.2)
  calc
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card ≤ (K \ ghosts).card :=
      Finset.card_le_card hcandidateSub
    _ = K.card - ghosts.card := Finset.card_sdiff_of_subset hghostsK
    _ = 2 := by
      have hK : K.card = 4 := hKcard
      have hg : ghosts.card = 2 := by simp [ghosts, hc01]
      rw [hK, hg]


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_eq_one_or_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card = 1 ∨
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card = 2 := by
  have hpos :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_pos
      G sites hsite q hcard z
  have hle :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_le_two
      G sites hsite q hcard z
  omega

end

end StatMech.Ising
