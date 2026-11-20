/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaSourceToggle










open Finset SimpleGraph
open scoped BigOperators symmDiff

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

namespace ReplicaCutParity

open StatMech.Sharpness.RandomCurrent

variable {W ι : Type*} [Fintype W] [DecidableEq W]
  [Fintype ι] [DecidableEq ι]

private theorem edge_side_card_even_of_no_cross
    (ends : ι -> Sym2 W) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
    (S : Finset W)
    (hno : ∀ {u v}, u ∈ S -> v ∉ S ->
      ¬ RandomCurrent.connK ends K u v)
    {i : ι} (hi : i ∈ K) :
    Even (#(S.filter fun x => x ∈ ends i)) := by
  obtain ⟨⟨a, b⟩, hab⟩ := (ends i).exists_rep
  have hne : a ≠ b := by
    intro h
    subst b
    exact hnd i hi (hab ▸ Sym2.mk_isDiag_iff.mpr rfl)
  have hset :
      S.filter (fun x => x ∈ ends i) =
        ({a, b} : Finset W).filter (fun x => x ∈ S) := by
    ext x
    simp only [Finset.mem_filter, ← hab, Sym2.mem_iff,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hsides : a ∈ S ↔ b ∈ S := by
    constructor
    · intro ha
      by_contra hb
      exact hno ha hb (Relation.ReflTransGen.single
        ⟨i, hi, hab ▸ Sym2.mem_mk_left a b,
          hab ▸ Sym2.mem_mk_right a b, hne⟩)
    · intro hb
      by_contra ha
      exact hno hb ha (Relation.ReflTransGen.single
        ⟨i, hi, hab ▸ Sym2.mem_mk_right a b,
          hab ▸ Sym2.mem_mk_left a b, hne.symm⟩)
  rw [hset]
  by_cases ha : a ∈ S
  · have hb := hsides.mp ha
    rw [Finset.filter_insert, Finset.filter_singleton,
      if_pos ha, if_pos hb,
      Finset.card_insert_of_notMem (by simp [hne]),
      Finset.card_singleton]
    exact ⟨1, rfl⟩
  · have hb : b ∉ S := fun h => ha (hsides.mpr h)
    rw [Finset.filter_insert, Finset.filter_singleton,
      if_neg ha, if_neg hb]
    simp



theorem sources_inter_even_of_no_cross
    (ends : ι -> Sym2 W) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
    (S : Finset W)
    (hno : ∀ {u v}, u ∈ S -> v ∉ S ->
      ¬ RandomCurrent.connK ends K u v) :
    Even (#(RandomCurrent.sources ends K ∩ S)) := by
  have hsumEq :
      (∑ x ∈ S, RandomCurrent.degK ends K x) =
        ∑ i ∈ K, #(S.filter fun x => x ∈ ends i) := by
    unfold RandomCurrent.degK
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hsum : Even (∑ x ∈ S, RandomCurrent.degK ends K x) := by
    rw [hsumEq]
    exact Finset.even_sum _ fun i hi =>
      edge_side_card_even_of_no_cross ends K hnd S hno hi
  have hcount := (RandomCurrent.even_sum_iff_even_count S
    (RandomCurrent.degK ends K)).mp hsum
  convert hcount using 1
  congr 1
  ext x
  simp only [Finset.mem_inter, Finset.mem_filter,
    RandomCurrent.mem_sources]
  tauto


theorem exists_cross_connection_of_odd_sources
    (ends : ι -> Sym2 W) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
    (S : Finset W)
    (hodd : Odd (#(RandomCurrent.sources ends K ∩ S))) :
    ∃ u ∈ S, ∃ v ∉ S, RandomCurrent.connK ends K u v := by
  by_contra h
  push_neg at h
  have heven := sources_inter_even_of_no_cross ends K hnd S
    (fun {_ _} hu hv => h _ hu _ hv)
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end ReplicaCutParity

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaCurrent_exists_crossConnection_of_odd_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hodd : Odd (#(StatMech.Sharpness.sources
      (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) ∩
        lpReplicaCurrentLeftSide))) :
    ∃ u ∈ lpReplicaCurrentLeftSide,
      ∃ v ∉ lpReplicaCurrentLeftSide,
        CurrentConnected (lpReplicaCurrentGraph G sites)
          (ofEdgeFun (lpReplicaCurrentGraph G sites) m) u v := by
  let H := lpReplicaCurrentGraph G sites
  have hsrc :
      RandomCurrent.sources (endsM H m)
          (Finset.univ : Finset (Copy H m)) =
        StatMech.Sharpness.sources H (ofEdgeFun H m) := by
    rw [sources_eq, profileFlux_univ]
  have hoddCopy : Odd (#(RandomCurrent.sources (endsM H m)
      (Finset.univ : Finset (Copy H m)) ∩
        lpReplicaCurrentLeftSide)) := by
    rwa [hsrc]
  obtain ⟨u, hu, v, hv, huv⟩ :=
    ReplicaCutParity.exists_cross_connection_of_odd_sources
      (endsM H m) (Finset.univ : Finset (Copy H m))
      (fun i _ => endsM_not_isDiag H m i)
      lpReplicaCurrentLeftSide hoddCopy
  exact ⟨u, hu, v, hv, (connK_univ_iff H m u v).mp huv⟩



theorem lpReplicaCurrent_exists_positiveSeam_of_crossConnection
    (G : SimpleGraph V) (sites : I -> V)
    (n : Current (LPReplicaCurrentVertex V))
    {u v : LPReplicaCurrentVertex V}
    (hu : u ∈ lpReplicaCurrentLeftSide)
    (hv : v ∉ lpReplicaCurrentLeftSide)
    (huv : CurrentConnected (lpReplicaCurrentGraph G sites) n u v) :
    ∃ i : I, 0 < n (lpReplicaCurrentSeamEdge sites i) := by
  obtain ⟨w⟩ := huv
  obtain ⟨k, _, _, hkout, hkin, hkadj, _⟩ :=
    walk_firstExit w lpReplicaCurrentLeftSide hu hv
  obtain ⟨i, hi⟩ := lpReplicaCurrent_crossingEdge_eq_seam
    G sites hkin hkout hkadj.1
  refine ⟨i, ?_⟩
  change 1 ≤ n (lpReplicaCurrentSeamEdge sites i)
  rw [← hi]
  exact hkadj.2



theorem lpReplicaCurrent_exists_connectedSeam_of_crossConnection
    (G : SimpleGraph V) (sites : I -> V)
    (n : Current (LPReplicaCurrentVertex V))
    {u v : LPReplicaCurrentVertex V}
    (hu : u ∈ lpReplicaCurrentLeftSide)
    (hv : v ∉ lpReplicaCurrentLeftSide)
    (huv : CurrentConnected (lpReplicaCurrentGraph G sites) n u v) :
    ∃ i : I, CurrentConnected (lpReplicaCurrentGraph G sites) n
      (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites i) := by
  obtain ⟨i, hi⟩ := lpReplicaCurrent_exists_positiveSeam_of_crossConnection
    G sites n hu hv huv
  refine ⟨i, SimpleGraph.Adj.reachable ?_⟩
  constructor
  · unfold lpReplicaCurrentLeft lpReplicaCurrentRight
    rw [lpReplicaCurrentGraph_adj_left_right_iff]
    exact ⟨i, rfl, rfl⟩
  · exact hi



theorem lpReplicaCurrent_exists_connectedSeam_of_odd_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hodd : Odd (#(StatMech.Sharpness.sources
      (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) ∩
        lpReplicaCurrentLeftSide))) :
    ∃ i : I, CurrentConnected (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites i) := by
  obtain ⟨u, hu, v, hv, huv⟩ :=
    lpReplicaCurrent_exists_crossConnection_of_odd_sources G sites m hodd
  exact lpReplicaCurrent_exists_connectedSeam_of_crossConnection
    G sites (ofEdgeFun (lpReplicaCurrentGraph G sites) m) hu hv huv



theorem lpReplicaCurrent_exists_positiveSeam_of_odd_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hodd : Odd (#(StatMech.Sharpness.sources
      (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) ∩
        lpReplicaCurrentLeftSide))) :
    ∃ i : I, 0 < (ofEdgeFun (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentSeamEdge sites i) := by
  obtain ⟨u, hu, v, hv, huv⟩ :=
    lpReplicaCurrent_exists_crossConnection_of_odd_sources G sites m hodd
  obtain ⟨i, hi⟩ := lpReplicaCurrent_exists_positiveSeam_of_crossConnection
    G sites (ofEdgeFun (lpReplicaCurrentGraph G sites) m) hu hv huv
  exact ⟨i, hi⟩



theorem lpReplica_offdiagSource_inter_leftSide
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j : I} (hij : i ≠ j) :
    ((lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) ∩ lpReplicaCurrentLeftSide) =
      {lpReplicaCurrentLeft sites i,
        lpReplicaCurrentLeft sites j, lpReplicaCurrentGhost0} := by
  have hs : sites i ≠ sites j := hsite.ne hij
  ext z
  rcases z with (z | b)
  · rcases z with x | x
    · simp [lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
        Finset.mem_symmDiff, hs, hs.symm]
      constructor
      · rintro (⟨hi, _⟩ | ⟨hj, _⟩)
        · exact Or.inl hi
        · exact Or.inr hj
      · rintro (hi | hj)
        · exact Or.inl ⟨hi, fun h => hs (hi.symm.trans h)⟩
        · exact Or.inr ⟨hj, fun h => hs (h.symm.trans hj)⟩
    · simp [lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
        Finset.mem_symmDiff]
  · cases b <;>
      simp [lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
        Finset.mem_symmDiff]


theorem lpReplica_offdiagSource_left_odd
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j : I} (hij : i ≠ j) :
    Odd (#((lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) ∩ lpReplicaCurrentLeftSide)) := by
  rw [lpReplica_offdiagSource_inter_leftSide sites hsite hij]
  have hs : sites i ≠ sites j := hsite.ne hij
  have hleft : lpReplicaCurrentLeft sites i ≠
      lpReplicaCurrentLeft sites j := by
    intro h
    exact hij (hsite (Sum.inl.inj (Sum.inl.inj h)))
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · exact ⟨1, rfl⟩
  · simp [lpReplicaCurrentLeft, lpReplicaCurrentGhost0]
  · intro hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact hleft h
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentGhost0] at h



theorem lpReplicaCurrent_exists_connectedSeam_of_offdiagSource
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hsrc : StatMech.Sharpness.sources
      (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    ∃ k : I, CurrentConnected (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentLeft sites k) (lpReplicaCurrentRight sites k) := by
  apply lpReplicaCurrent_exists_connectedSeam_of_odd_sources G sites m
  rw [hsrc]
  exact lpReplica_offdiagSource_left_odd sites hsite hij



theorem lpReplicaCurrent_exists_positiveSeam_of_offdiagSource
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hsrc : StatMech.Sharpness.sources
      (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    ∃ k : I, 0 < (ofEdgeFun (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentSeamEdge sites k) := by
  apply lpReplicaCurrent_exists_positiveSeam_of_odd_sources G sites m
  rw [hsrc]
  exact lpReplica_offdiagSource_left_odd sites hsite hij

end

end StatMech.Ising
