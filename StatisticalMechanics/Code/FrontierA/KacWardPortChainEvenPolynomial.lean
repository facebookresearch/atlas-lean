/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPortChainGeneral
import Code.FrontierA.KacWardStar










open scoped BigOperators

namespace StatMech.FrontierA

open Finset SimpleGraph
open StatMech.Ising


noncomputable def kwDartEdgeBitValue
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) : Sym2 V -> Fin 2 :=
  Sym2.lift <| ⟨fun v w => if h : G.Adj v w then b.1 ⟨(v, w), h⟩ else 0, by
    intro v w
    dsimp only
    by_cases h : G.Adj v w
    · rw [dif_pos h, dif_pos h.symm]
      exact (b.2 ⟨(v, w), h⟩).symm
    · rw [dif_neg h, dif_neg (fun hwv => h hwv.symm)]⟩

@[simp] theorem kwDartEdgeBitValue_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (d : G.Dart) :
    kwDartEdgeBitValue G b d.edge = b.1 d := by
  rcases d with ⟨⟨v, w⟩, hvw⟩
  simp [kwDartEdgeBitValue, SimpleGraph.Dart.edge, hvw]


noncomputable def kwDartEdgeBitsFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun edge => kwDartEdgeBitValue G b edge = 1

@[simp] theorem mem_kwDartEdgeBitsFinset_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (d : G.Dart) :
    d.edge ∈ kwDartEdgeBitsFinset G b ↔ b.1 d = 1 := by
  simp [kwDartEdgeBitsFinset]


def kwFinsetDartEdgeBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 V)) : KWDartEdgeBits G :=
  ⟨fun d => if d.edge ∈ F then 1 else 0, by
    intro d
    change (if d.symm.edge ∈ F then 1 else 0) =
      if d.edge ∈ F then 1 else 0
    rw [d.edge_symm]⟩

@[simp] theorem kwFinsetDartEdgeBits_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 V)) (d : G.Dart) :
    (kwFinsetDartEdgeBits G F).1 d = (if d.edge ∈ F then 1 else 0) :=
  rfl

theorem kwDartEdgeBitsFinset_finset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    kwDartEdgeBitsFinset G (kwFinsetDartEdgeBits G F) = F := by
  ext edge
  induction edge using Sym2.ind with
  | _ v w =>
    constructor
    · simp only [kwDartEdgeBitsFinset, Finset.mem_filter]
      intro h
      have hvw : G.Adj v w := by simpa using h.1
      simpa [kwDartEdgeBitValue, hvw] using h.2
    · intro hedge
      have hgraph := hF hedge
      simp only [kwDartEdgeBitsFinset, Finset.mem_filter]
      refine ⟨hgraph, ?_⟩
      have hvw : G.Adj v w := by simpa using hgraph
      simp [kwDartEdgeBitValue, hvw, hedge]

theorem kwFinsetDartEdgeBits_bitsFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) :
    kwFinsetDartEdgeBits G (kwDartEdgeBitsFinset G b) = b := by
  apply Subtype.ext
  funext d
  simp only [kwFinsetDartEdgeBits_apply, mem_kwDartEdgeBitsFinset_iff]
  have h : b.1 d = 0 ∨ b.1 d = 1 := by omega
  rcases h with h | h <;> simp [h]



theorem kw_incidenceFinset_eq_image_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.incidenceFinset v = (G.neighborFinset v).image (fun w => s(v, w)) := by
  ext edge
  induction edge using Sym2.inductionOn with
  | _ a b =>
      simp only [SimpleGraph.mem_incidenceFinset,
        SimpleGraph.mk'_mem_incidenceSet_iff, Finset.mem_image,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hab, rfl | rfl⟩
        · exact ⟨b, hab, rfl⟩
        · exact ⟨a, hab.symm, Sym2.eq_swap⟩
      · rintro ⟨w, hvw, heq⟩
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨hva, hwb⟩ | ⟨hvb, hwa⟩
        · subst a
          subst b
          exact ⟨hvw, Or.inl rfl⟩
        · subst a
          subst b
          exact ⟨hvw.symm, Or.inr rfl⟩

theorem kw_neighborEdge_injective
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v : V) :
    Set.InjOn (fun w => s(v, w)) (G.neighborSet v) := by
  intro a ha b hb heq
  rw [Sym2.eq_iff] at heq
  rcases heq with h | h
  · exact h.2
  · exfalso
    have hva : G.Adj v a := ha
    rw [h.2] at hva
    exact G.loopless.irrefl v hva

theorem kw_incCount_filter_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : Sym2 V → Prop) [DecidablePred Q] (v : V) :
    incCount (G.edgeFinset.filter Q) v =
      ((G.incidenceFinset v).filter Q).card := by
  unfold incCount
  rw [SimpleGraph.incidenceFinset_eq_filter]
  congr 1
  ext edge
  simp only [Finset.mem_filter]
  tauto

theorem kw_cast_incCount_filter_eq_neighbor_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : Sym2 V → Prop) [DecidablePred Q] (v : V) :
    ((incCount (G.edgeFinset.filter Q) v : ℕ) : ZMod 2) =
      ∑ w ∈ G.neighborFinset v,
        if Q s(v, w) then (1 : ZMod 2) else 0 := by
  rw [kw_incCount_filter_edgeFinset, Finset.natCast_card_filter,
    kw_incidenceFinset_eq_image_neighborFinset, Finset.sum_image]
  intro a ha b hb hab
  apply kw_neighborEdge_injective G v
  · exact (SimpleGraph.mem_neighborFinset G v a).mp ha
  · exact (SimpleGraph.mem_neighborFinset G v b).mp hb
  · exact hab

@[simp] theorem kw_fin2_indicator_eq (a : Fin 2) :
    (if a = 1 then (1 : Fin 2) else 0) = a := by
  have h : a = 0 ∨ a = 1 := by omega
  rcases h with h | h <;> simp [h]

@[simp] theorem kw_zmod2_indicator_eq (a : Fin 2) :
    (if a = 1 then (1 : ZMod 2) else 0) = a := by
  fin_cases a <;> decide


def kwNeighborEquivOutgoingDart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.neighborSet v ≃ KWOutgoingDart (G := G) v where
  toFun w := ⟨⟨(v, w.1), w.2⟩, rfl⟩
  invFun d := ⟨d.1.snd, by
    change G.Adj v d.1.snd
    simpa [d.2] using d.1.adj⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv d := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    exact Prod.ext d.2.symm rfl

theorem kw_externalPortBits_sum_eq_neighbor_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (v : V) :
    (∑ i : Fin (Fintype.card (KWOutgoingDart (G := G) v)),
        kwExternalPortBits G b ⟨v, i⟩) =
      ∑ w ∈ G.neighborFinset v, kwDartEdgeBitValue G b s(v, w) := by
  calc
    (∑ i : Fin (Fintype.card (KWOutgoingDart (G := G) v)),
        kwExternalPortBits G b ⟨v, i⟩) =
        ∑ d : KWOutgoingDart (G := G) v, b.1 d.1 := by
      simpa only [kwExternalPortBits, kwDartOfPort, kwDartPortEquiv,
        Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
        Equiv.sigmaFiberEquiv_apply] using
          (Equiv.sum_comp
            (Fintype.equivFin (KWOutgoingDart (G := G) v)).symm
            (fun d : KWOutgoingDart (G := G) v => b.1 d.1))
    _ = ∑ w : G.neighborSet v,
        b.1 (kwNeighborEquivOutgoingDart G v w).1 := by
      exact (Equiv.sum_comp (kwNeighborEquivOutgoingDart G v)
        (fun d : KWOutgoingDart (G := G) v => b.1 d.1)).symm
    _ = ∑ w : G.neighborSet v, kwDartEdgeBitValue G b s(v, w.1) := by
      apply Finset.sum_congr rfl
      intro w _
      change b.1 ⟨(v, w.1), w.2⟩ = _
      rw [← kwDartEdgeBitValue_edge G b ⟨(v, w.1), w.2⟩]
      rfl
    _ = ∑ w ∈ G.neighborFinset v,
        kwDartEdgeBitValue G b s(v, w) := by
      exact (Finset.sum_subtype (p := fun w => G.Adj v w)
        (G.neighborFinset v)
        (fun w => SimpleGraph.mem_neighborFinset G v w)
        (fun w => kwDartEdgeBitValue G b s(v, w))).symm



theorem kwDartEdgeBitsFinset_even_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) :
    IsEvenSubgraph (kwDartEdgeBitsFinset G b) ↔
      KWOriginalPortEven G b := by
  constructor
  · intro heven v
    rw [kw_externalPortBits_sum_eq_neighbor_sum G b v]
    have hcast : ((incCount (kwDartEdgeBitsFinset G b) v : ℕ) : ZMod 2) = 0 := by
      apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr
      exact even_iff_two_dvd.mp (heven v)
    have hsum := kw_cast_incCount_filter_eq_neighbor_sum G
      (fun edge => kwDartEdgeBitValue G b edge = 1) v
    change ((incCount (kwDartEdgeBitsFinset G b) v : ℕ) : ZMod 2) = _ at hsum
    rw [hcast] at hsum
    simpa only [kw_zmod2_indicator_eq] using hsum.symm
  · intro hport v
    apply even_iff_two_dvd.mpr
    apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp
    have hneighbor : (∑ w ∈ G.neighborFinset v,
        kwDartEdgeBitValue G b s(v, w)) = 0 := by
      rw [← kw_externalPortBits_sum_eq_neighbor_sum G b v]
      exact hport v
    have hsum := kw_cast_incCount_filter_eq_neighbor_sum G
      (fun edge => kwDartEdgeBitValue G b edge = 1) v
    change ((incCount (kwDartEdgeBitsFinset G b) v : ℕ) : ZMod 2) = _ at hsum
    rw [hsum]
    simpa only [kw_zmod2_indicator_eq] using hneighbor




noncomputable def kwOrderedInternalNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (p : KWDartPort G) : Finset (KWDartPort G) :=
  Finset.univ.filter fun q => p.1 = q.1 ∧
    (kwOrderedPortRank order p + 1 = kwOrderedPortRank order q ∨
      kwOrderedPortRank order q + 1 = kwOrderedPortRank order p)

@[simp] theorem mem_kwOrderedInternalNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (p q : KWDartPort G) :
    q ∈ kwOrderedInternalNeighborFinset G order p ↔
      p.1 = q.1 ∧
        (kwOrderedPortRank order p + 1 = kwOrderedPortRank order q ∨
          kwOrderedPortRank order q + 1 = kwOrderedPortRank order p) := by
  simp [kwOrderedInternalNeighborFinset]


noncomputable def kwOrderedMatchingNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : KWDartPort G) : KWDartPort G :=
  kwPortOfDart G (kwDartOfPort G p).symm

@[simp] theorem kwDartOfPort_matchingNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : KWDartPort G) :
    kwDartOfPort G (kwOrderedMatchingNeighbor G p) =
      (kwDartOfPort G p).symm := by
  simp [kwOrderedMatchingNeighbor]

theorem kwOrderedMatchingNeighbor_not_mem_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (p : KWDartPort G) :
    kwOrderedMatchingNeighbor G p ∉
      kwOrderedInternalNeighborFinset G order p := by
  intro hmem
  rw [mem_kwOrderedInternalNeighborFinset] at hmem
  have hfirst : (kwDartOfPort G p).snd =
      (kwOrderedMatchingNeighbor G p).1 := by
    simpa using kwDartOfPort_fst G (kwOrderedMatchingNeighbor G p)
  apply (kwDartOfPort G p).fst_ne_snd
  calc
    (kwDartOfPort G p).fst = p.1 := kwDartOfPort_fst G p
    _ = (kwOrderedMatchingNeighbor G p).1 := hmem.1
    _ = (kwDartOfPort G p).snd := hfirst.symm

theorem kwOrderedSplit_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (p : KWDartPort G) :
    (kwOrderedDartPortSplitGraph G order).neighborFinset p =
      insert (kwOrderedMatchingNeighbor G p)
        (kwOrderedInternalNeighborFinset G order p) := by
  ext q
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
    mem_kwOrderedInternalNeighborFinset,
    kwOrderedDartPortSplitGraph_adj]
  constructor
  · rintro (hext | hint)
    · left
      apply kwDartOfPort_injective G
      rw [hext]
      simp
    · exact Or.inr hint
  · rintro (rfl | hint)
    · left
      simp
    · exact Or.inr hint


noncomputable def kwOrderedSplitEdgeBitValue
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) : Sym2 (KWDartPort G) → Fin 2 :=
  Sym2.lift <| ⟨fun p q =>
    if h : (kwOrderedDartPortSplitGraph G order).Adj p q then
      kwOrderedPortSplitAdjBit G order b y p q else 0, by
    intro p q
    dsimp only
    by_cases h : (kwOrderedDartPortSplitGraph G order).Adj p q
    · rw [dif_pos h, dif_pos h.symm]
      exact kwOrderedPortSplitAdjBit_symm G order b y h
    · rw [dif_neg h, dif_neg (fun hqp => h hqp.symm)]⟩

@[simp] theorem kwOrderedSplitEdgeBitValue_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G)
    (d : (kwOrderedDartPortSplitGraph G order).Dart) :
    kwOrderedSplitEdgeBitValue G order b y d.edge =
      kwOrderedPortSplitAdjBit G order b y d.fst d.snd := by
  rcases d with ⟨⟨p, q⟩, hpq⟩
  change (if h : (kwOrderedDartPortSplitGraph G order).Adj p q then
      kwOrderedPortSplitAdjBit G order b y p q else 0) = _
  rw [dif_pos hpq]


noncomputable def kwOrderedSplitEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) : Finset (Sym2 (KWDartPort G)) :=
  (kwOrderedDartPortSplitGraph G order).edgeFinset.filter fun edge =>
    kwOrderedSplitEdgeBitValue G order b y edge = 1

@[simp] theorem mem_kwOrderedSplitEdges_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G)
    (d : (kwOrderedDartPortSplitGraph G order).Dart) :
    d.edge ∈ kwOrderedSplitEdges G order b y ↔
      kwOrderedPortSplitAdjBit G order b y d.fst d.snd = 1 := by
  simp [kwOrderedSplitEdges]


theorem kw_fin_sum_adjacent {n : ℕ} (i : Fin n) (left right : Fin 2) :
    (∑ j ∈ (Finset.univ.filter fun j : Fin n =>
        i.val + 1 = j.val ∨ j.val + 1 = i.val),
      if j.val + 1 = i.val then left else right) =
      (if i.val = 0 then 0 else left) +
        (if i.val + 1 = n then 0 else right) := by
  classical
  by_cases hzero : i.val = 0
  · by_cases hlast : i.val + 1 = n
    · have hempty : (Finset.univ.filter fun j : Fin n =>
          i.val + 1 = j.val ∨ j.val + 1 = i.val) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp
        omega
      rw [hempty]
      rw [Finset.sum_empty, if_pos hzero, if_pos hlast, add_zero]
    · have hsucc : i.val + 1 < n := by omega
      let next : Fin n := ⟨i.val + 1, hsucc⟩
      have hsingle : (Finset.univ.filter fun j : Fin n =>
          i.val + 1 = j.val ∨ j.val + 1 = i.val) = {next} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · intro h
          apply Fin.ext
          rcases h with h | h <;> dsimp only [next] <;> omega
        · rintro rfl
          exact Or.inl rfl
      rw [hsingle, Finset.sum_singleton]
      have hnotPred : ¬(next.val + 1 = i.val) := by
        dsimp only [next]
        omega
      rw [if_neg hnotPred, if_pos hzero, if_neg hlast, zero_add]
  · have hpos : 0 < i.val := by omega
    let previous : Fin n := ⟨i.val - 1, by omega⟩
    by_cases hlast : i.val + 1 = n
    · have hsingle : (Finset.univ.filter fun j : Fin n =>
          i.val + 1 = j.val ∨ j.val + 1 = i.val) = {previous} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · intro h
          apply Fin.ext
          rcases h with h | h <;> dsimp only [previous] <;> omega
        · rintro rfl
          right
          dsimp only [previous]
          omega
      rw [hsingle, Finset.sum_singleton]
      have hpred : previous.val + 1 = i.val := by
        dsimp only [previous]
        omega
      rw [if_pos hpred, if_neg hzero, if_pos hlast, add_zero]
    · have hsucc : i.val + 1 < n := by omega
      let next : Fin n := ⟨i.val + 1, hsucc⟩
      have hne : previous ≠ next := by
        intro h
        have := congrArg Fin.val h
        dsimp only [previous, next] at this
        omega
      have hpair : (Finset.univ.filter fun j : Fin n =>
          i.val + 1 = j.val ∨ j.val + 1 = i.val) =
          {previous, next} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h
          rcases h with h | h
          · right
            apply Fin.ext
            simpa [next] using h.symm
          · left
            apply Fin.ext
            dsimp only [previous]
            omega
        · rintro (rfl | rfl)
          · right
            dsimp only [previous]
            omega
          · left
            rfl
      have hpred : previous.val + 1 = i.val := by
        dsimp only [previous]
        omega
      have hnotPred : ¬(next.val + 1 = i.val) := by
        dsimp only [next]
        omega
      rw [hpair, Finset.sum_insert (by simpa using hne),
        Finset.sum_singleton, if_pos hpred, if_neg hnotPred,
        if_neg hzero, if_neg hlast]


theorem kwOrderedInternalNeighborFinset_eq_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (p : KWDartPort G) :
    kwOrderedInternalNeighborFinset G order p =
      (Finset.univ.filter fun j :
        Fin (Fintype.card (KWOutgoingDart (G := G) p.1)) =>
          kwOrderedPortRank order p + 1 = j.val ∨
            j.val + 1 = kwOrderedPortRank order p).image
        (kwPortAtOrderedRank order p.1) := by
  ext q
  rw [mem_kwOrderedInternalNeighborFinset, Finset.mem_image]
  constructor
  · rintro ⟨hfirst, hrank⟩
    let j : Fin (Fintype.card (KWOutgoingDart (G := G) p.1)) :=
      ⟨kwOrderedPortRank order q, by
        change (order q.1 q.2).val < _
        simpa [hfirst] using (order q.1 q.2).isLt⟩
    refine ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [j] using hrank
    · rcases p with ⟨v, i⟩
      rcases q with ⟨w, k⟩
      dsimp only at hfirst ⊢
      subst w
      simp [kwPortAtOrderedRank, j, kwOrderedPortRank]
  · rintro ⟨j, hj, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    constructor
    · rfl
    · have hrank : kwOrderedPortRank order
          (kwPortAtOrderedRank order p.1 j) = j.val := by
        change ((order p.1) ((order p.1).symm j)).val = j.val
        exact congrArg Fin.val ((order p.1).apply_symm_apply j)
      rw [hrank]
      exact hj

theorem kwPortAtOrderedRank_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (v : V) :
    Function.Injective (kwPortAtOrderedRank order v) := by
  intro i j h
  have hsecond : (order v).symm i = (order v).symm j :=
    HEq.eq (Sigma.ext_iff.mp h).2
  exact (order v).symm.injective hsecond



theorem kwOrderedInternalNeighbor_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) (p : KWDartPort G) :
    (∑ q ∈ kwOrderedInternalNeighborFinset G order p,
        kwOrderedPortSplitAdjBit G order b y p q) =
      (if kwOrderedPortRank order p = 0 then 0
        else y p.1 (order p.1 p.2).castSucc) +
      (if kwOrderedPortRank order p + 1 =
          Fintype.card (KWOutgoingDart (G := G) p.1) then 0
        else y p.1 (order p.1 p.2).succ) := by
  classical
  rw [kwOrderedInternalNeighborFinset_eq_image]
  rw [Finset.sum_image]
  · let i := order p.1 p.2
    have hrankp : kwOrderedPortRank order p = i.val := rfl
    have hterm (j : Fin (Fintype.card (KWOutgoingDart (G := G) p.1)))
        (hj : j ∈ Finset.univ.filter fun j =>
          kwOrderedPortRank order p + 1 = j.val ∨
            j.val + 1 = kwOrderedPortRank order p) :
        kwOrderedPortSplitAdjBit G order b y p
            (kwPortAtOrderedRank order p.1 j) =
          if j.val + 1 = i.val then y p.1 i.castSucc
          else y p.1 i.succ := by
      have hext : ¬kwDartOfPort G (kwPortAtOrderedRank order p.1 j) =
          (kwDartOfPort G p).symm := by
        intro h
        have hfirst : p.1 = (kwDartOfPort G p).snd := by
          calc
            p.1 = (kwPortAtOrderedRank order p.1 j).1 := rfl
            _ = (kwDartOfPort G
                (kwPortAtOrderedRank order p.1 j)).fst :=
              (kwDartOfPort_fst G _).symm
            _ = ((kwDartOfPort G p).symm).fst :=
              congrArg (fun d : G.Dart => d.fst) h
            _ = (kwDartOfPort G p).snd := rfl
        apply (kwDartOfPort G p).fst_ne_snd
        calc
          (kwDartOfPort G p).fst = p.1 := kwDartOfPort_fst G p
          _ = (kwDartOfPort G p).snd := hfirst
      unfold kwOrderedPortSplitAdjBit
      rw [if_neg hext]
      have hrankj : kwOrderedPortRank order
          (kwPortAtOrderedRank order p.1 j) = j.val := by
        change ((order p.1) ((order p.1).symm j)).val = j.val
        exact congrArg Fin.val ((order p.1).apply_symm_apply j)
      rw [hrankj, hrankp]
    calc
      (∑ x ∈ Finset.univ.filter fun j :
          Fin (Fintype.card (KWOutgoingDart (G := G) p.1)) =>
            kwOrderedPortRank order p + 1 = j.val ∨
              j.val + 1 = kwOrderedPortRank order p,
          kwOrderedPortSplitAdjBit G order b y p
            (kwPortAtOrderedRank order p.1 x)) =
          ∑ x ∈ Finset.univ.filter fun j :
            Fin (Fintype.card (KWOutgoingDart (G := G) p.1)) =>
              i.val + 1 = j.val ∨ j.val + 1 = i.val,
            if x.val + 1 = i.val then y p.1 i.castSucc
            else y p.1 i.succ := by
        apply Finset.sum_congr
        · ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hrankp]
        · intro j hj
          apply hterm j
          simpa [hrankp] using hj
      _ = (if i.val = 0 then 0 else y p.1 i.castSucc) +
          (if i.val + 1 = Fintype.card
              (KWOutgoingDart (G := G) p.1) then 0
            else y p.1 i.succ) :=
        kw_fin_sum_adjacent i (y p.1 i.castSucc) (y p.1 i.succ)
      _ = _ := by rfl
  · intro a ha c hc hac
    exact kwPortAtOrderedRank_injective order p.1 hac

@[simp] theorem kwOrderedPortSplitAdjBit_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) (p : KWDartPort G) :
    kwOrderedPortSplitAdjBit G order b y p
      (kwOrderedMatchingNeighbor G p) = kwExternalPortBits G b p := by
  unfold kwOrderedPortSplitAdjBit
  rw [if_pos]
  simp [kwOrderedMatchingNeighbor]


theorem kwOrderedPortSplit_neighbor_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) (p : KWDartPort G) :
    (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
      kwOrderedPortSplitAdjBit G order b y p q) =
        kwOrderedPortSplitIncidence G order b y p := by
  rw [kwOrderedSplit_neighborFinset,
    Finset.sum_insert (kwOrderedMatchingNeighbor_not_mem_internal G order p),
    kwOrderedPortSplitAdjBit_matching,
    kwOrderedInternalNeighbor_sum]
  unfold kwOrderedPortSplitIncidence
  abel



theorem kwOrderedSplitEdges_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G)
    (hy : KWOrderedGlobalPortChainEven G order b y) :
    kwOrderedSplitEdges G order b y ∈
      evenSubgraphs (kwOrderedDartPortSplitGraph G order) := by
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact Finset.filter_subset _ _
  · intro p
    apply even_iff_two_dvd.mpr
    apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp
    have hsum := kw_cast_incCount_filter_eq_neighbor_sum
      (kwOrderedDartPortSplitGraph G order)
      (fun edge => kwOrderedSplitEdgeBitValue G order b y edge = 1) p
    change ((incCount (kwOrderedSplitEdges G order b y) p : ℕ) : ZMod 2) = _
      at hsum
    rw [hsum]
    simp only [kw_zmod2_indicator_eq]
    have hedgeSum :
        (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
          kwOrderedSplitEdgeBitValue G order b y s(p, q)) =
        ∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
          kwOrderedPortSplitAdjBit G order b y p q := by
      apply Finset.sum_congr rfl
      intro q hq
      let d : (kwOrderedDartPortSplitGraph G order).Dart :=
        ⟨(p, q), (SimpleGraph.mem_neighborFinset _ _ _).mp hq⟩
      exact kwOrderedSplitEdgeBitValue_edge G order b y d
    have hbits :
        (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
          kwOrderedPortSplitAdjBit G order b y p q) = 0 := by
      rw [kwOrderedPortSplit_neighbor_sum]
      exact kwOrderedPortSplitIncidence_eq_zero_of_globalEven G order b y hy p
    have hedgeFin :
        (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
          kwOrderedSplitEdgeBitValue G order b y s(p, q)) = 0 :=
      hedgeSum.trans hbits
    exact_mod_cast hedgeFin




noncomputable def kwOrderedSplitFinsetExternalBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 (KWDartPort G))) : KWDartEdgeBits G :=
  ⟨fun d => if s(kwPortOfDart G d, kwPortOfDart G d.symm) ∈ F then 1 else 0, by
    intro d
    have hedge : s(kwPortOfDart G d.symm,
        kwPortOfDart G d.symm.symm) =
        s(kwPortOfDart G d, kwPortOfDart G d.symm) := by
      rw [d.symm_symm]
      exact Sym2.eq_swap
    change (if s(kwPortOfDart G d.symm,
        kwPortOfDart G d.symm.symm) ∈ F then 1 else 0) =
      if s(kwPortOfDart G d, kwPortOfDart G d.symm) ∈ F then 1 else 0
    rw [hedge]⟩



noncomputable def kwOrderedSplitFinsetChainField
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G))) : KWPortChainField G :=
  fun v k =>
    if hzero : k = 0 then 0
    else if hlast : k = Fin.last
        (Fintype.card (KWOutgoingDart (G := G) v)) then 0
    else if s(kwPortAtOrderedRank order v (k.pred hzero),
        kwPortAtOrderedRank order v (k.castPred hlast)) ∈ F then 1 else 0

@[simp] theorem kwOrderedSplitFinsetChainField_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G))) (v : V) :
    kwOrderedSplitFinsetChainField G order F v 0 = 0 := by
  simp [kwOrderedSplitFinsetChainField]

@[simp] theorem kwOrderedSplitFinsetChainField_last
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G))) (v : V) :
    kwOrderedSplitFinsetChainField G order F v
      (Fin.last (Fintype.card (KWOutgoingDart (G := G) v))) = 0 := by
  by_cases h : Fin.last (Fintype.card (KWOutgoingDart (G := G) v)) = 0
  · rw [h]
    exact kwOrderedSplitFinsetChainField_zero G order F v
  · simp [kwOrderedSplitFinsetChainField, h]

@[simp] theorem kwExternalPortBits_extract
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 (KWDartPort G))) (p : KWDartPort G) :
    kwExternalPortBits G (kwOrderedSplitFinsetExternalBits G F) p =
      if s(p, kwOrderedMatchingNeighbor G p) ∈ F then 1 else 0 := by
  unfold kwExternalPortBits kwOrderedSplitFinsetExternalBits
  simp only [kwPortOfDart_dartOfPort]
  rfl

theorem kwOrderedSplitFinsetChainField_castSucc
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G))) (v : V)
    (i : Fin (Fintype.card (KWOutgoingDart (G := G) v)))
    (hpos : 0 < i.val) :
    kwOrderedSplitFinsetChainField G order F v i.castSucc =
      if s(kwPortAtOrderedRank order v
          ⟨i.val - 1, by omega⟩,
        kwPortAtOrderedRank order v i) ∈ F then 1 else 0 := by
  unfold kwOrderedSplitFinsetChainField
  have hzero : i.castSucc ≠ 0 := by
    apply Fin.ne_of_val_ne
    simp only [Fin.val_castSucc, Fin.val_zero]
    omega
  have hlast : i.castSucc ≠ Fin.last
      (Fintype.card (KWOutgoingDart (G := G) v)) := by
    apply Fin.ne_of_val_ne
    simp only [Fin.val_castSucc, Fin.val_last]
    exact Nat.ne_of_lt i.isLt
  rw [dif_neg hzero, dif_neg hlast]
  congr 3

theorem kwOrderedSplitFinsetChainField_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G))) (v : V)
    (i : Fin (Fintype.card (KWOutgoingDart (G := G) v)))
    (hnext : i.val + 1 < Fintype.card (KWOutgoingDart (G := G) v)) :
    kwOrderedSplitFinsetChainField G order F v i.succ =
      if s(kwPortAtOrderedRank order v i,
        kwPortAtOrderedRank order v ⟨i.val + 1, hnext⟩) ∈ F
      then 1 else 0 := by
  unfold kwOrderedSplitFinsetChainField
  have hzero : i.succ ≠ 0 := by
    apply Fin.ne_of_val_ne
    simp
  have hlast : i.succ ≠ Fin.last
      (Fintype.card (KWOutgoingDart (G := G) v)) := by
    apply Fin.ne_of_val_ne
    simp only [Fin.val_succ, Fin.val_last]
    exact Nat.ne_of_lt hnext
  rw [dif_neg hzero, dif_neg hlast]
  congr 3

theorem kw_evenSubgraph_neighbor_sum_zero
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (F : Finset (Sym2 W)) (hF : F ∈ evenSubgraphs H) (v : W) :
    ∑ w ∈ H.neighborFinset v,
      (if s(v, w) ∈ F then (1 : ZMod 2) else 0) = 0 := by
  have hdata := hF
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  have hFeq : F = H.edgeFinset.filter (fun edge => edge ∈ F) := by
    ext edge
    simp only [Finset.mem_filter]
    constructor
    · intro hedge
      exact ⟨hdata.1 hedge, hedge⟩
    · exact And.right
  have hcast : ((incCount F v : ℕ) : ZMod 2) = 0 := by
    apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr
    exact even_iff_two_dvd.mp (hdata.2 v)
  have hsum := kw_cast_incCount_filter_eq_neighbor_sum H
    (fun edge => edge ∈ F) v
  rw [← hFeq, hcast] at hsum
  exact hsum.symm



theorem kwOrderedPortSplitAdjBit_extract
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G))) {p q : KWDartPort G}
    (hpq : (kwOrderedDartPortSplitGraph G order).Adj p q) :
    kwOrderedPortSplitAdjBit G order
      (kwOrderedSplitFinsetExternalBits G F)
      (kwOrderedSplitFinsetChainField G order F) p q =
        if s(p, q) ∈ F then 1 else 0 := by
  rw [kwOrderedDartPortSplitGraph_adj] at hpq
  rcases hpq with hext | hint
  · have hq : q = kwOrderedMatchingNeighbor G p := by
      apply kwDartOfPort_injective G
      rw [hext]
      simp
    subst q
    rw [kwOrderedPortSplitAdjBit_matching, kwExternalPortBits_extract]
  · have hnotext : ¬kwDartOfPort G q = (kwDartOfPort G p).symm := by
      intro hext
      have hfirst := congrArg (fun d : G.Dart => d.fst) hext
      have hpfirst := kwDartOfPort_fst G p
      have hqfirst := kwDartOfPort_fst G q
      apply (kwDartOfPort G p).fst_ne_snd
      calc
        (kwDartOfPort G p).fst = p.1 := hpfirst
        _ = q.1 := hint.1
        _ = (kwDartOfPort G q).fst := hqfirst.symm
        _ = ((kwDartOfPort G p).symm).fst := hfirst
        _ = (kwDartOfPort G p).snd := rfl
    unfold kwOrderedPortSplitAdjBit
    rw [if_neg hnotext]
    let i := order p.1 p.2
    have hrankp : kwOrderedPortRank order p = i.val := rfl
    have hp : p = kwPortAtOrderedRank order p.1 i := by
      apply kwDartPort_eq_of_fst_of_orderRank
        (p := p) (q := kwPortAtOrderedRank order p.1 i) order rfl
      change i.val = ((order p.1) ((order p.1).symm i)).val
      rw [(order p.1).apply_symm_apply]
    rcases hint.2 with hsucc | hpred
    · have hnext : i.val + 1 <
          Fintype.card (KWOutgoingDart (G := G) p.1) := by
        have hqbound : kwOrderedPortRank order q <
            Fintype.card (KWOutgoingDart (G := G) q.1) :=
          (order q.1 q.2).isLt
        rw [← hrankp, hsucc]
        simpa [hint.1] using hqbound
      have hq : q = kwPortAtOrderedRank order p.1
          ⟨i.val + 1, hnext⟩ := by
        apply kwDartPort_eq_of_fst_of_orderRank
          (p := q) (q := kwPortAtOrderedRank order p.1
            ⟨i.val + 1, hnext⟩) order hint.1.symm
        change kwOrderedPortRank order q =
          ((order p.1) ((order p.1).symm ⟨i.val + 1, hnext⟩)).val
        rw [(order p.1).apply_symm_apply]
        change kwOrderedPortRank order q = i.val + 1
        omega
      have hnotpred : ¬(kwOrderedPortRank order q + 1 =
          kwOrderedPortRank order p) := by omega
      rw [if_neg hnotpred,
        kwOrderedSplitFinsetChainField_succ G order F p.1 i hnext]
      rw [← hq]
      rw [← hp]
    · have hpos : 0 < i.val := by
        rw [← hrankp, ← hpred]
        omega
      have hq : q = kwPortAtOrderedRank order p.1
          ⟨i.val - 1, by omega⟩ := by
        apply kwDartPort_eq_of_fst_of_orderRank
          (p := q) (q := kwPortAtOrderedRank order p.1
            ⟨i.val - 1, by omega⟩) order hint.1.symm
        change kwOrderedPortRank order q =
          ((order p.1) ((order p.1).symm ⟨i.val - 1, by omega⟩)).val
        rw [(order p.1).apply_symm_apply]
        change kwOrderedPortRank order q = i.val - 1
        omega
      rw [if_pos hpred,
        kwOrderedSplitFinsetChainField_castSucc G order F p.1 i hpos]
      rw [← hq, Sym2.eq_swap]
      rw [← hp]

theorem kw_fin2_solve_recurrence (external left right : Fin 2)
    (h : external + left + right = 0) :
    right = left + external := by
  calc
    right = right + 0 := (add_zero _).symm
    _ = right + (external + left + right) := by rw [h]
    _ = (right + right) + (external + left) := by ac_rfl
    _ = external + left := by rw [kw_fin_two_self_add, zero_add]
    _ = left + external := add_comm _ _



theorem kwOrderedSplitFinset_globalEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G)))
    (hF : F ∈ evenSubgraphs (kwOrderedDartPortSplitGraph G order)) :
    KWOrderedGlobalPortChainEven G order
      (kwOrderedSplitFinsetExternalBits G F)
      (kwOrderedSplitFinsetChainField G order F) := by
  intro v
  let b := kwOrderedSplitFinsetExternalBits G F
  let y := kwOrderedSplitFinsetChainField G order F
  refine ⟨kwOrderedSplitFinsetChainField_zero G order F v, ?_,
    kwOrderedSplitFinsetChainField_last G order F v⟩
  intro i
  let p := kwPortAtOrderedRank order v i
  have hsumZ := kw_evenSubgraph_neighbor_sum_zero
    (kwOrderedDartPortSplitGraph G order) F hF p
  have hsumFin :
      (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
        (if s(p, q) ∈ F then (1 : Fin 2) else 0)) = 0 := by
    simpa only using hsumZ
  have hadjEq :
      (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
        kwOrderedPortSplitAdjBit G order b y p q) =
      ∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
        (if s(p, q) ∈ F then (1 : Fin 2) else 0) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact kwOrderedPortSplitAdjBit_extract G order F
      ((SimpleGraph.mem_neighborFinset _ _ _).mp hq)
  have hadj :
      (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
        kwOrderedPortSplitAdjBit G order b y p q) = 0 :=
    hadjEq.trans hsumFin
  have hinc : kwOrderedPortSplitIncidence G order b y p = 0 := by
    rw [← kwOrderedPortSplit_neighbor_sum]
    exact hadj
  unfold kwOrderedPortSplitIncidence at hinc
  dsimp only [p, kwPortAtOrderedRank, kwOrderedPortRank] at hinc
  let j := (order v) ((order v).symm i)
  have hj : j = i := (order v).apply_symm_apply i
  change ((kwExternalPortBits G b (kwPortAtOrderedRank order v i) +
      if j.val = 0 then 0 else y v j.castSucc) +
      if j.val + 1 = Fintype.card (KWOutgoingDart (G := G) v) then 0
      else y v j.succ) = 0 at hinc
  have hleft :
      (if j.val = 0 then 0 else y v j.castSucc) = y v j.castSucc := by
    by_cases hzero : j.val = 0
    · rw [if_pos hzero]
      symm
      have hi : j.castSucc = (0 : Fin
          (Fintype.card (KWOutgoingDart (G := G) v) + 1)) := Fin.ext hzero
      rw [hi]
      exact kwOrderedSplitFinsetChainField_zero G order F v
    · rw [if_neg hzero]
  have hright :
      (if j.val + 1 = Fintype.card (KWOutgoingDart (G := G) v) then 0
        else y v j.succ) = y v j.succ := by
    by_cases hlast : j.val + 1 =
        Fintype.card (KWOutgoingDart (G := G) v)
    · rw [if_pos hlast]
      symm
      have hi : j.succ = Fin.last
          (Fintype.card (KWOutgoingDart (G := G) v)) := Fin.ext hlast
      rw [hi]
      exact kwOrderedSplitFinsetChainField_last G order F v
    · rw [if_neg hlast]
  rw [hleft, hright] at hinc
  have hrec : y v j.succ = y v j.castSucc +
      kwExternalPortBits G b (kwPortAtOrderedRank order v i) :=
    kw_fin2_solve_recurrence _ _ _ hinc
  have hsucc := congrArg (fun k : Fin
      (Fintype.card (KWOutgoingDart (G := G) v)) => y v k.succ) hj
  have hcast := congrArg (fun k : Fin
      (Fintype.card (KWOutgoingDart (G := G) v)) => y v k.castSucc) hj
  change y v i.succ = y v i.castSucc +
    kwExternalPortBits G b (kwPortAtOrderedRank order v i)
  calc
    y v i.succ = y v j.succ := hsucc.symm
    _ = y v j.castSucc +
        kwExternalPortBits G b (kwPortAtOrderedRank order v i) := hrec
    _ = y v i.castSucc +
        kwExternalPortBits G b (kwPortAtOrderedRank order v i) :=
      congrArg (fun z => z +
        kwExternalPortBits G b (kwPortAtOrderedRank order v i)) hcast



theorem kwOrderedSplitEdges_extract
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G)))
    (hF : F ∈ evenSubgraphs (kwOrderedDartPortSplitGraph G order)) :
    kwOrderedSplitEdges G order
      (kwOrderedSplitFinsetExternalBits G F)
      (kwOrderedSplitFinsetChainField G order F) = F := by
  have hdata := hF
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  ext edge
  induction edge using Sym2.inductionOn with
  | _ p q =>
      by_cases hedge : s(p, q) ∈
          (kwOrderedDartPortSplitGraph G order).edgeFinset
      · have hpq : (kwOrderedDartPortSplitGraph G order).Adj p q :=
          SimpleGraph.mem_edgeFinset.mp hedge
        have hbit := kwOrderedPortSplitAdjBit_extract G order F hpq
        have hedgeBit : kwOrderedSplitEdgeBitValue G order
            (kwOrderedSplitFinsetExternalBits G F)
            (kwOrderedSplitFinsetChainField G order F) s(p, q) =
            kwOrderedPortSplitAdjBit G order
              (kwOrderedSplitFinsetExternalBits G F)
              (kwOrderedSplitFinsetChainField G order F) p q := by
          let d : (kwOrderedDartPortSplitGraph G order).Dart :=
            ⟨(p, q), hpq⟩
          exact kwOrderedSplitEdgeBitValue_edge G order _ _ d
        rw [kwOrderedSplitEdges, Finset.mem_filter, and_iff_right hedge,
          hedgeBit, hbit]
        simp
      · have hnotF : s(p, q) ∉ F := fun h => hedge (hdata.1 h)
        simp [kwOrderedSplitEdges, hedge, hnotF]



theorem kwOrderedSplitFinsetExternalBits_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) :
    kwOrderedSplitFinsetExternalBits G
      (kwOrderedSplitEdges G order b y) = b := by
  apply Subtype.ext
  funext d
  let delta := (kwOrderedExternalSplitDartOfDart G order d).1
  change (if s(kwPortOfDart G d, kwPortOfDart G d.symm) ∈
      kwOrderedSplitEdges G order b y then 1 else 0) = b.1 d
  have hedge : s(kwPortOfDart G d, kwPortOfDart G d.symm) = delta.edge := by
    rfl
  rw [hedge]
  simp only [mem_kwOrderedSplitEdges_iff G order b y delta]
  have hmatch : delta.snd = kwOrderedMatchingNeighbor G delta.fst := by
    apply kwDartOfPort_injective G
    simp [delta, kwOrderedMatchingNeighbor]
  rw [hmatch, kwOrderedPortSplitAdjBit_matching]
  have hbit : kwExternalPortBits G b delta.fst = b.1 d := by
    simp [delta, kwExternalPortBits]
  rw [hbit]
  exact kw_fin2_indicator_eq _



def KWActualEvenSubgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {F : Finset (Sym2 V) // F ∈ evenSubgraphs G}

noncomputable instance KWActualEvenSubgraph_fintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype (KWActualEvenSubgraph G) := by
  classical
  unfold KWActualEvenSubgraph
  infer_instance



noncomputable def kwActualEvenSubgraphEquivBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    KWActualEvenSubgraph G ≃ KWOriginalEvenBits G where
  toFun F := ⟨kwFinsetDartEdgeBits G F.1, by
    have hdata := F.2
    change F.1 ∈ G.edgeFinset.powerset.filter IsEvenSubgraph at hdata
    rw [Finset.mem_filter, Finset.mem_powerset] at hdata
    apply (kwDartEdgeBitsFinset_even_iff G _).mp
    rw [kwDartEdgeBitsFinset_finset G F.1 hdata.1]
    exact hdata.2⟩
  invFun b := ⟨kwDartEdgeBitsFinset G b.1, by
    rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _,
      (kwDartEdgeBitsFinset_even_iff G b.1).mpr b.2⟩⟩
  left_inv F := by
    apply Subtype.ext
    have hdata := F.2
    change F.1 ∈ G.edgeFinset.powerset.filter IsEvenSubgraph at hdata
    rw [Finset.mem_filter, Finset.mem_powerset] at hdata
    exact kwDartEdgeBitsFinset_finset G F.1 hdata.1
  right_inv b := by
    apply Subtype.ext
    exact kwFinsetDartEdgeBits_bitsFinset G b.1


def KWOrderedSplitEvenBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :=
  {p : KWDartEdgeBits G × KWPortChainField G //
    KWOrderedGlobalPortChainEven G order p.1 p.2}

noncomputable def kwOrderedCanonicalPortChainField
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (b : KWDartEdgeBits G) : KWPortChainField G :=
  fun v => kwPortChainState
    (fun i => kwExternalPortBits G b (kwPortAtOrderedRank order v i))

theorem kwOrderedCanonicalPortChainField_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (b : KWDartEdgeBits G) (hb : KWOriginalPortEven G b) :
    KWOrderedGlobalPortChainEven G order b
      (kwOrderedCanonicalPortChainField G order b) := by
  intro v
  exact ⟨kwPortChainState_zero _, kwPortChainState_succ _,
    (kwPortChainState_last_eq_zero_iff _).2 (by
      rw [kwOrderedExternalPortBits_sum_eq G order b v, hb v])⟩

theorem kwOrderedPortChainField_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (b : KWDartEdgeBits G) (y z : KWPortChainField G)
    (hy : KWOrderedGlobalPortChainEven G order b y)
    (hz : KWOrderedGlobalPortChainEven G order b z) : y = z := by
  funext v
  exact (kwPortChainState_unique _ (y v) (hy v).1 (hy v).2.1).trans
    (kwPortChainState_unique _ (z v) (hz v).1 (hz v).2.1).symm



noncomputable def kwOriginalEvenBitsEquivOrderedSplit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    KWOriginalEvenBits G ≃ KWOrderedSplitEvenBits G order where
  toFun b := ⟨⟨b.1, kwOrderedCanonicalPortChainField G order b.1⟩,
    kwOrderedCanonicalPortChainField_even G order b.1 b.2⟩
  invFun p := ⟨p.1.1, by
    apply (kwOrderedDartPortSplit_existsUnique_internal_iff G order p.1.1).mpr
    refine ⟨p.1.2, p.2, ?_⟩
    intro z hz
    exact kwOrderedPortChainField_unique G order p.1.1 z p.1.2 hz p.2⟩
  left_inv b := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (kwOrderedPortChainField_unique G order p.1.1
        (kwOrderedCanonicalPortChainField G order p.1.1) p.1.2
        (kwOrderedCanonicalPortChainField_even G order p.1.1
          ((kwOrderedDartPortSplit_existsUnique_internal_iff G order p.1.1).mpr
            ⟨p.1.2, p.2, fun z hz =>
              kwOrderedPortChainField_unique G order p.1.1 z p.1.2 hz p.2⟩))
        p.2)



noncomputable def kwActualOrderedSplitEvenEquivBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    KWActualEvenSubgraph (kwOrderedDartPortSplitGraph G order) ≃
      KWOrderedSplitEvenBits G order where
  toFun F := ⟨⟨kwOrderedSplitFinsetExternalBits G F.1,
      kwOrderedSplitFinsetChainField G order F.1⟩,
    kwOrderedSplitFinset_globalEven G order F.1 F.2⟩
  invFun p := ⟨kwOrderedSplitEdges G order p.1.1 p.1.2,
    kwOrderedSplitEdges_even G order p.1.1 p.1.2 p.2⟩
  left_inv F := by
    apply Subtype.ext
    exact kwOrderedSplitEdges_extract G order F.1 F.2
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact kwOrderedSplitFinsetExternalBits_edges G order p.1.1 p.1.2
    · let F := kwOrderedSplitEdges G order p.1.1 p.1.2
      let y' := kwOrderedSplitFinsetChainField G order F
      have hb : kwOrderedSplitFinsetExternalBits G F = p.1.1 :=
        kwOrderedSplitFinsetExternalBits_edges G order p.1.1 p.1.2
      have hy' : KWOrderedGlobalPortChainEven G order p.1.1 y' := by
        rw [← hb]
        exact kwOrderedSplitFinset_globalEven G order F
          (kwOrderedSplitEdges_even G order p.1.1 p.1.2 p.2)
      exact kwOrderedPortChainField_unique G order p.1.1 y' p.1.2 hy' p.2



noncomputable def kwOrderedSplitEvenSubgraphEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    KWActualEvenSubgraph G ≃
      KWActualEvenSubgraph (kwOrderedDartPortSplitGraph G order) :=
  (kwActualEvenSubgraphEquivBits G).trans
    ((kwOriginalEvenBitsEquivOrderedSplit G order).trans
      (kwActualOrderedSplitEvenEquivBits G order).symm)






def kwOrderedSplitEdgeProjection
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    Sym2 (KWDartPort G) → Sym2 V :=
  Sym2.map Sigma.fst

@[simp] theorem kwOrderedSplitEdgeProjection_mk
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (p q : KWDartPort G) :
    kwOrderedSplitEdgeProjection s(p, q) = s(p.1, q.1) := by
  simp [kwOrderedSplitEdgeProjection]

theorem kwOrderedSplit_external_of_projection_not_diag
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {p q : KWDartPort G}
    (hpq : (kwOrderedDartPortSplitGraph G order).Adj p q)
    (hdiag : ¬(kwOrderedSplitEdgeProjection s(p, q)).IsDiag) :
    kwDartOfPort G q = (kwDartOfPort G p).symm := by
  rw [kwOrderedDartPortSplitGraph_adj] at hpq
  rcases hpq with hext | hint
  · exact hext
  · exfalso
    apply hdiag
    rw [kwOrderedSplitEdgeProjection_mk, Sym2.mk_isDiag_iff]
    exact hint.1

theorem kwDartOfPort_toProd_of_external
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : KWDartPort G}
    (hext : kwDartOfPort G q = (kwDartOfPort G p).symm) :
    (kwDartOfPort G p).toProd = (p.1, q.1) := by
  apply Prod.ext
  · exact kwDartOfPort_fst G p
  · have hfirst := congrArg (fun d : G.Dart => d.fst) hext
    change (kwDartOfPort G q).fst = (kwDartOfPort G p).snd at hfirst
    rw [kwDartOfPort_fst] at hfirst
    exact hfirst.symm

theorem kwOrderedSplitEdgeProjection_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {edge edge' : Sym2 (KWDartPort G)}
    (hedge : edge ∈ (kwOrderedDartPortSplitGraph G order).edgeFinset)
    (hedge' : edge' ∈ (kwOrderedDartPortSplitGraph G order).edgeFinset)
    (hdiag : ¬(kwOrderedSplitEdgeProjection edge).IsDiag)
    (hdiag' : ¬(kwOrderedSplitEdgeProjection edge').IsDiag)
    (heq : kwOrderedSplitEdgeProjection edge =
      kwOrderedSplitEdgeProjection edge') : edge = edge' := by
  induction edge using Sym2.inductionOn with
  | _ p q =>
    induction edge' using Sym2.inductionOn with
    | _ r s =>
      have hpq : (kwOrderedDartPortSplitGraph G order).Adj p q :=
        SimpleGraph.mem_edgeFinset.mp hedge
      have hrs : (kwOrderedDartPortSplitGraph G order).Adj r s :=
        SimpleGraph.mem_edgeFinset.mp hedge'
      have hpqext := kwOrderedSplit_external_of_projection_not_diag
        G order hpq hdiag
      have hrsext := kwOrderedSplit_external_of_projection_not_diag
        G order hrs hdiag'
      rw [kwOrderedSplitEdgeProjection_mk,
        kwOrderedSplitEdgeProjection_mk, Sym2.eq_iff] at heq
      rcases heq with heq | heq
      · have hpr : p = r := by
          apply kwDartOfPort_injective G
          apply SimpleGraph.Dart.ext
          rw [kwDartOfPort_toProd_of_external G hpqext,
            kwDartOfPort_toProd_of_external G hrsext, heq.1, heq.2]
        have hqs : q = s := by
          apply kwDartOfPort_injective G
          rw [hpqext, hrsext, hpr]
        rw [hpr, hqs]
      · have hps : p = s := by
          apply kwDartOfPort_injective G
          apply SimpleGraph.Dart.ext
          rw [kwDartOfPort_toProd_of_external G hpqext]
          have hsrev : kwDartOfPort G r = (kwDartOfPort G s).symm := by
            rw [hrsext]
            exact (kwDartOfPort G r).symm_symm.symm
          rw [kwDartOfPort_toProd_of_external G hsrev, heq.1, heq.2]
        have hqr : q = r := by
          apply kwDartOfPort_injective G
          calc
            kwDartOfPort G q = (kwDartOfPort G p).symm := hpqext
            _ = (kwDartOfPort G s).symm := by rw [hps]
            _ = ((kwDartOfPort G r).symm).symm := by rw [hrsext]
            _ = kwDartOfPort G r := (kwDartOfPort G r).symm_symm
        rw [hps, hqr]
        exact Sym2.eq_swap

theorem kwOrderedSplitWeight_eq_one_of_projection_diag
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : Sym2 V → ℂ)
    {edge : Sym2 (KWDartPort G)} (hdiag :
      (kwOrderedSplitEdgeProjection edge).IsDiag) :
    kwOrderedSplitWeight G weight edge = 1 := by
  induction edge using Sym2.inductionOn with
  | _ p q =>
    rw [kwOrderedSplitEdgeProjection_mk, Sym2.mk_isDiag_iff] at hdiag
    unfold kwOrderedSplitWeight
    change (if kwDartOfPort G q = (kwDartOfPort G p).symm
      then weight (kwDartOfPort G p).edge else 1) = 1
    by_cases hext : kwDartOfPort G q = (kwDartOfPort G p).symm
    · have hfirst := congrArg (fun d : G.Dart => d.fst) hext
      change (kwDartOfPort G q).fst = (kwDartOfPort G p).snd at hfirst
      rw [kwDartOfPort_fst] at hfirst
      exact ((kwDartOfPort G p).fst_ne_snd (by
        calc
          (kwDartOfPort G p).fst = p.1 := kwDartOfPort_fst G p
          _ = q.1 := hdiag
          _ = (kwDartOfPort G p).snd := hfirst)).elim
    · rw [if_neg hext]

theorem kwOrderedSplitWeight_eq_projection_of_not_diag
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 V → ℂ) {edge : Sym2 (KWDartPort G)}
    (hedge : edge ∈ (kwOrderedDartPortSplitGraph G order).edgeFinset)
    (hdiag : ¬(kwOrderedSplitEdgeProjection edge).IsDiag) :
    kwOrderedSplitWeight G weight edge =
      weight (kwOrderedSplitEdgeProjection edge) := by
  induction edge using Sym2.inductionOn with
  | _ p q =>
    have hpq : (kwOrderedDartPortSplitGraph G order).Adj p q :=
      SimpleGraph.mem_edgeFinset.mp hedge
    have hext := kwOrderedSplit_external_of_projection_not_diag
      G order hpq hdiag
    unfold kwOrderedSplitWeight
    change (if kwDartOfPort G q = (kwDartOfPort G p).symm
      then weight (kwDartOfPort G p).edge else 1) =
        weight (kwOrderedSplitEdgeProjection s(p, q))
    rw [if_pos hext, kwOrderedSplitEdgeProjection_mk]
    have hprod := kwDartOfPort_toProd_of_external G hext
    unfold SimpleGraph.Dart.edge
    rw [hprod]



theorem kwOrderedSplitEdges_weight_prod
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 V → ℂ) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) :
    (∏ edge ∈ kwOrderedSplitEdges G order b y,
        kwOrderedSplitWeight G weight edge) =
      ∏ edge ∈ kwDartEdgeBitsFinset G b, weight edge := by
  classical
  let S := (kwOrderedSplitEdges G order b y).filter fun edge =>
    ¬(kwOrderedSplitEdgeProjection edge).IsDiag
  let T := kwDartEdgeBitsFinset G b
  have hremove :
      (∏ edge ∈ S, kwOrderedSplitWeight G weight edge) =
        ∏ edge ∈ kwOrderedSplitEdges G order b y,
          kwOrderedSplitWeight G weight edge := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro edge hedge hnot
    apply kwOrderedSplitWeight_eq_one_of_projection_diag G weight
    by_contra hdiag
    apply hnot
    exact Finset.mem_filter.mpr ⟨hedge, hdiag⟩
  rw [← hremove]
  apply Finset.prod_bij
    (fun edge (_ : edge ∈ S) => kwOrderedSplitEdgeProjection edge)
  · intro edge hedge
    have hdata := Finset.mem_filter.mp hedge
    induction edge using Sym2.inductionOn with
    | _ p q =>
      have hpqEdge : s(p, q) ∈
          (kwOrderedDartPortSplitGraph G order).edgeFinset :=
        (Finset.filter_subset _ _) hdata.1
      have hpq : (kwOrderedDartPortSplitGraph G order).Adj p q :=
        SimpleGraph.mem_edgeFinset.mp hpqEdge
      have hext := kwOrderedSplit_external_of_projection_not_diag
        G order hpq hdata.2
      let d : (kwOrderedDartPortSplitGraph G order).Dart := ⟨(p, q), hpq⟩
      have hbit : kwOrderedPortSplitAdjBit G order b y p q = 1 :=
        (mem_kwOrderedSplitEdges_iff G order b y d).mp hdata.1
      unfold kwOrderedPortSplitAdjBit at hbit
      rw [if_pos hext] at hbit
      have hproj : kwOrderedSplitEdgeProjection s(p, q) =
          (kwDartOfPort G p).edge := by
        rw [kwOrderedSplitEdgeProjection_mk]
        have hprod := kwDartOfPort_toProd_of_external G hext
        unfold SimpleGraph.Dart.edge
        rw [hprod]
      rw [hproj]
      exact (mem_kwDartEdgeBitsFinset_iff G b (kwDartOfPort G p)).mpr hbit
  · intro edge hedge edge' hedge' heq
    have hdata := Finset.mem_filter.mp hedge
    have hdata' := Finset.mem_filter.mp hedge'
    exact kwOrderedSplitEdgeProjection_injective G order
      ((Finset.filter_subset _ _) hdata.1)
      ((Finset.filter_subset _ _) hdata'.1) hdata.2 hdata'.2 heq
  · intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ v w =>
      have hdata := Finset.mem_filter.mp hedge
      have hvw : G.Adj v w := by simpa using hdata.1
      let d : G.Dart := ⟨(v, w), hvw⟩
      let delta := (kwOrderedExternalSplitDartOfDart G order d).1
      have hproj : kwOrderedSplitEdgeProjection delta.edge = d.edge := by
        have hp : (kwPortOfDart G d).1 = d.fst := by
          simpa using (kwDartOfPort_fst G (kwPortOfDart G d)).symm
        have hq : (kwPortOfDart G d.symm).1 = d.snd := by
          simpa using (kwDartOfPort_fst G (kwPortOfDart G d.symm)).symm
        change s((kwPortOfDart G d).1,
          (kwPortOfDart G d.symm).1) = d.edge
        rw [hp, hq]
        rfl
      refine ⟨delta.edge, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · apply (mem_kwOrderedSplitEdges_iff G order b y delta).mpr
          have hmatch : delta.snd = kwOrderedMatchingNeighbor G delta.fst := by
            apply kwDartOfPort_injective G
            simp [delta, kwOrderedMatchingNeighbor]
          rw [hmatch, kwOrderedPortSplitAdjBit_matching]
          have hb : b.1 d = 1 := by
            have hdedge : d.edge = s(v, w) := rfl
            rw [← hdedge, kwDartEdgeBitValue_edge] at hdata
            exact hdata.2
          simpa [delta, kwExternalPortBits, d] using hb
        · rw [hproj]
          simpa [d, SimpleGraph.Dart.edge, Sym2.mk_isDiag_iff] using hvw.ne
      · simpa [d, SimpleGraph.Dart.edge] using hproj
  · intro edge hedge
    have hdata := Finset.mem_filter.mp hedge
    apply kwOrderedSplitWeight_eq_projection_of_not_diag G order weight
    · exact (Finset.filter_subset _ _) hdata.1
    · exact hdata.2

theorem kwEvenPolynomial_eq_sum_actual
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) :
    kwEvenPolynomial G weight =
      ∑ F : KWActualEvenSubgraph G, ∏ edge ∈ F.1, weight edge := by
  unfold kwEvenPolynomial KWActualEvenSubgraph
  exact Finset.sum_subtype (G.edgeFinset.powerset.filter IsEvenSubgraph)
    (fun F => Iff.rfl) (fun F => ∏ edge ∈ F, weight edge)





theorem kwOrderedSplit_evenPolynomial_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 V → ℂ) :
    kwEvenPolynomial (kwOrderedDartPortSplitGraph G order)
        (kwOrderedSplitWeight G weight) =
      kwEvenPolynomial G weight := by
  rw [kwEvenPolynomial_eq_sum_actual, kwEvenPolynomial_eq_sum_actual]
  symm
  apply Fintype.sum_equiv (kwOrderedSplitEvenSubgraphEquiv G order)
  intro F
  have hdata := F.2
  change F.1 ∈ G.edgeFinset.powerset.filter IsEvenSubgraph at hdata
  rw [Finset.mem_filter, Finset.mem_powerset] at hdata
  let b := kwFinsetDartEdgeBits G F.1
  let y := kwOrderedCanonicalPortChainField G order b
  have hprod := kwOrderedSplitEdges_weight_prod G order weight b y
  have hFset : kwDartEdgeBitsFinset G b = F.1 :=
    kwDartEdgeBitsFinset_finset G F.1 hdata.1
  rw [hFset] at hprod
  simpa [kwOrderedSplitEvenSubgraphEquiv,
    kwActualEvenSubgraphEquivBits, kwOriginalEvenBitsEquivOrderedSplit,
    kwActualOrderedSplitEvenEquivBits, Equiv.trans_apply, b, y] using hprod.symm

end StatMech.FrontierA
