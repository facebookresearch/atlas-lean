/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWSequentialStoppedConditionalLaw
import Code.Lattice.PathVisitsRow












open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section






abbrev RlcSourceRightFullCrossing (n : Int) :=
  { gamma : RlcRightDiagonalPath n //
    (gamma.1.1 : Site 2) 1 < 0 ∧
      ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 ->
        z = (gamma.1.1 : Site 2) }



abbrev RlcSourceLeftFullCrossing (n : Int) :=
  { gamma : RlcLeftDiagonalPath n //
    0 < (gamma.1.2.1 : Site 2) 1 ∧
      ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 ->
        z = (gamma.1.2.1 : Site 2) }


abbrev RlcSourceFullCrossingPair (n : Int) :=
  RlcSourceRightFullCrossing n × RlcSourceLeftFullCrossing n

noncomputable instance rlc_sourceFullCrossingPairFintype (n : Int) :
    Fintype (RlcSourceFullCrossingPair n) := by
  unfold RlcSourceFullCrossingPair RlcSourceRightFullCrossing
    RlcSourceLeftFullCrossing
  infer_instance




noncomputable def rlc_sourceExtremalPairCandidate {n : Int}
    (pair : RlcSourceFullCrossingPair n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_extremalPairCandidate (pair.1.1, pair.2.1)



noncomputable def rlc_sourceStoppedDiagonalEvent (n : Int) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ pair : RlcSourceFullCrossingPair n,
    rlc_sourceExtremalPairCandidate pair

theorem RlcSourceRightFullCrossing.axis_contact_eq_endpoint {n : Int}
    (gamma : RlcSourceRightFullCrossing n) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1.1) (hz0 : z 0 = 0) :
    z = (gamma.1.1.1 : Site 2) :=
  gamma.2.2 hz hz0

theorem RlcSourceRightFullCrossing.axis_contact_strict {n : Int}
    (gamma : RlcSourceRightFullCrossing n) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1.1) (hz0 : z 0 = 0) :
    z 1 < 0 := by
  rw [gamma.axis_contact_eq_endpoint hz hz0]
  exact gamma.2.1

theorem RlcSourceLeftFullCrossing.axis_contact_eq_endpoint {n : Int}
    (gamma : RlcSourceLeftFullCrossing n) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1.1) (hz0 : z 0 = 0) :
    z = (gamma.1.1.2.1 : Site 2) :=
  gamma.2.2 hz hz0

theorem RlcSourceLeftFullCrossing.axis_contact_strict {n : Int}
    (gamma : RlcSourceLeftFullCrossing n) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1.1) (hz0 : z 0 = 0) :
    0 < z 1 := by
  rw [gamma.axis_contact_eq_endpoint hz hz0]
  exact gamma.2.1

theorem rlc_sourceExtremalPairCandidate_subset_diagonalEvent {n : Int}
    (pair : RlcSourceFullCrossingPair n) :
    rlc_sourceExtremalPairCandidate pair ⊆
      rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
  intro omega homega
  rw [← rlc_iUnion_extremalPairCandidate]
  exact Set.mem_iUnion.mpr ⟨(pair.1.1, pair.2.1), homega⟩



theorem rlc_sourceStoppedDiagonalEvent_subset_diagonalEvent (n : Int) :
    rlc_sourceStoppedDiagonalEvent n ⊆
      rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
  intro omega homega
  obtain ⟨pair, hpair⟩ := Set.mem_iUnion.mp homega
  exact rlc_sourceExtremalPairCandidate_subset_diagonalEvent pair hpair



theorem rlc_sourceExtremalPairCandidate_pairwiseDisjoint {n : Int}
    (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    Pairwise (fun pair pair' : RlcSourceFullCrossingPair n =>
      Disjoint (rlc_sourceExtremalPairCandidate pair)
        (rlc_sourceExtremalPairCandidate pair')) := by
  intro pair pair' hne
  apply rlc_extremalPairCandidate_pairwiseDisjoint hright hleft
  intro hval
  apply hne
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst hval
  · exact congrArg Prod.snd hval

theorem rlc_rightWalk_first_axis_contact_from_outer {n : Int}
    {x y : rect 0 (2 * n) (-n) n}
    (p : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Walk x y)
    (hx : 0 < (x : Site 2) 0) (hy : (y : Site 2) 0 = 0) :
    ∃ j ≤ p.length, (p.getVert j : Site 2) 0 = 0 ∧
      ∀ m < j, 0 < (p.getVert m : Site 2) 0 := by
  have hlen : (p.getVert p.length : Site 2) 0 ≤ 0 := by
    rw [p.getVert_length, hy]
  classical
  let P : ℕ → Prop := fun m => (p.getVert m : Site 2) 0 ≤ 0
  have hPex : ∃ m, P m := ⟨p.length, hlen⟩
  let j := Nat.find hPex
  have hjP : (p.getVert j : Site 2) 0 ≤ 0 := Nat.find_spec hPex
  have hjle : j ≤ p.length := Nat.find_le hlen
  have habove : ∀ m < j, 0 < (p.getVert m : Site 2) 0 := by
    intro m hm
    have := Nat.find_min hPex hm
    simpa [P, not_le] using this
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, p.getVert_zero] at hjP
    exact (not_le_of_gt hx) hjP
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hkj : k < j := by omega
  have hkt : 0 < (p.getVert k : Site 2) 0 := habove k hkj
  have hklt : k < p.length := by omega
  have hadj := p.adj_getVert_succ hklt
  have hdiff := pvr_adj_coord_diff_le_one hadj 0
  have habs : |(p.getVert k : Site 2) 0 -
      (p.getVert (k + 1) : Site 2) 0| ≤ 1 := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hdiff
  have hge : 0 ≤ (p.getVert (k + 1) : Site 2) 0 := by
    have hstep : (p.getVert k : Site 2) 0 -
        (p.getVert (k + 1) : Site 2) 0 ≤ 1 :=
      (le_abs_self _).trans habs
    omega
  refine ⟨j, hjle, ?_, habove⟩
  have hjP' : (p.getVert k.succ : Site 2) 0 ≤ 0 := by
    simpa [hk] using hjP
  have hge' : 0 ≤ (p.getVert k.succ : Site 2) 0 := by
    simpa [Nat.succ_eq_add_one] using hge
  rw [hk]
  exact le_antisymm hjP' hge'

theorem rlc_leftWalk_first_axis_contact_from_outer {n : Int}
    {x y : rect (-2 * n) 0 (-n) n}
    (p : ((hypercubicLattice 2).induce
      (rect (-2 * n) 0 (-n) n)).Walk x y)
    (hx : (x : Site 2) 0 < 0) (hy : (y : Site 2) 0 = 0) :
    ∃ j ≤ p.length, (p.getVert j : Site 2) 0 = 0 ∧
      ∀ m < j, (p.getVert m : Site 2) 0 < 0 := by
  have hlen : 0 ≤ (p.getVert p.length : Site 2) 0 := by
    rw [p.getVert_length, hy]
  classical
  let P : ℕ → Prop := fun m => 0 ≤ (p.getVert m : Site 2) 0
  have hPex : ∃ m, P m := ⟨p.length, hlen⟩
  let j := Nat.find hPex
  have hjP : 0 ≤ (p.getVert j : Site 2) 0 := Nat.find_spec hPex
  have hjle : j ≤ p.length := Nat.find_le hlen
  have hbelow : ∀ m < j, (p.getVert m : Site 2) 0 < 0 := by
    intro m hm
    have := Nat.find_min hPex hm
    simpa [P, not_le] using this
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, p.getVert_zero] at hjP
    exact (not_le_of_gt hx) hjP
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hkj : k < j := by omega
  have hkt : (p.getVert k : Site 2) 0 < 0 := hbelow k hkj
  have hklt : k < p.length := by omega
  have hadj := p.adj_getVert_succ hklt
  have hdiff := pvr_adj_coord_diff_le_one hadj 0
  have habs : |(p.getVert (k + 1) : Site 2) 0 -
      (p.getVert k : Site 2) 0| ≤ 1 := by
    rw [show (p.getVert (k + 1) : Site 2) 0 -
        (p.getVert k : Site 2) 0 =
      -((p.getVert k : Site 2) 0 -
        (p.getVert (k + 1) : Site 2) 0) by ring,
      abs_neg, Int.abs_eq_natAbs]
    exact_mod_cast hdiff
  have hle : (p.getVert (k + 1) : Site 2) 0 ≤ 0 := by
    have hstep : (p.getVert (k + 1) : Site 2) 0 -
        (p.getVert k : Site 2) 0 ≤ 1 :=
      (le_abs_self _).trans habs
    omega
  refine ⟨j, hjle, ?_, hbelow⟩
  have hjP' : 0 ≤ (p.getVert k.succ : Site 2) 0 := by
    simpa [hk] using hjP
  have hle' : (p.getVert k.succ : Site 2) 0 ≤ 0 := by
    simpa [Nat.succ_eq_add_one] using hle
  rw [hk]
  exact le_antisymm hle' hjP'

set_option maxHeartbeats 800000 in


theorem rlc_exists_rightBookFaithfulSubpath_of_axis_strict
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (hneg : ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 ->
      z 0 = 0 -> z 1 < 0) :
    ∃ delta : RlcRightDiagonalPath n,
      rlc_pathEdges delta.1 ⊆ rlc_pathEdges gamma.1 ∧
      rlc_pathVertices delta.1 ⊆ rlc_pathVertices gamma.1 ∧
      (∀ {z : Site 2}, z ∈ rlc_pathVertices delta.1 -> z 0 = 0 ->
        z = (delta.1.1 : Site 2)) ∧
      (delta.1.1 : Site 2) 1 < 0 := by
  classical
  let w := gamma.1.2.2.1
  let p := w.reverse
  have hpStart : 0 <
      ((⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ :
        rect 0 (2 * n) (-n) n) : Site 2) 0 := by
    change 0 < (gamma.1.2.1 : Site 2) 0
    have := gamma.1.2.1.2.2
    omega
  have hpEnd :
      ((⟨gamma.1.1, leftSide_subset gamma.1.1.2⟩ :
        rect 0 (2 * n) (-n) n) : Site 2) 0 = 0 := by
    exact gamma.1.1.2.2
  obtain ⟨j, hjle, hju, hjpos⟩ :=
    rlc_rightWalk_first_axis_contact_from_outer p hpStart hpEnd
  let u := p.getVert j
  let qrev := p.take j
  let q := qrev.reverse
  have hqPath : q.IsPath := (gamma.1.2.2.2.reverse.take j).reverse
  let x : leftSide 0 (2 * n) (-n) n := ⟨u, u.2, hju⟩
  let delta0 : RlcCrossingPath 0 (2 * n) (-n) n :=
    ⟨x, gamma.1.2.1, ⟨q, hqPath⟩⟩
  have huGamma : (u : Site 2) ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    refine ⟨u, ?_, rfl⟩
    have huP : u ∈ p.support := p.getVert_mem_support j
    simpa [p, SimpleGraph.Walk.support_reverse] using huP
  have huNeg : (u : Site 2) 1 < 0 := hneg huGamma hju
  let delta : RlcRightDiagonalPath n :=
    ⟨delta0, le_of_lt huNeg, gamma.2.2⟩
  refine ⟨delta, ?_, ?_, ?_, huNeg⟩
  · intro e he
    simp only [rlc_pathEdges, delta, delta0, Finset.mem_image,
      List.mem_toFinset] at he ⊢
    obtain ⟨e0, he0, rfl⟩ := he
    refine ⟨e0, ?_, rfl⟩
    have heQrev : e0 ∈ qrev.edges := by
      simpa [q, SimpleGraph.Walk.edges_reverse] using he0
    have heP : e0 ∈ p.edges := by
      simp only [qrev, SimpleGraph.Walk.edges_take] at heQrev
      exact List.mem_of_mem_take heQrev
    simpa [p, SimpleGraph.Walk.edges_reverse] using heP
  · intro z hz
    simp only [rlc_pathVertices, delta, delta0, Finset.mem_image,
      List.mem_toFinset] at hz ⊢
    obtain ⟨v, hv, rfl⟩ := hz
    refine ⟨v, ?_, rfl⟩
    have hvQrev : v ∈ qrev.support := by
      simpa [q, SimpleGraph.Walk.support_reverse] using hv
    simp only [qrev, SimpleGraph.Walk.take_support_eq_support_take_succ] at hvQrev
    have hvP : v ∈ p.support := List.mem_of_mem_take hvQrev
    simpa [p, SimpleGraph.Walk.support_reverse] using hvP
  · intro z hz hz0
    simp only [rlc_pathVertices, delta, delta0, Finset.mem_image,
      List.mem_toFinset] at hz
    obtain ⟨v, hv, hvz⟩ := hz
    have hvQrev : v ∈ qrev.support := by
      simpa [q, SimpleGraph.Walk.support_reverse] using hv
    simp only [qrev, SimpleGraph.Walk.take_support_eq_support_take_succ] at hvQrev
    obtain ⟨m, hmlt, hmv⟩ := List.mem_iff_getElem.mp hvQrev
    rw [List.length_take] at hmlt
    have hmle : m ≤ j := by omega
    have hmplen : m ≤ p.length := hmle.trans hjle
    rw [List.getElem_take] at hmv
    have hvm : v = p.getVert m := by
      rw [← hmv, ← SimpleGraph.Walk.getVert_eq_support_getElem p hmplen]
    have hmj : m = j := by
      by_contra hne
      have hmltJ : m < j := lt_of_le_of_ne hmle hne
      have hmPos := hjpos m hmltJ
      rw [← hvm] at hmPos
      have : (v : Site 2) 0 = 0 := by simpa [hvz] using hz0
      omega
    have hvu : v = u := by simpa [u, hmj] using hvm
    exact hvz.symm.trans (congrArg Subtype.val hvu)

set_option maxHeartbeats 800000 in


theorem rlc_exists_leftBookFaithfulSubpath_of_axis_strict
    {n : Int} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n)
    (hpos : ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 ->
      z 0 = 0 -> 0 < z 1) :
    ∃ delta : RlcLeftDiagonalPath n,
      rlc_pathEdges delta.1 ⊆ rlc_pathEdges gamma.1 ∧
      rlc_pathVertices delta.1 ⊆ rlc_pathVertices gamma.1 ∧
      (∀ {z : Site 2}, z ∈ rlc_pathVertices delta.1 -> z 0 = 0 ->
        z = (delta.1.2.1 : Site 2)) ∧
      0 < (delta.1.2.1 : Site 2) 1 := by
  classical
  let p := gamma.1.2.2.1
  have hpStart :
      ((⟨gamma.1.1, leftSide_subset gamma.1.1.2⟩ :
        rect (-2 * n) 0 (-n) n) : Site 2) 0 < 0 := by
    change (gamma.1.1 : Site 2) 0 < 0
    have := gamma.1.1.2.2
    omega
  have hpEnd :
      ((⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ :
        rect (-2 * n) 0 (-n) n) : Site 2) 0 = 0 :=
    gamma.1.2.1.2.2
  obtain ⟨j, hjle, hju, hjneg⟩ :=
    rlc_leftWalk_first_axis_contact_from_outer p hpStart hpEnd
  let u := p.getVert j
  let q := p.take j
  have hqPath : q.IsPath := gamma.1.2.2.2.take j
  let y : rightSide (-2 * n) 0 (-n) n := ⟨u, u.2, hju⟩
  let delta0 : RlcCrossingPath (-2 * n) 0 (-n) n :=
    ⟨gamma.1.1, y, ⟨q, hqPath⟩⟩
  have huGamma : (u : Site 2) ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨u, p.getVert_mem_support j, rfl⟩
  have huPos : 0 < (u : Site 2) 1 := hpos huGamma hju
  let delta : RlcLeftDiagonalPath n :=
    ⟨delta0, gamma.2.1, le_of_lt huPos⟩
  refine ⟨delta, ?_, ?_, ?_, huPos⟩
  · intro e he
    simp only [rlc_pathEdges, delta, delta0, Finset.mem_image,
      List.mem_toFinset] at he ⊢
    obtain ⟨e0, he0, rfl⟩ := he
    refine ⟨e0, ?_, rfl⟩
    simp only [q, SimpleGraph.Walk.edges_take] at he0
    exact List.mem_of_mem_take he0
  · intro z hz
    simp only [rlc_pathVertices, delta, delta0, Finset.mem_image,
      List.mem_toFinset] at hz ⊢
    obtain ⟨v, hv, rfl⟩ := hz
    refine ⟨v, ?_, rfl⟩
    simp only [q, SimpleGraph.Walk.take_support_eq_support_take_succ] at hv
    exact List.mem_of_mem_take hv
  · intro z hz hz0
    simp only [rlc_pathVertices, delta, delta0, Finset.mem_image,
      List.mem_toFinset] at hz
    obtain ⟨v, hv, hvz⟩ := hz
    simp only [q, SimpleGraph.Walk.take_support_eq_support_take_succ] at hv
    obtain ⟨m, hmlt, hmv⟩ := List.mem_iff_getElem.mp hv
    rw [List.length_take] at hmlt
    have hmle : m ≤ j := by omega
    have hmplen : m ≤ p.length := hmle.trans hjle
    rw [List.getElem_take] at hmv
    have hvm : v = p.getVert m := by
      rw [← hmv, ← SimpleGraph.Walk.getVert_eq_support_getElem p hmplen]
    have hmj : m = j := by
      by_contra hne
      have hmltJ : m < j := lt_of_le_of_ne hmle hne
      have hmNeg := hjneg m hmltJ
      rw [← hvm] at hmNeg
      have : (v : Site 2) 0 = 0 := by simpa [hvz] using hz0
      omega
    have hvu : v = u := by simpa [u, hmj] using hvm
    exact hvz.symm.trans (congrArg Subtype.val hvu)



theorem rlc_exists_bookFaithfulSubpaths_of_axis_strict
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1))
    (hright : ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 →
      z 0 = 0 → z 1 < 0)
    (hleft : ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma'.1 →
      z 0 = 0 → 0 < z 1) :
    ∃ (delta : RlcRightDiagonalPath n)
      (delta' : RlcLeftDiagonalPath n),
      RlcBookFaithfulTracePair delta delta' ∧
        rlc_pathEdges delta.1 ⊆ rlc_pathEdges gamma.1 ∧
        rlc_pathEdges delta'.1 ⊆ rlc_pathEdges gamma'.1 ∧
        rlc_pathVertices delta.1 ⊆ rlc_pathVertices gamma.1 ∧
        rlc_pathVertices delta'.1 ⊆ rlc_pathVertices gamma'.1 := by
  obtain ⟨delta, hrEdges, hrVerts, hrUnique, hrStrict⟩ :=
    rlc_exists_rightBookFaithfulSubpath_of_axis_strict hn gamma hright
  obtain ⟨delta', hlEdges, hlVerts, hlUnique, hlStrict⟩ :=
    rlc_exists_leftBookFaithfulSubpath_of_axis_strict hn gamma' hleft
  have hsubDisj : Disjoint (rlc_pathVertices delta.1)
      (rlc_pathVertices delta'.1) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    exact (Finset.disjoint_left.mp hdisj) (hrVerts hz) (hlVerts hz')
  refine ⟨delta, delta', ?_, hrEdges, hlEdges, hrVerts, hlVerts⟩
  exact {
    toRlcBookPositionedTracePair := {
      exposed_disjoint := hsubDisj
      right_axis_strict := hrStrict
      left_axis_strict := hlStrict }
    right_axis_unique := hrUnique
    left_axis_unique := hlUnique }



theorem rlc_finiteConnectorEvent_eq_univ_of_common_trace_vertex
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : z ∈ rlc_pathVertices gamma'.1) :
    rlc_finiteConnectorEvent gamma gamma' = Set.univ := by
  ext tau
  simp only [Set.mem_univ, iff_true]
  let x : RlcConnectorVertex n :=
    ⟨z, rlc_rightPathVertex_mem_connectorBox gamma hzRight⟩
  exact ⟨x, x, hzRight, hzLeft, SimpleGraph.Reachable.refl x⟩




theorem rlc_extremalPairCandidate_faithfulReplacement_or_axisDefect_or_intersects
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hactive : (rlc_extremalPairCandidate (gamma, gamma')).Nonempty) :
    (∃ (delta : RlcRightDiagonalPath n)
        (delta' : RlcLeftDiagonalPath n),
        RlcBookFaithfulStratumReplacement gamma gamma' delta delta') ∨
      (∃ z ∈ rlc_pathVertices gamma.1,
        z 0 = 0 ∧ 0 ≤ z 1) ∨
      (∃ z ∈ rlc_pathVertices gamma'.1,
        z 0 = 0 ∧ z 1 ≤ 0) ∨
      ∃ z, z ∈ rlc_pathVertices gamma.1 ∧
        z ∈ rlc_pathVertices gamma'.1 := by
  classical
  by_cases hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1)
  · by_cases hright : ∀ {z : Site 2},
        z ∈ rlc_pathVertices gamma.1 → z 0 = 0 → z 1 < 0
    · by_cases hleft : ∀ {z : Site 2},
          z ∈ rlc_pathVertices gamma'.1 → z 0 = 0 → 0 < z 1
      · left
        obtain ⟨delta, delta', hfaith, hrEdges, hlEdges,
            hrVerts, hlVerts⟩ :=
          rlc_exists_bookFaithfulSubpaths_of_axis_strict
            hn gamma gamma' hdisj hright hleft
        exact ⟨delta, delta',
          RlcBookFaithfulStratumReplacement.of_subpaths
            hfaith hrEdges hlEdges hrVerts hlVerts hactive⟩
      · right
        right
        left
        push Not at hleft
        obtain ⟨z, hz, hz0, hzNot⟩ := hleft
        exact ⟨z, hz, hz0, hzNot⟩
    · right
      left
      push Not at hright
      obtain ⟨z, hz, hz0, hzNot⟩ := hright
      exact ⟨z, hz, hz0, hzNot⟩
  · right
    right
    right
    rw [Finset.disjoint_left] at hdisj
    push Not at hdisj
    exact hdisj




theorem rlc_sourceExtremalPairCandidate_faithfulReplacement_or_intersects
    {n : Int} (hn : 0 < n) (pair : RlcSourceFullCrossingPair n)
    (hactive : (rlc_sourceExtremalPairCandidate pair).Nonempty) :
    (∃ (delta : RlcRightDiagonalPath n)
        (delta' : RlcLeftDiagonalPath n),
        RlcBookFaithfulStratumReplacement
          pair.1.1 pair.2.1 delta delta') ∨
      ∃ z, z ∈ rlc_pathVertices pair.1.1.1 ∧
        z ∈ rlc_pathVertices pair.2.1.1 := by
  classical
  by_cases hdisj : Disjoint (rlc_pathVertices pair.1.1.1)
      (rlc_pathVertices pair.2.1.1)
  · left
    obtain ⟨delta, delta', hfaith, hrEdges, hlEdges,
        hrVertices, hlVertices⟩ :=
      rlc_exists_bookFaithfulSubpaths_of_axis_strict hn pair.1.1 pair.2.1
        hdisj
        (fun hz hz0 => pair.1.axis_contact_strict hz hz0)
        (fun hz hz0 => pair.2.axis_contact_strict hz hz0)
    exact ⟨delta, delta',
      RlcBookFaithfulStratumReplacement.of_subpaths hfaith hrEdges hlEdges
        hrVertices hlVertices hactive⟩
  · right
    rw [Finset.disjoint_left] at hdisj
    push Not at hdisj
    exact hdisj




theorem rlc_sourceExtremalPairCandidate_replacement_or_connectorEvent_eq_univ
    {n : Int} (hn : 0 < n) (pair : RlcSourceFullCrossingPair n)
    (hactive : (rlc_sourceExtremalPairCandidate pair).Nonempty) :
    (∃ (delta : RlcRightDiagonalPath n)
        (delta' : RlcLeftDiagonalPath n),
        RlcBookFaithfulStratumReplacement
          pair.1.1 pair.2.1 delta delta') ∨
      rlc_finiteConnectorEvent pair.1.1 pair.2.1 = Set.univ := by
  rcases rlc_sourceExtremalPairCandidate_faithfulReplacement_or_intersects
      hn pair hactive with hreplacement | ⟨z, hzRight, hzLeft⟩
  · exact Or.inl hreplacement
  · exact Or.inr
      (rlc_finiteConnectorEvent_eq_univ_of_common_trace_vertex
        pair.1.1 pair.2.1 hzRight hzLeft)

end

end StatMech.Universality
