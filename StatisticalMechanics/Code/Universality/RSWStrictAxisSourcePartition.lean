/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWStoppedFaithfulSubpath














open Finset SimpleGraph Set MeasureTheory

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section





abbrev RlcStrictAxisRightFullCrossing (n : Int) :=
  { gamma : RlcRightDiagonalPath n //
      ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 -> z 1 < 0 }


abbrev RlcStrictAxisLeftFullCrossing (n : Int) :=
  { gamma : RlcLeftDiagonalPath n //
      ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 -> 0 < z 1 }


abbrev RlcStrictAxisFullCrossingPair (n : Int) :=
  RlcStrictAxisRightFullCrossing n × RlcStrictAxisLeftFullCrossing n

noncomputable instance rlc_strictAxisFullCrossingPairFintype (n : Int) :
    Fintype (RlcStrictAxisFullCrossingPair n) := by
  unfold RlcStrictAxisFullCrossingPair RlcStrictAxisRightFullCrossing
    RlcStrictAxisLeftFullCrossing
  infer_instance



noncomputable def rlc_strictAxisRightSourceEvent (n : Int) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ gamma : RlcStrictAxisRightFullCrossing n, rlc_pathOpen gamma.1.1


noncomputable def rlc_strictAxisLeftSourceEvent (n : Int) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ gamma : RlcStrictAxisLeftFullCrossing n, rlc_pathOpen gamma.1.1



noncomputable def rlc_strictAxisExtremalPairCandidate {n : Int}
    (pair : RlcStrictAxisFullCrossingPair n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_extremalPairCandidate (pair.1.1, pair.2.1)


noncomputable def rlc_strictAxisStoppedDiagonalEvent (n : Int) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ pair : RlcStrictAxisFullCrossingPair n,
    rlc_strictAxisExtremalPairCandidate pair





theorem RlcStrictAxisRightFullCrossing.axis_nonnegative_mem_strictTopSet
    {n : Int} (hn : 0 < n) (gamma : RlcStrictAxisRightFullCrossing n)
    {z : Site 2} (hzR : z ∈ rect 0 (2 * n) (-n) n)
    (hz0 : z 0 = 0) (hz1 : 0 ≤ z 1) :
    z ∈ rlc_strictTopSet gamma.1 := by
  let x : Site 2 := ![0, n]
  have hxTop : x ∈ topSide 0 (2 * n) (-n) n := by
    rw [mem_topSide, mem_rect]
    simp [x]
    omega
  have hzle : z 1 ≤ n := by
    rw [mem_rect] at hzR
    exact hzR.2.2.2
  let w0 := sw_vertSeg 0 n (z 1)
  let w : (hypercubicLattice 2).Walk x z := w0.copy
    (by ext i; fin_cases i <;> simp [x])
    (by ext i; fin_cases i <;> simp [hz0])
  have support_data : ∀ {u : Site 2}, u ∈ w.support ->
      u ∈ rect 0 (2 * n) (-n) n ∧
        u ∉ rlc_pathVertices gamma.1.1 := by
    intro u hu
    have hu0 : u 0 = 0 := by
      have hu' : u ∈ w0.support := by
        simpa [w, SimpleGraph.Walk.support_copy] using hu
      rw [sw_vertSeg_mem_support] at hu'
      obtain ⟨t, _ht, rfl⟩ := hu'
      simp
    have huI : u 1 ∈ Set.uIcc n (z 1) := by
      have hu' : u ∈ w0.support := by
        simpa [w, SimpleGraph.Walk.support_copy] using hu
      rw [sw_vertSeg_mem_support] at hu'
      obtain ⟨t, ht, heq⟩ := hu'
      have hu1 : u 1 = t := by rw [heq]; simp
      simpa [hu1] using ht
    have huBounds : z 1 ≤ u 1 ∧ u 1 ≤ n := by
      simpa [Set.uIcc_of_ge hzle] using huI
    constructor
    · rw [mem_rect]
      omega
    · intro huPath
      have := gamma.2 huPath hu0
      omega
  have hw : (rlc_rightPathAvoidGraph gamma.1).Walk x z := by
    apply w.transfer (rlc_rightPathAvoidGraph gamma.1)
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have hadj := w.adj_of_mem_edges he
        have hu := support_data (w.fst_mem_support_of_mem_edges he)
        have hv := support_data (w.snd_mem_support_of_mem_edges he)
        exact ⟨hadj, hu.1, hv.1, hu.2, hv.2⟩
  have hxNot : x ∉ rlc_pathVertices gamma.1.1 :=
    (support_data w.start_mem_support).2
  exact ⟨x, hxTop, hxNot, ⟨hw⟩⟩



theorem RlcStrictAxisLeftFullCrossing.axis_nonpositive_mem_strictBottomSet
    {n : Int} (hn : 0 < n) (gamma : RlcStrictAxisLeftFullCrossing n)
    {z : Site 2} (hzR : z ∈ rect (-2 * n) 0 (-n) n)
    (hz0 : z 0 = 0) (hz1 : z 1 ≤ 0) :
    z ∈ rlc_strictBottomSet gamma.1 := by
  let x : Site 2 := ![0, -n]
  have hxBottom : x ∈ bottomSide (-2 * n) 0 (-n) n := by
    rw [mem_bottomSide, mem_rect]
    simp [x]
    omega
  have hzge : -n ≤ z 1 := by
    rw [mem_rect] at hzR
    exact hzR.2.2.1
  let w0 := sw_vertSeg 0 (-n) (z 1)
  let w : (hypercubicLattice 2).Walk x z := w0.copy
    (by ext i; fin_cases i <;> simp [x])
    (by ext i; fin_cases i <;> simp [hz0])
  have support_data : ∀ {u : Site 2}, u ∈ w.support ->
      u ∈ rect (-2 * n) 0 (-n) n ∧
        u ∉ rlc_pathVertices gamma.1.1 := by
    intro u hu
    have hu0 : u 0 = 0 := by
      have hu' : u ∈ w0.support := by
        simpa [w, SimpleGraph.Walk.support_copy] using hu
      rw [sw_vertSeg_mem_support] at hu'
      obtain ⟨t, _ht, rfl⟩ := hu'
      simp
    have huI : u 1 ∈ Set.uIcc (-n) (z 1) := by
      have hu' : u ∈ w0.support := by
        simpa [w, SimpleGraph.Walk.support_copy] using hu
      rw [sw_vertSeg_mem_support] at hu'
      obtain ⟨t, ht, heq⟩ := hu'
      have hu1 : u 1 = t := by rw [heq]; simp
      simpa [hu1] using ht
    have huBounds : -n ≤ u 1 ∧ u 1 ≤ z 1 := by
      simpa [Set.uIcc_of_le hzge] using huI
    constructor
    · rw [mem_rect]
      omega
    · intro huPath
      have := gamma.2 huPath hu0
      omega
  have hw : (rlc_leftPathAvoidGraph gamma.1).Walk x z := by
    apply w.transfer (rlc_leftPathAvoidGraph gamma.1)
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have hadj := w.adj_of_mem_edges he
        have hu := support_data (w.fst_mem_support_of_mem_edges he)
        have hv := support_data (w.snd_mem_support_of_mem_edges he)
        exact ⟨hadj, hu.1, hv.1, hu.2, hv.2⟩
  have hxNot : x ∉ rlc_pathVertices gamma.1.1 :=
    (support_data w.start_mem_support).2
  exact ⟨x, hxBottom, hxNot, ⟨hw⟩⟩





theorem rlc_rightLowestCandidate_explored_subset_of_open
    {n : Int} (henv : RlcRightEnvelopeProperty n)
    {gamma delta : RlcRightDiagonalPath n}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_rightLowestCandidate gamma)
    (hdelta : omega ∈ rlc_pathOpen delta.1) :
    rlc_rightExploredVertices gamma ⊆ rlc_rightExploredVertices delta := by
  obtain ⟨lambda, hedges, hregion⟩ := henv gamma delta
  have hlambda : omega ∈ rlc_pathOpen lambda.1 :=
    rlc_pathOpen_of_edges_subset_union lambda.1 gamma.1 delta.1 hedges
      hgamma.1 hdelta
  have hsubGamma : rlc_rightExploredVertices lambda ⊆
      rlc_rightExploredVertices gamma := fun z hz =>
    (Finset.mem_inter.mp (hregion hz)).1
  have hsubDelta : rlc_rightExploredVertices lambda ⊆
      rlc_rightExploredVertices delta := fun z hz =>
    (Finset.mem_inter.mp (hregion hz)).2
  have heq := rlc_rightLowestCandidate_explored_eq_of_open_subset
    hgamma hlambda hsubGamma
  exact fun z hz => hsubDelta (heq.symm ▸ hz)


theorem rlc_leftHighestCandidate_explored_subset_of_open
    {n : Int} (henv : RlcLeftEnvelopeProperty n)
    {gamma delta : RlcLeftDiagonalPath n}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_leftHighestCandidate gamma)
    (hdelta : omega ∈ rlc_pathOpen delta.1) :
    rlc_leftExploredVertices gamma ⊆ rlc_leftExploredVertices delta := by
  obtain ⟨lambda, hedges, hregion⟩ := henv gamma delta
  have hlambda : omega ∈ rlc_pathOpen lambda.1 :=
    rlc_pathOpen_of_edges_subset_union lambda.1 gamma.1 delta.1 hedges
      hgamma.1 hdelta
  have hsubGamma : rlc_leftExploredVertices lambda ⊆
      rlc_leftExploredVertices gamma := fun z hz =>
    (Finset.mem_inter.mp (hregion hz)).1
  have hsubDelta : rlc_leftExploredVertices lambda ⊆
      rlc_leftExploredVertices delta := fun z hz =>
    (Finset.mem_inter.mp (hregion hz)).2
  have heq := rlc_leftHighestCandidate_explored_eq_of_open_subset
    hgamma hlambda hsubGamma
  exact fun z hz => hsubDelta (heq.symm ▸ hz)



theorem rlc_rightLowestCandidate_axis_strict_of_open_strictAxis
    {n : Int} (hn : 0 < n) (henv : RlcRightEnvelopeProperty n)
    {gamma : RlcRightDiagonalPath n}
    (delta : RlcStrictAxisRightFullCrossing n)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_rightLowestCandidate gamma)
    (hdelta : omega ∈ rlc_pathOpen delta.1.1) :
    ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 ->
      z 0 = 0 -> z 1 < 0 := by
  have hsub := rlc_rightLowestCandidate_explored_subset_of_open
    henv hgamma hdelta
  intro z hz hz0
  by_contra hz1
  have hzNonneg : 0 ≤ z 1 := by omega
  have hzR : z ∈ rect 0 (2 * n) (-n) n :=
    rlc_pathVertex_mem_rect gamma.1 hz
  have hzTop := delta.axis_nonnegative_mem_strictTopSet hn hzR hz0 hzNonneg
  have hzExplored := hsub (rlc_rightPathVertex_mem_explored gamma hz)
  rw [rlc_rightExploredVertices, Finset.mem_sdiff] at hzExplored
  exact hzExplored.2 (by simpa using hzTop)


theorem rlc_leftHighestCandidate_axis_strict_of_open_strictAxis
    {n : Int} (hn : 0 < n) (henv : RlcLeftEnvelopeProperty n)
    {gamma : RlcLeftDiagonalPath n}
    (delta : RlcStrictAxisLeftFullCrossing n)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_leftHighestCandidate gamma)
    (hdelta : omega ∈ rlc_pathOpen delta.1.1) :
    ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 ->
      z 0 = 0 -> 0 < z 1 := by
  have hsub := rlc_leftHighestCandidate_explored_subset_of_open
    henv hgamma hdelta
  intro z hz hz0
  by_contra hz1
  have hzNonpos : z 1 ≤ 0 := by omega
  have hzR : z ∈ rect (-2 * n) 0 (-n) n :=
    rlc_pathVertex_mem_rect gamma.1 hz
  have hzBottom := delta.axis_nonpositive_mem_strictBottomSet
    hn hzR hz0 hzNonpos
  have hzExplored := hsub (rlc_leftPathVertex_mem_explored gamma hz)
  rw [rlc_leftExploredVertices, Finset.mem_sdiff] at hzExplored
  exact hzExplored.2 (by simpa using hzBottom)





theorem rlc_iUnion_strictAxisExtremalPairCandidate {n : Int} (hn : 0 < n)
    (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    rlc_strictAxisStoppedDiagonalEvent n =
      rlc_strictAxisRightSourceEvent n ∩
        rlc_strictAxisLeftSourceEvent n := by
  apply Set.Subset.antisymm
  · intro omega homega
    obtain ⟨pair, hrightSel, hleftSel⟩ := Set.mem_iUnion.mp homega
    exact ⟨Set.mem_iUnion.mpr ⟨pair.1, hrightSel.1⟩,
      Set.mem_iUnion.mpr ⟨pair.2, hleftSel.1⟩⟩
  · rintro omega ⟨hrightSource, hleftSource⟩
    obtain ⟨delta, hdelta⟩ := Set.mem_iUnion.mp hrightSource
    obtain ⟨delta', hdelta'⟩ := Set.mem_iUnion.mp hleftSource
    have hdiag : omega ∈ rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
      rw [← rlc_iUnion_rightDiagonalPath, ← rlc_iUnion_leftDiagonalPath]
      exact ⟨Set.mem_iUnion.mpr ⟨delta.1, hdelta⟩,
        Set.mem_iUnion.mpr ⟨delta'.1, hdelta'⟩⟩
    rw [← rlc_iUnion_extremalPairCandidate] at hdiag
    obtain ⟨pair, hpair⟩ := Set.mem_iUnion.mp hdiag
    let gamma : RlcStrictAxisRightFullCrossing n :=
      ⟨pair.1, rlc_rightLowestCandidate_axis_strict_of_open_strictAxis
        hn hright delta hpair.1 hdelta⟩
    let gamma' : RlcStrictAxisLeftFullCrossing n :=
      ⟨pair.2, rlc_leftHighestCandidate_axis_strict_of_open_strictAxis
        hn hleft delta' hpair.2 hdelta'⟩
    exact Set.mem_iUnion.mpr ⟨(gamma, gamma'), hpair⟩



theorem rlc_strictAxisExtremalPairCandidate_pairwiseDisjoint {n : Int}
    (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    Pairwise (fun pair pair' : RlcStrictAxisFullCrossingPair n =>
      Disjoint (rlc_strictAxisExtremalPairCandidate pair)
        (rlc_strictAxisExtremalPairCandidate pair')) := by
  intro pair pair' hne
  apply rlc_extremalPairCandidate_pairwiseDisjoint hright hleft
  intro hval
  apply hne
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst hval
  · exact congrArg Prod.snd hval




theorem rlc_strictAxisRightSourceEvent_isIncreasing (n : Int) :
    IsIncreasing (rlc_strictAxisRightSourceEvent n) := by
  intro omega omega' hle homega
  obtain ⟨gamma, hgamma⟩ := Set.mem_iUnion.mp homega
  apply Set.mem_iUnion.mpr
  exact ⟨gamma, fun e he => hle e (hgamma e he)⟩


theorem rlc_strictAxisLeftSourceEvent_isIncreasing (n : Int) :
    IsIncreasing (rlc_strictAxisLeftSourceEvent n) := by
  intro omega omega' hle homega
  obtain ⟨gamma, hgamma⟩ := Set.mem_iUnion.mp homega
  apply Set.mem_iUnion.mpr
  exact ⟨gamma, fun e he => hle e (hgamma e he)⟩



theorem rlc_pathEdges_subset_edgesWithinFinset {a b c d : Int}
    (gamma : RlcCrossingPath a b c d) :
    rlc_pathEdges gamma ⊆
      edgesWithinFinset (rect_finite a b c d).toFinset := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [mem_edgesWithinFinset]
      have hends := rlc_pathEdge_endpoints_mem_vertices gamma he
      exact ⟨x, by simpa using rlc_pathVertex_mem_rect gamma hends.1,
        y, by simpa using rlc_pathVertex_mem_rect gamma hends.2, rfl⟩


theorem rlc_strictAxisRightSourceEvent_dependsOn (n : Int) :
    _root_.DependsOn ((rlc_strictAxisRightSourceEvent n).indicator
      (fun _ => (1 : Real)))
      (edgesWithinFinset (rect_finite 0 (2 * n) (-n) n).toFinset :
        Set (Sym2 (Site 2))) := by
  let S := edgesWithinFinset (rect_finite 0 (2 * n) (-n) n).toFinset
  intro omega omega' hagree
  have hpath : ∀ gamma : RlcStrictAxisRightFullCrossing n,
      omega ∈ rlc_pathOpen gamma.1.1 ↔
        omega' ∈ rlc_pathOpen gamma.1.1 := by
    intro gamma
    apply indic_iff
    apply rlc_pathOpen_dependsOn gamma.1.1
    intro e he
    simpa only [eq_comm] using hagree e (by
      change e ∈ S
      exact rlc_pathEdges_subset_edgesWithinFinset gamma.1.1 he)
  have hevent : omega ∈ rlc_strictAxisRightSourceEvent n ↔
      omega' ∈ rlc_strictAxisRightSourceEvent n := by
    simp only [rlc_strictAxisRightSourceEvent, Set.mem_iUnion]
    exact exists_congr hpath
  by_cases hmem : omega ∈ rlc_strictAxisRightSourceEvent n
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]


theorem rlc_strictAxisLeftSourceEvent_dependsOn (n : Int) :
    _root_.DependsOn ((rlc_strictAxisLeftSourceEvent n).indicator
      (fun _ => (1 : Real)))
      (edgesWithinFinset (rect_finite (-2 * n) 0 (-n) n).toFinset :
        Set (Sym2 (Site 2))) := by
  let S := edgesWithinFinset (rect_finite (-2 * n) 0 (-n) n).toFinset
  intro omega omega' hagree
  have hpath : ∀ gamma : RlcStrictAxisLeftFullCrossing n,
      omega ∈ rlc_pathOpen gamma.1.1 ↔
        omega' ∈ rlc_pathOpen gamma.1.1 := by
    intro gamma
    apply indic_iff
    apply rlc_pathOpen_dependsOn gamma.1.1
    intro e he
    simpa only [eq_comm] using hagree e (by
      change e ∈ S
      exact rlc_pathEdges_subset_edgesWithinFinset gamma.1.1 he)
  have hevent : omega ∈ rlc_strictAxisLeftSourceEvent n ↔
      omega' ∈ rlc_strictAxisLeftSourceEvent n := by
    simp only [rlc_strictAxisLeftSourceEvent, Set.mem_iUnion]
    exact exists_congr hpath
  by_cases hmem : omega ∈ rlc_strictAxisLeftSourceEvent n
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]




theorem rlc_strictAxisStoppedDiagonalEvent_mass_lower
    (p : NNReal) (hp : p ≤ 1) {n : Int} (hn : 0 < n)
    (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n)
    {a b : Real} (hb0 : 0 ≤ b)
    (ha : a ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (rlc_strictAxisRightSourceEvent n))
    (hb : b ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (rlc_strictAxisLeftSourceEvent n)) :
    a * b ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (rlc_strictAxisStoppedDiagonalEvent n) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have harris :
      mu.real (rlc_strictAxisRightSourceEvent n) *
          mu.real (rlc_strictAxisLeftSourceEvent n) ≤
        mu.real (rlc_strictAxisRightSourceEvent n ∩
          rlc_strictAxisLeftSourceEvent n) := by
    exact rlc_harris_cylinder p hp
      (rlc_strictAxisRightSourceEvent_isIncreasing n)
      (rlc_strictAxisLeftSourceEvent_isIncreasing n)
      (edgesWithinFinset (rect_finite 0 (2 * n) (-n) n).toFinset)
      (edgesWithinFinset (rect_finite (-2 * n) 0 (-n) n).toFinset)
      (rlc_strictAxisRightSourceEvent_dependsOn n)
      (rlc_strictAxisLeftSourceEvent_dependsOn n)
  rw [rlc_iUnion_strictAxisExtremalPairCandidate hn hright hleft]
  exact (mul_le_mul ha hb hb0 measureReal_nonneg).trans harris



theorem rlc_strictAxisExtremalPairCandidate_faithfulReplacement_or_intersects
    {n : Int} (hn : 0 < n) (pair : RlcStrictAxisFullCrossingPair n)
    (hactive : (rlc_strictAxisExtremalPairCandidate pair).Nonempty) :
    (∃ (delta : RlcRightDiagonalPath n) (delta' : RlcLeftDiagonalPath n),
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
        hdisj (fun hz hz0 => pair.1.2 hz hz0)
        (fun hz hz0 => pair.2.2 hz hz0)
    exact ⟨delta, delta',
      RlcBookFaithfulStratumReplacement.of_subpaths hfaith hrEdges hlEdges
        hrVertices hlVertices hactive⟩
  · right
    rw [Finset.disjoint_left] at hdisj
    push Not at hdisj
    exact hdisj



theorem rlc_strictAxisExtremalPairCandidate_replacement_or_connectorEvent_eq_univ
    {n : Int} (hn : 0 < n) (pair : RlcStrictAxisFullCrossingPair n)
    (hactive : (rlc_strictAxisExtremalPairCandidate pair).Nonempty) :
    (∃ (delta : RlcRightDiagonalPath n) (delta' : RlcLeftDiagonalPath n),
        RlcBookFaithfulStratumReplacement
          pair.1.1 pair.2.1 delta delta') ∨
      rlc_finiteConnectorEvent pair.1.1 pair.2.1 = Set.univ := by
  rcases
      rlc_strictAxisExtremalPairCandidate_faithfulReplacement_or_intersects
        hn pair hactive with hreplacement | ⟨z, hzRight, hzLeft⟩
  · exact Or.inl hreplacement
  · exact Or.inr
      (rlc_finiteConnectorEvent_eq_univ_of_common_trace_vertex
        pair.1.1 pair.2.1 hzRight hzLeft)

end

end StatMech.Universality
