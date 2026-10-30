/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneJoinedArms

/-!
# Finite sources joined through the unique infinite cluster

Two far-apart translated orbit boxes that both meet the infinite cluster and are joined to each
other inside a bounded region, with probability close to one.

## i. Overview

`orbitBoxCoordinateBound E n i` bounds the `i`-th coordinate of every vertex of the orbit box of
radius `n`; together with a uniform bound `B` on the coordinate excursion of embedded edges it
bounds every point of an embedded walk staying in that orbit box. For finite vertex sets `L`, `R`,
`finiteInfinitePairConnectionEvent L R N` is the event that `L` and `R` both meet the infinite
cluster and no pair of infinite-cluster vertices `x ∈ L`, `y ∈ R` fails to be joined inside the
orbit box of radius `N` (no pair-merge error). On this event there is an open walk from `L` to `R`
inside the buffered orbit box, hence an embedded open path with explicit coordinate bounds.
Inclusion–exclusion bounds its probability below by `P(L hits ∞) + P(R hits ∞) - P(error) - 1`.
Under translation invariance and almost-sure uniqueness of the infinite cluster, orbit boxes of a
common radius `n` around any two translates `zL`, `zR` are therefore joined with probability
`> 1 - ε` inside a large enough box.

Headline fidelity. Sections A and B are unconditional. The two results of section C are
conditional on `P.IsTranslationInvariant mu` and `mu {omega | P.HasUniqueInfiniteCluster omega} =
1` (no FKG needed). These are satisfiable hypotheses on one measure, so the results are not
vacuous. In the duality argument they are applied to the dual measure.

## ii. Key results

- `PeriodicGraph.finiteInfinitePairConnectionEvent_graphWalk_coordBounds` : an open embedded path
  between the two sets with explicit coordinate bounds.
- `PeriodicGraph.exists_uniformRadius_highProbability_translatedBoxPairConnection` : a common
  orbit-box radius for which any two translated boxes are joined with probability `> 1 - ε`.

## iii. Table of contents

- A. Coordinate bounds for orbit boxes and embedded walks
- B. Pair connection events between finite sets
- C. High-probability pair connections under uniqueness

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Coordinate bounds for orbit boxes and embedded walks -/

/-- The largest absolute value of the `i`-th embedded coordinate over the orbit box of radius `n`.
-/
noncomputable def PeriodicPlaneEmbedding.orbitBoxCoordinateBound
    (E : PeriodicPlaneEmbedding P) (n : Nat) (i : Fin 2) : Real :=
  (P.orbitBox n).sup'
    ⟨P.root, P.orbitBox_mono (Nat.zero_le n) P.root_mem_orbitBox_zero⟩
    (fun v => |E.vertexCoord v i|)

omit [Countable V] in
/-- Every vertex of the orbit box of radius `n` has `i`-th coordinate bounded by
`orbitBoxCoordinateBound n i`. -/
lemma PeriodicPlaneEmbedding.abs_vertexCoord_le_orbitBoxCoordinateBound
    (E : PeriodicPlaneEmbedding P) {n : Nat} {v : V}
    (hv : v ∈ P.orbitBox n) (i : Fin 2) :
    |E.vertexCoord v i| ≤ E.orbitBoxCoordinateBound n i := by
  classical
  unfold PeriodicPlaneEmbedding.orbitBoxCoordinateBound
  exact Finset.le_sup' (fun w => |E.vertexCoord w i|) hv

omit [Countable V] in
/-- An embedded walk whose vertices stay in the orbit box of radius `n` stays within
`orbitBoxCoordinateBound n i + B` in each coordinate, where `B` bounds the excursion of embedded
edges. -/
lemma PeriodicPlaneEmbedding.walkArc_abs_coord_le_of_support_orbitBox
    (E : PeriodicPlaneEmbedding P) {B : Real} (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {n : Nat} {x y : V} (q : P.graph.Walk x y)
    (hq : ∀ v ∈ q.support, v ∈ P.orbitBox n) :
    ∀ (t : unitInterval) (i : Fin 2),
      |E.coordinates (E.walkArc q t) i| ≤
        E.orbitBoxCoordinateBound n i + B := by
  intro t i
  have hpoint : E.walkArc q t ∈ Set.range (E.walkArc q) := ⟨t, rfl⟩
  rcases E.mem_walkArc_range_cases q hpoint with hstart | hedge
  · have hx := E.abs_vertexCoord_le_orbitBoxCoordinateBound
      (hq x (by simp)) i
    change E.walkArc q t = E.vertex x at hstart
    rw [hstart]
    change |E.vertexCoord x i| ≤ E.orbitBoxCoordinateBound n i + B
    linarith
  · obtain ⟨u, v, huv, huvEdge, s, hs⟩ := hedge
    have hu := E.abs_vertexCoord_le_orbitBoxCoordinateBound
      (hq u (q.fst_mem_support_of_mem_edges huvEdge)) i
    have hlo := E.vertex_sub_le_edgeArc_coord hB huv s i
    have hhi := E.edgeArc_coord_le_vertex_add hB huv s i
    change E.edgeArc huv s = E.walkArc q t at hs
    rw [← hs]
    rw [abs_le]
    rw [abs_le] at hu
    constructor <;> linarith

/-! ## B. Pair connection events between finite sets -/

/-- The event that some vertex of the finite set `L` lies in an infinite open cluster. See also
`PeriodicGraph.setHitsInfinite`, which takes a `Set` (same event for `(L : Set V)`). -/
def PeriodicGraph.finiteSetHitsInfinite
    (P : PeriodicGraph V) (L : Finset V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ L, (P.cluster omega x).Infinite}

/-- The event that a finite set hits the infinite cluster is measurable. See also
`PeriodicGraph.setHitsInfinite_measurableSet`. -/
lemma PeriodicGraph.finiteSetHitsInfinite_measurableSet
    (P : PeriodicGraph V) (L : Finset V) :
    MeasurableSet (P.finiteSetHitsInfinite L) := by
  have heq : P.finiteSetHitsInfinite L =
      ⋃ x ∈ L, {omega : ConfigSpace (Sym2 V) |
        (P.cluster omega x).Infinite} := by
    ext omega
    simp [PeriodicGraph.finiteSetHitsInfinite]
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    P.measurableSet_cluster_infinite x

omit [Countable V] in
/-- A translated orbit box hits the infinite cluster exactly on `translatedOrbitBoxHitsInfinite`. -/
lemma PeriodicGraph.finiteSetHitsInfinite_image_shift
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    P.finiteSetHitsInfinite ((P.orbitBox n).image (P.shift z)) =
      P.translatedOrbitBoxHitsInfinite z n := by
  ext omega
  simp [PeriodicGraph.finiteSetHitsInfinite,
    PeriodicGraph.translatedOrbitBoxHitsInfinite]

/-- The event that `L` and `R` both meet the infinite cluster and no pair-merge error occurs at
radius `N` between them: every pair of infinite-cluster vertices of `L` and `R` is joined inside the
orbit box. -/
def PeriodicGraph.finiteInfinitePairConnectionEvent
    (P : PeriodicGraph V) (L R : Finset V) (N : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  (P.finiteSetHitsInfinite L ∩ P.finiteSetHitsInfinite R) \
    P.pairMergeErrorUnion L R N

/-- The union of the pair-merge error events over `L × R` is measurable. -/
lemma PeriodicGraph.pairMergeErrorUnion_measurableSet
    (P : PeriodicGraph V) (L R : Finset V) (N : Nat) :
    MeasurableSet (P.pairMergeErrorUnion L R N) := by
  unfold PeriodicGraph.pairMergeErrorUnion
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
      P.pairMergeError_measurableSet x y N

/-- The pair connection event is measurable. -/
lemma PeriodicGraph.finiteInfinitePairConnectionEvent_measurableSet
    (P : PeriodicGraph V) (L R : Finset V) (N : Nat) :
    MeasurableSet (P.finiteInfinitePairConnectionEvent L R N) :=
  ((P.finiteSetHitsInfinite_measurableSet L).inter
    (P.finiteSetHitsInfinite_measurableSet R)).diff
      (P.pairMergeErrorUnion_measurableSet L R N)

omit [Countable V] in
/-- On the pair connection event there are infinite-cluster vertices `x ∈ L`, `y ∈ R` joined inside
the orbit box of radius `N`. -/
lemma PeriodicGraph.finiteInfinitePairConnectionEvent_witnesses
    (P : PeriodicGraph V) {omega : ConfigSpace (Sym2 V)}
    {L R : Finset V} {N : Nat}
    (h : omega ∈ P.finiteInfinitePairConnectionEvent L R N) :
    ∃ x ∈ L, (P.cluster omega x).Infinite ∧
      ∃ y ∈ R, (P.cluster omega y).Infinite ∧
        omega ∈ P.connectedWithinOrbit x y N := by
  rcases h.1.1 with ⟨x, hxL, hxinf⟩
  rcases h.1.2 with ⟨y, hyR, hyinf⟩
  refine ⟨x, hxL, hxinf, y, hyR, hyinf, ?_⟩
  by_contra hxy
  apply h.2
  simp only [PeriodicGraph.pairMergeErrorUnion, Set.mem_iUnion]
  exact ⟨x, ⟨hxL, y, ⟨hyR, ⟨⟨hxinf, hyinf⟩, hxy⟩⟩⟩⟩

omit [Countable V] in
/-- On the pair connection event there is an open walk from `L` to `R` inside the buffered orbit
box. -/
lemma PeriodicGraph.finiteInfinitePairConnectionEvent_graphWalk
    (P : PeriodicGraph V) {omega : ConfigSpace (Sym2 V)}
    {L R : Finset V} {N : Nat}
    (h : omega ∈ P.finiteInfinitePairConnectionEvent L R N) :
    ∃ x ∈ L, ∃ y ∈ R, ∃ q : P.graph.Walk x y,
      (∀ v ∈ q.support, v ∈ P.orbitBox (P.bufferedRadius N)) ∧
      ∀ {u v : V}, s(u, v) ∈ q.edges → omega s(u, v) = true := by
  obtain ⟨x, hxL, _hxinf, y, hyR, _hyinf, l, hchain, hlast, hbox⟩ :=
    P.finiteInfinitePairConnectionEvent_witnesses h
  let q₀ : (P.openSubgraph omega).Walk x ((x :: l).getLast (List.cons_ne_nil _ _)) :=
    SimpleGraph.Walk.ofSupport (x :: l) (List.cons_ne_nil _ _) hchain
  let q : (P.openSubgraph omega).Walk x y := q₀.copy rfl hlast
  obtain ⟨qG, hsupport, hopen⟩ :=
    P.openSubgraphWalk_exists_graphWalk omega q
  refine ⟨x, hxL, y, hyR, qG, ?_, hopen⟩
  intro v hv
  apply hbox v
  have hvq : v ∈ q.support := by rwa [← hsupport]
  have hvq₀ : v ∈ q₀.support := by simpa only [q, SimpleGraph.Walk.support_copy] using hvq
  rwa [show q₀.support = x :: l from SimpleGraph.Walk.support_ofSupport _ hchain] at hvq₀

omit [Countable V] in
/-- On the pair connection event there is an open walk from `L` to `R` whose embedding has
coordinates bounded by `orbitBoxCoordinateBound (bufferedRadius N) i + B`. -/
lemma PeriodicGraph.finiteInfinitePairConnectionEvent_graphWalk_coordBounds
    (P : PeriodicGraph V) (E : PeriodicPlaneEmbedding P)
    {B : Real} (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {omega : ConfigSpace (Sym2 V)} {L R : Finset V} {N : Nat}
    (h : omega ∈ P.finiteInfinitePairConnectionEvent L R N) :
    ∃ x ∈ L, ∃ y ∈ R, ∃ q : P.graph.Walk x y,
      (∀ {u v : V}, s(u, v) ∈ q.edges → omega s(u, v) = true) ∧
      ∀ (t : unitInterval) (i : Fin 2),
        |E.coordinates (E.walkArc q t) i| ≤
          E.orbitBoxCoordinateBound (P.bufferedRadius N) i + B := by
  obtain ⟨x, hx, y, hy, q, hsupport, hopen⟩ :=
    P.finiteInfinitePairConnectionEvent_graphWalk h
  refine ⟨x, hx, y, hy, q, hopen, ?_⟩
  exact E.walkArc_abs_coord_le_of_support_orbitBox hB0 hB q hsupport

/-- Inclusion–exclusion lower bound: `P(L hits ∞) + P(R hits ∞) - P(merge error) - 1` is at most the
probability of the pair connection event. -/
lemma PeriodicGraph.finiteInfinitePairConnectionEvent_measureReal_ge
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (L R : Finset V) (N : Nat) :
    mu.real (P.finiteSetHitsInfinite L) +
        mu.real (P.finiteSetHitsInfinite R) -
        mu.real (P.pairMergeErrorUnion L R N) - 1 ≤
      mu.real (P.finiteInfinitePairConnectionEvent L R N) := by
  let A := P.finiteSetHitsInfinite L
  let B := P.finiteSetHitsInfinite R
  let C := P.pairMergeErrorUnion L R N
  have hthree := three_event_intersection_lower_bound mu
    (P.finiteSetHitsInfinite_measurableSet R)
    (P.pairMergeErrorUnion_measurableSet L R N).compl
    (A := A) (B := B) (C := Cᶜ)
  have hC : mu.real Cᶜ = 1 - mu.real C := by
    rw [measureReal_compl (P.pairMergeErrorUnion_measurableSet L R N),
      probReal_univ]
  rw [hC] at hthree
  change mu.real A + mu.real B - mu.real C - 1 ≤
    mu.real ((A ∩ B) \ C)
  convert hthree using 1 <;> first | ring | simp [Set.sdiff_eq]

/-! ## C. High-probability pair connections under uniqueness -/

/-- Under translation invariance and a.s. uniqueness of the infinite cluster, orbit boxes around any
two translates are joined with probability `> 1 - ε` for large enough radii. -/
lemma PeriodicGraph.exists_highProbability_translatedBoxPairConnection
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (zL zR : Site 2) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ n N : Nat,
      1 - epsilon < mu.real
        (P.finiteInfinitePairConnectionEvent
          ((P.orbitBox n).image (P.shift zL))
          ((P.orbitBox n).image (P.shift zR)) N) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun omega h => h.1
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hev : ∀ᶠ n in atTop,
      1 - epsilon / 4 < mu.real (P.orbitBoxHitsInfinite n) :=
    (tendsto_order.1 hhit).1 _ (by linarith)
  obtain ⟨n, hn⟩ := hev.exists
  let L := (P.orbitBox n).image (P.shift zL)
  let R := (P.orbitBox n).image (P.shift zR)
  have hmergeT := P.pairMergeErrorUnion_real_tendsto_zero mu hunique L R
  have hmergeEv : ∀ᶠ N in atTop,
      mu.real (P.pairMergeErrorUnion L R N) < epsilon / 2 :=
    (tendsto_order.1 hmergeT).2 _ (half_pos hepsilon)
  obtain ⟨N, hN⟩ := hmergeEv.exists
  have hL : mu.real (P.finiteSetHitsInfinite L) =
      mu.real (P.orbitBoxHitsInfinite n) := by
    rw [P.finiteSetHitsInfinite_image_shift]
    exact congrArg ENNReal.toReal
      (P.translatedOrbitBoxHitsInfinite_measure_eq mu hTI zL n)
  have hR : mu.real (P.finiteSetHitsInfinite R) =
      mu.real (P.orbitBoxHitsInfinite n) := by
    rw [P.finiteSetHitsInfinite_image_shift]
    exact congrArg ENNReal.toReal
      (P.translatedOrbitBoxHitsInfinite_measure_eq mu hTI zR n)
  refine ⟨n, N, ?_⟩
  have hbound := P.finiteInfinitePairConnectionEvent_measureReal_ge
    mu L R N
  dsimp only [L, R] at hbound ⊢
  rw [hL, hR] at hbound
  dsimp only [L, R] at hN
  linarith

/-- Uniform version: one orbit-box radius `n` works for all pairs of translates `zL`, `zR`, with a
connection radius `N` depending on the pair (translation invariance, a.s. uniqueness). -/
lemma PeriodicGraph.exists_uniformRadius_highProbability_translatedBoxPairConnection
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ n : Nat, ∀ zL zR : Site 2, ∃ N : Nat,
      1 - epsilon < mu.real
        (P.finiteInfinitePairConnectionEvent
          ((P.orbitBox n).image (P.shift zL))
          ((P.orbitBox n).image (P.shift zR)) N) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun omega h => h.1
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hev : ∀ᶠ n in atTop,
      1 - epsilon / 4 < mu.real (P.orbitBoxHitsInfinite n) :=
    (tendsto_order.1 hhit).1 _ (by linarith)
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨n, ?_⟩
  intro zL zR
  let L := (P.orbitBox n).image (P.shift zL)
  let R := (P.orbitBox n).image (P.shift zR)
  have hmergeT := P.pairMergeErrorUnion_real_tendsto_zero mu hunique L R
  have hmergeEv : ∀ᶠ N in atTop,
      mu.real (P.pairMergeErrorUnion L R N) < epsilon / 2 :=
    (tendsto_order.1 hmergeT).2 _ (half_pos hepsilon)
  obtain ⟨N, hN⟩ := hmergeEv.exists
  have hL : mu.real (P.finiteSetHitsInfinite L) =
      mu.real (P.orbitBoxHitsInfinite n) := by
    rw [P.finiteSetHitsInfinite_image_shift]
    exact congrArg ENNReal.toReal
      (P.translatedOrbitBoxHitsInfinite_measure_eq mu hTI zL n)
  have hR : mu.real (P.finiteSetHitsInfinite R) =
      mu.real (P.orbitBoxHitsInfinite n) := by
    rw [P.finiteSetHitsInfinite_image_shift]
    exact congrArg ENNReal.toReal
      (P.translatedOrbitBoxHitsInfinite_measure_eq mu hTI zR n)
  refine ⟨N, ?_⟩
  have hbound := P.finiteInfinitePairConnectionEvent_measureReal_ge
    mu L R N
  dsimp only [L, R] at hbound hN ⊢
  rw [hL, hR] at hbound
  linarith

end StatMech.FK.PeriodicPlanar
