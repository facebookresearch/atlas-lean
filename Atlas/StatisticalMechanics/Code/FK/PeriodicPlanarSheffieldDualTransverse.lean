/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms









open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



noncomputable def PeriodicPlaneEmbedding.orbitBoxCoordinateBound
    (E : PeriodicPlaneEmbedding P) (n : Nat) (i : Fin 2) : Real :=
  (P.orbitBox n).sup'
    ⟨P.root, P.orbitBox_mono (Nat.zero_le n) P.root_mem_orbitBox_zero⟩
    (fun v => |E.vertexCoord v i|)

theorem PeriodicPlaneEmbedding.abs_vertexCoord_le_orbitBoxCoordinateBound
    (E : PeriodicPlaneEmbedding P) {n : Nat} {v : V}
    (hv : v ∈ P.orbitBox n) (i : Fin 2) :
    |E.vertexCoord v i| ≤ E.orbitBoxCoordinateBound n i := by
  classical
  unfold PeriodicPlaneEmbedding.orbitBoxCoordinateBound
  exact Finset.le_sup' (fun w => |E.vertexCoord w i|) hv



theorem PeriodicPlaneEmbedding.walkArc_abs_coord_le_of_support_orbitBox
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


def PeriodicGraph.finiteSetHitsInfinite
    (P : PeriodicGraph V) (L : Finset V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ L, (P.cluster omega x).Infinite}

theorem PeriodicGraph.finiteSetHitsInfinite_measurableSet
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

theorem PeriodicGraph.finiteSetHitsInfinite_image_shift
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    P.finiteSetHitsInfinite ((P.orbitBox n).image (P.shift z)) =
      P.translatedOrbitBoxHitsInfinite z n := by
  ext omega
  simp [PeriodicGraph.finiteSetHitsInfinite,
    PeriodicGraph.translatedOrbitBoxHitsInfinite]



def PeriodicGraph.finiteInfinitePairConnectionEvent
    (P : PeriodicGraph V) (L R : Finset V) (N : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  (P.finiteSetHitsInfinite L ∩ P.finiteSetHitsInfinite R) \
    P.pairMergeErrorUnion L R N

theorem PeriodicGraph.pairMergeErrorUnion_measurableSet
    (P : PeriodicGraph V) (L R : Finset V) (N : Nat) :
    MeasurableSet (P.pairMergeErrorUnion L R N) := by
  unfold PeriodicGraph.pairMergeErrorUnion
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
      P.pairMergeError_measurableSet x y N

theorem PeriodicGraph.finiteInfinitePairConnectionEvent_measurableSet
    (P : PeriodicGraph V) (L R : Finset V) (N : Nat) :
    MeasurableSet (P.finiteInfinitePairConnectionEvent L R N) :=
  ((P.finiteSetHitsInfinite_measurableSet L).inter
    (P.finiteSetHitsInfinite_measurableSet R)).diff
      (P.pairMergeErrorUnion_measurableSet L R N)



theorem PeriodicGraph.finiteInfinitePairConnectionEvent_witnesses
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


theorem PeriodicGraph.finiteInfinitePairConnectionEvent_graphWalk
    (P : PeriodicGraph V) {omega : ConfigSpace (Sym2 V)}
    {L R : Finset V} {N : Nat}
    (h : omega ∈ P.finiteInfinitePairConnectionEvent L R N) :
    ∃ x ∈ L, ∃ y ∈ R, ∃ q : P.graph.Walk x y,
      (∀ v ∈ q.support, v ∈ P.orbitBox (P.bufferedRadius N)) ∧
      ∀ {u v : V}, s(u, v) ∈ q.edges → omega s(u, v) = true := by
  obtain ⟨x, hxL, _hxinf, y, hyR, _hyinf, l, hchain, hlast, hbox⟩ :=
    P.finiteInfinitePairConnectionEvent_witnesses h
  let q₀ := walkOfChain (P.openSubgraph omega) x l hchain
  let q : (P.openSubgraph omega).Walk x y := q₀.copy rfl hlast
  obtain ⟨qG, hsupport, hopen⟩ :=
    P.openSubgraphWalk_exists_graphWalk omega q
  refine ⟨x, hxL, y, hyR, qG, ?_, hopen⟩
  intro v hv
  apply hbox v
  have hvq : v ∈ q.support := by rwa [← hsupport]
  simpa only [q, SimpleGraph.Walk.support_copy, q₀, walkOfChain_support]
    using hvq



theorem PeriodicGraph.finiteInfinitePairConnectionEvent_graphWalk_coordBounds
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


theorem PeriodicGraph.finiteInfinitePairConnectionEvent_measureReal_ge
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
  convert hthree using 1 <;> ring




theorem PeriodicGraph.exists_highProbability_translatedBoxPairConnection
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



theorem PeriodicGraph.exists_uniformRadius_highProbability_translatedBoxPairConnection
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
