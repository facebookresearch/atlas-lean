/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldAxisSwap










open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def PeriodicPlaneEmbedding.rectBottomBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) : Set V :=
  {x | x ∈ E.rectVertices a b c d ∧
    ∃ y, P.graph.Adj x y ∧ E.vertexCoord y 1 < c}

def PeriodicPlaneEmbedding.rectTopBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) : Set V :=
  {x | x ∈ E.rectVertices a b c d ∧
    ∃ y, P.graph.Adj x y ∧ d < E.vertexCoord y 1}

def PeriodicPlaneEmbedding.rectLeftBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) : Set V :=
  {x | x ∈ E.rectVertices a b c d ∧
    ∃ y, P.graph.Adj x y ∧ E.vertexCoord y 0 < a}

def PeriodicPlaneEmbedding.rectRightBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) : Set V :=
  {x | x ∈ E.rectVertices a b c d ∧
    ∃ y, P.graph.Adj x y ∧ b < E.vertexCoord y 0}




def PeriodicPlaneEmbedding.rectSideConnectionEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (S side : Set V) : Set (ConfigSpace (Sym2 V)) :=
  P.infiniteSetConnectionWithin (E.rectVertices a b c d) S side

theorem PeriodicPlaneEmbedding.rectSideConnectionEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S side : Set V) :
    MeasurableSet (E.rectSideConnectionEvent a b c d S side) :=
  P.infiniteSetConnectionWithin_measurableSet
    (E.rectVertices a b c d) S side

theorem PeriodicPlaneEmbedding.rectSideConnectionEvent_isIncreasing
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S side : Set V) :
    IsIncreasing (E.rectSideConnectionEvent a b c d S side) :=
  P.infiniteSetConnectionWithin_isIncreasing
    (E.rectVertices a b c d) S side



theorem PeriodicPlaneEmbedding.setHitsInfinite_subset_rectSideConnection_union
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S : Set V)
    (hS : S ⊆ E.rectVertices a b c d) :
    P.setHitsInfinite S ⊆
      E.rectSideConnectionEvent a b c d S
          (E.rectBottomBoundaryVertices a b c d) ∪
        (E.rectSideConnectionEvent a b c d S
            (E.rectTopBoundaryVertices a b c d) ∪
          (E.rectSideConnectionEvent a b c d S
              (E.rectLeftBoundaryVertices a b c d) ∪
            E.rectSideConnectionEvent a b c d S
              (E.rectRightBoundaryVertices a b c d))) := by
  intro omega homega
  obtain ⟨x, hxS, hxinf⟩ := homega
  obtain ⟨y, hycluster, hyout⟩ :=
    hxinf.exists_notMem_finite (E.rectVertices_finite a b c d)
  obtain ⟨p⟩ := hycluster
  obtain ⟨v, hvRect, z, hvz, hzout, q, hqRect, _hqsub⟩ :=
    P.exists_boundary_walk_of_walk_to_compl omega
      (E.rectVertices a b c d) p (hS hxS) hyout
  have hxv : omega ∈ P.connectedWithinSet (E.rectVertices a b c d) x v :=
    P.mem_connectedWithinSet_of_walk q hqRect
  by_cases hzLeft : E.vertexCoord z 0 < a
  · exact Or.inr (Or.inr (Or.inl
      ⟨x, hxS, hxinf, v, ⟨hvRect, z, hvz, hzLeft⟩, hxv⟩))
  by_cases hzRight : b < E.vertexCoord z 0
  · exact Or.inr (Or.inr (Or.inr
      ⟨x, hxS, hxinf, v, ⟨hvRect, z, hvz, hzRight⟩, hxv⟩))
  by_cases hzBottom : E.vertexCoord z 1 < c
  · exact Or.inl ⟨x, hxS, hxinf, v, ⟨hvRect, z, hvz, hzBottom⟩, hxv⟩
  have hzTop : d < E.vertexCoord z 1 := by
    apply lt_of_not_ge
    intro hzd
    apply hzout
    exact ⟨le_of_not_gt hzLeft, le_of_not_gt hzRight,
      le_of_not_gt hzBottom, hzd⟩
  exact Or.inr (Or.inl
    ⟨x, hxS, hxinf, v, ⟨hvRect, z, hvz, hzTop⟩, hxv⟩)



def PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  ⋃ x ∈ L, ⋃ y ∈ R,
    (({omega | (P.cluster omega x).Infinite} ∩
      {omega | (P.cluster omega y).Infinite}) \
        P.connectedWithinSet (E.rectVertices a b c d) x y)

theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    MeasurableSet (E.rectanglePairMergeErrorUnion a b c d L R) := by
  unfold PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
      ((P.measurableSet_cluster_infinite x).inter
        (P.measurableSet_cluster_infinite y)).diff
          (P.connectedWithinSet_measurableSet
            (E.rectVertices a b c d) x y)

omit [Countable V] in theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_mono_sources
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    {L R L' R' : Finset V} (hL : L ⊆ L') (hR : R ⊆ R') :
    E.rectanglePairMergeErrorUnion a b c d L R ⊆
      E.rectanglePairMergeErrorUnion a b c d L' R' := by
  intro omega homega
  obtain ⟨x, hxL, y, hyR, hxy⟩ := by
    simpa only [PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion,
      Set.mem_iUnion] using homega
  apply Set.mem_iUnion.2
  exact ⟨x, Set.mem_iUnion.2 ⟨hL hxL, Set.mem_iUnion.2 ⟨y,
    Set.mem_iUnion.2 ⟨hR hyR, hxy⟩⟩⟩⟩

theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_mono_sources
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (a b c d : Real) {L R L' R' : Finset V}
    (hL : L ⊆ L') (hR : R ⊆ R') :
    mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
      mu.real (E.rectanglePairMergeErrorUnion a b c d L' R') :=
  measureReal_mono (E.rectanglePairMergeErrorUnion_mono_sources
    a b c d hL hR)

omit [Countable V] in theorem PeriodicGraph.connectedWithinOrbit_subset_connectedWithinSet
    (P : PeriodicGraph V) {A : Set V} {x y : V} {N : Nat}
    (hbox : (P.orbitBox (P.bufferedRadius N) : Set V) ⊆ A) :
    P.connectedWithinOrbit x y N ⊆ P.connectedWithinSet A x y := by
  rintro omega ⟨l, hchain, hlast, hsupport⟩
  exact ⟨l, hchain, hlast, fun v hv => hbox (hsupport v hv)⟩



theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_subset_pairMergeErrorUnion
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (L R : Finset V) (N : Nat)
    (hbox : (P.orbitBox (P.bufferedRadius N) : Set V) ⊆
      E.rectVertices a b c d) :
    E.rectanglePairMergeErrorUnion a b c d L R ⊆
      P.pairMergeErrorUnion L R N := by
  intro omega homega
  obtain ⟨x, hxL, y, hyR, hinf, hnotRect⟩ := by
    simpa only [PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion,
      Set.mem_iUnion, Set.mem_diff, Set.mem_inter_iff,
      Set.mem_setOf_eq] using homega
  apply Set.mem_iUnion.2
  refine ⟨x, Set.mem_iUnion.2 ⟨hxL, Set.mem_iUnion.2 ⟨y,
    Set.mem_iUnion.2 ⟨hyR, ⟨hinf, ?_⟩⟩⟩⟩⟩
  intro horbit
  exact hnotRect
    (P.connectedWithinOrbit_subset_connectedWithinSet hbox horbit)

theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (a b c d : Real) (L R : Finset V) (N : Nat)
    (hbox : (P.orbitBox (P.bufferedRadius N) : Set V) ⊆
      E.rectVertices a b c d) :
    mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
      mu.real (P.pairMergeErrorUnion L R N) :=
  measureReal_mono
    (E.rectanglePairMergeErrorUnion_subset_pairMergeErrorUnion
      a b c d L R N hbox)




theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (a b c d : Nat → Real) (L R : Finset V)
    (hbox : ∀ N, (P.orbitBox (P.bufferedRadius N) : Set V) ⊆
      E.rectVertices (a N) (b N) (c N) (d N)) :
    Tendsto (fun N => mu.real
      (E.rectanglePairMergeErrorUnion (a N) (b N) (c N) (d N) L R))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro N
    exact measureReal_nonneg
  · intro N
    exact E.rectanglePairMergeErrorUnion_measureReal_le
      mu (a N) (b N) (c N) (d N) L R N (hbox N)
  · exact P.pairMergeErrorUnion_real_tendsto_zero mu hunique L R



theorem PeriodicPlaneEmbedding.configTranslate_preimage_rectanglePairMergeErrorUnion_subset
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (a b c d : Real)
    (L R : Finset V) (N : Nat)
    (hbox : (P.shift z '' (P.orbitBox (P.bufferedRadius N) : Set V)) ⊆
      E.rectVertices a b c d) :
    P.configTranslate z ⁻¹'
        E.rectanglePairMergeErrorUnion a b c d
          (L.image (P.shift z)) (R.image (P.shift z)) ⊆
      P.pairMergeErrorUnion L R N := by
  intro omega homega
  change P.configTranslate z omega ∈
    E.rectanglePairMergeErrorUnion a b c d
      (L.image (P.shift z)) (R.image (P.shift z)) at homega
  obtain ⟨xz, hxzL, yz, hyzR, hinf, hnotRect⟩ := by
    simpa only [PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion,
      Set.mem_iUnion, Set.mem_diff, Set.mem_inter_iff,
      Set.mem_setOf_eq] using homega
  obtain ⟨x, hxL, hxxz⟩ := Finset.mem_image.mp hxzL
  obtain ⟨y, hyR, hyyz⟩ := Finset.mem_image.mp hyzR
  subst xz
  subst yz
  have hxinf : (P.cluster omega x).Infinite :=
    (P.cluster_infinite_configTranslate z omega x).mp hinf.1
  have hyinf : (P.cluster omega y).Infinite :=
    (P.cluster_infinite_configTranslate z omega y).mp hinf.2
  apply Set.mem_iUnion.2
  refine ⟨x, Set.mem_iUnion.2 ⟨hxL, Set.mem_iUnion.2 ⟨y,
    Set.mem_iUnion.2 ⟨hyR, ⟨⟨hxinf, hyinf⟩, ?_⟩⟩⟩⟩⟩
  intro horbit
  have hshiftConn : P.configTranslate z omega ∈
      P.connectedWithinSet
        (P.shift z '' (P.orbitBox (P.bufferedRadius N) : Set V))
        (P.shift z x) (P.shift z y) := by
    apply (P.connectedWithinSet_configTranslate z omega
      (P.orbitBox (P.bufferedRadius N) : Set V) x y).2
    exact P.connectedWithinOrbit_subset_connectedWithinSet
      (fun _ h => h) horbit
  exact hnotRect
    (P.connectedWithinSet_mono_region hbox (P.shift z x) (P.shift z y)
      hshiftConn)

theorem PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Site 2) (a b c d : Real) (L R : Finset V) (N : Nat)
    (hbox : (P.shift z '' (P.orbitBox (P.bufferedRadius N) : Set V)) ⊆
      E.rectVertices a b c d) :
    mu.real (E.rectanglePairMergeErrorUnion a b c d
        (L.image (P.shift z)) (R.image (P.shift z))) ≤
      mu.real (P.pairMergeErrorUnion L R N) := by
  let A := E.rectanglePairMergeErrorUnion a b c d
    (L.image (P.shift z)) (R.image (P.shift z))
  have hmeasure := P.translateEvent_measure_eq mu hTI z
    (E.rectanglePairMergeErrorUnion_measurableSet a b c d
      (L.image (P.shift z)) (R.image (P.shift z)))
  have hreal : mu.real (P.configTranslate z ⁻¹' A) = mu.real A :=
    congrArg ENNReal.toReal hmeasure
  rw [← hreal]
  exact measureReal_mono
    (E.configTranslate_preimage_rectanglePairMergeErrorUnion_subset
      z a b c d L R N hbox)




theorem PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_measureReal_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (z : Nat → Site 2) (a b c d : Nat → Real) (L R : Finset V)
    (hbox : ∀ N,
      (P.shift (z N) '' (P.orbitBox (P.bufferedRadius N) : Set V)) ⊆
        E.rectVertices (a N) (b N) (c N) (d N)) :
    Tendsto (fun N => mu.real
      (E.rectanglePairMergeErrorUnion (a N) (b N) (c N) (d N)
        (L.image (P.shift (z N))) (R.image (P.shift (z N)))))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro N
    exact measureReal_nonneg
  · intro N
    exact E.translated_rectanglePairMergeErrorUnion_measureReal_le
      mu hTI (z N) (a N) (b N) (c N) (d N) L R N (hbox N)
  · exact P.pairMergeErrorUnion_real_tendsto_zero mu hunique L R



def PeriodicPlaneEmbedding.finiteRectangleJoinedVerticalEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (P.infiniteSetConnectionWithin (E.rectVertices a b c d) (L : Set V)
      (E.rectBottomBoundaryVertices a b c d) ∩
    P.infiniteSetConnectionWithin (E.rectVertices a b c d) (R : Set V)
      (E.rectTopBoundaryVertices a b c d)) \
    E.rectanglePairMergeErrorUnion a b c d L R

theorem PeriodicPlaneEmbedding.finiteRectangleJoinedVerticalEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    MeasurableSet (E.finiteRectangleJoinedVerticalEvent a b c d L R) :=
  ((P.infiniteSetConnectionWithin_measurableSet
      (E.rectVertices a b c d) (L : Set V)
      (E.rectBottomBoundaryVertices a b c d)).inter
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rectVertices a b c d) (R : Set V)
      (E.rectTopBoundaryVertices a b c d))).diff
    (E.rectanglePairMergeErrorUnion_measurableSet a b c d L R)



theorem PeriodicPlaneEmbedding.finiteRectangleJoinedVerticalEvent_subset_verticalCrossing
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    E.finiteRectangleJoinedVerticalEvent a b c d L R ⊆
      E.verticalCrossingEvent a b c d := by
  intro omega homega
  obtain ⟨x, hxL, hxinf, xb, hxbBottom, hxxb⟩ := homega.1.1
  obtain ⟨y, hyR, hyinf, yt, hytTop, hyyt⟩ := homega.1.2
  have hxy : omega ∈
      P.connectedWithinSet (E.rectVertices a b c d) x y := by
    by_contra hnot
    apply homega.2
    apply Set.mem_iUnion.2
    refine ⟨x, Set.mem_iUnion.2 ⟨hxL, Set.mem_iUnion.2 ⟨y,
      Set.mem_iUnion.2 ⟨hyR, ?_⟩⟩⟩⟩
    exact ⟨⟨hxinf, hyinf⟩, hnot⟩
  obtain ⟨qxb, hqxb⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxxb
  obtain ⟨qxy, hqxy⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  obtain ⟨qyt, hqyt⟩ := P.connectedWithinSet_exists_openSubgraphWalk hyyt
  let q : (P.openSubgraph omega).Walk xb yt :=
    qxb.reverse.append (qxy.append qyt)
  have hqRect : ∀ v ∈ q.support, v ∈ E.rectVertices a b c d := by
    intro v hv
    dsimp only [q] at hv
    rw [SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hqxb v (by simpa using hv)
    · rw [SimpleGraph.Walk.support_append] at hv
      rcases List.mem_append.mp (List.mem_of_mem_tail hv) with hv | hv
      · exact hqxy v hv
      · exact hqyt v (List.mem_of_mem_tail hv)
  have hxbRect := hqRect xb q.start_mem_support
  have hytRect := hqRect yt q.end_mem_support
  have hbottom : E.rectBottomBoundary a b c d ⟨xb, hxbRect⟩ := by
    exact hxbBottom.2
  have htop : E.rectTopBoundary a b c d ⟨yt, hytRect⟩ := by
    exact hytTop.2
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices a b c d)).Reachable
        ⟨xb, hxbRect⟩ ⟨yt, hytRect⟩ :=
    ⟨q.induce (E.rectVertices a b c d) hqRect⟩
  change E.rectRestrict a b c d omega ∈ E.finiteVerticalCrossing a b c d
  refine ⟨⟨xb, hxbRect⟩, ⟨yt, hytRect⟩, hbottom, htop, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach


def PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (P.infiniteSetConnectionWithin (E.rectVertices a b c d) (L : Set V)
      (E.rectLeftBoundaryVertices a b c d) ∩
    P.infiniteSetConnectionWithin (E.rectVertices a b c d) (R : Set V)
      (E.rectRightBoundaryVertices a b c d)) \
    E.rectanglePairMergeErrorUnion a b c d L R

theorem PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    MeasurableSet (E.finiteRectangleJoinedHorizontalEvent a b c d L R) :=
  ((P.infiniteSetConnectionWithin_measurableSet
      (E.rectVertices a b c d) (L : Set V)
      (E.rectLeftBoundaryVertices a b c d)).inter
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rectVertices a b c d) (R : Set V)
      (E.rectRightBoundaryVertices a b c d))).diff
    (E.rectanglePairMergeErrorUnion_measurableSet a b c d L R)



theorem PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent_subset_horizontalCrossing
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    E.finiteRectangleJoinedHorizontalEvent a b c d L R ⊆
      E.horizontalCrossingEvent a b c d := by
  intro omega homega
  obtain ⟨x, hxL, hxinf, xl, hxlLeft, hxxl⟩ := homega.1.1
  obtain ⟨y, hyR, hyinf, yr, hyrRight, hyyr⟩ := homega.1.2
  have hxy : omega ∈
      P.connectedWithinSet (E.rectVertices a b c d) x y := by
    by_contra hnot
    apply homega.2
    apply Set.mem_iUnion.2
    refine ⟨x, Set.mem_iUnion.2 ⟨hxL, Set.mem_iUnion.2 ⟨y,
      Set.mem_iUnion.2 ⟨hyR, ?_⟩⟩⟩⟩
    exact ⟨⟨hxinf, hyinf⟩, hnot⟩
  obtain ⟨qxl, hqxl⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxxl
  obtain ⟨qxy, hqxy⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  obtain ⟨qyr, hqyr⟩ := P.connectedWithinSet_exists_openSubgraphWalk hyyr
  let q : (P.openSubgraph omega).Walk xl yr :=
    qxl.reverse.append (qxy.append qyr)
  have hqRect : ∀ v ∈ q.support, v ∈ E.rectVertices a b c d := by
    intro v hv
    dsimp only [q] at hv
    rw [SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hqxl v (by simpa using hv)
    · rw [SimpleGraph.Walk.support_append] at hv
      rcases List.mem_append.mp (List.mem_of_mem_tail hv) with hv | hv
      · exact hqxy v hv
      · exact hqyr v (List.mem_of_mem_tail hv)
  have hxlRect := hqRect xl q.start_mem_support
  have hyrRect := hqRect yr q.end_mem_support
  have hleft : E.rectLeftBoundary a b c d ⟨xl, hxlRect⟩ := hxlLeft.2
  have hright : E.rectRightBoundary a b c d ⟨yr, hyrRect⟩ := hyrRight.2
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices a b c d)).Reachable
        ⟨xl, hxlRect⟩ ⟨yr, hyrRect⟩ :=
    ⟨q.induce (E.rectVertices a b c d) hqRect⟩
  change E.rectRestrict a b c d omega ∈ E.finiteHorizontalCrossing a b c d
  refine ⟨⟨xl, hxlRect⟩, ⟨yr, hyrRect⟩, hleft, hright, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach




theorem PeriodicPlaneEmbedding.verticalCrossing_measureReal_ge_side_mul_sub_mergeError
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V) :
    mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d)) *
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d)) -
      mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
        mu.real (E.verticalCrossingEvent a b c d) := by
  let A := E.rectSideConnectionEvent a b c d (L : Set V)
    (E.rectBottomBoundaryVertices a b c d)
  let B := E.rectSideConnectionEvent a b c d (R : Set V)
    (E.rectTopBoundaryVertices a b c d)
  let M := E.rectanglePairMergeErrorUnion a b c d L R
  have hinter : mu.real A * mu.real B ≤ mu.real (A ∩ B) :=
    hFKG A B
      (E.rectSideConnectionEvent_measurableSet a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d))
  have hdiff : mu.real (A ∩ B) - mu.real M ≤
      mu.real ((A ∩ B) \ M) := le_measureReal_diff
  have hjoined : mu.real ((A ∩ B) \ M) ≤
      mu.real (E.verticalCrossingEvent a b c d) :=
    measureReal_mono
      (E.finiteRectangleJoinedVerticalEvent_subset_verticalCrossing
        a b c d L R)
  dsimp only [A, B, M] at hinter hdiff hjoined ⊢
  linarith


theorem PeriodicPlaneEmbedding.horizontalCrossing_measureReal_ge_side_mul_sub_mergeError
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V) :
    mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectLeftBoundaryVertices a b c d)) *
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d)) -
      mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
        mu.real (E.horizontalCrossingEvent a b c d) := by
  let A := E.rectSideConnectionEvent a b c d (L : Set V)
    (E.rectLeftBoundaryVertices a b c d)
  let B := E.rectSideConnectionEvent a b c d (R : Set V)
    (E.rectRightBoundaryVertices a b c d)
  let M := E.rectanglePairMergeErrorUnion a b c d L R
  have hinter : mu.real A * mu.real B ≤ mu.real (A ∩ B) :=
    hFKG A B
      (E.rectSideConnectionEvent_measurableSet a b c d (L : Set V)
        (E.rectLeftBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d (L : Set V)
        (E.rectLeftBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d))
  have hdiff : mu.real (A ∩ B) - mu.real M ≤
      mu.real ((A ∩ B) \ M) := le_measureReal_diff
  have hjoined : mu.real ((A ∩ B) \ M) ≤
      mu.real (E.horizontalCrossingEvent a b c d) :=
    measureReal_mono
      (E.finiteRectangleJoinedHorizontalEvent_subset_horizontalCrossing
        a b c d L R)
  dsimp only [A, B, M] at hinter hdiff hjoined ⊢
  linarith



theorem PeriodicPlaneEmbedding.setHitsInfinite_inter_rectSide_diff_mergeError_subset_rectSide
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (L R : Finset V) (side : Set V) :
    (P.setHitsInfinite (R : Set V) ∩
      E.rectSideConnectionEvent a b c d (L : Set V) side) \
        E.rectanglePairMergeErrorUnion a b c d L R ⊆
      E.rectSideConnectionEvent a b c d (R : Set V) side := by
  intro omega homega
  obtain ⟨y, hyR, hyinf⟩ := homega.1.1
  obtain ⟨x, hxL, hxinf, v, hvside, hxv⟩ := homega.1.2
  have hxy : omega ∈
      P.connectedWithinSet (E.rectVertices a b c d) x y := by
    by_contra hnot
    apply homega.2
    apply Set.mem_iUnion.2
    refine ⟨x, Set.mem_iUnion.2 ⟨hxL, Set.mem_iUnion.2 ⟨y,
      Set.mem_iUnion.2 ⟨hyR, ⟨⟨hxinf, hyinf⟩, hnot⟩⟩⟩⟩⟩
  obtain ⟨qxy, hqxy⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  obtain ⟨qxv, hqxv⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxv
  let q : (P.openSubgraph omega).Walk y v := qxy.reverse.append qxv
  have hqRect : ∀ w ∈ q.support, w ∈ E.rectVertices a b c d := by
    intro w hw
    dsimp only [q] at hw
    rw [SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse] at hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hqxy w (by simpa using hw)
    · exact hqxv w (List.mem_of_mem_tail hw)
  exact ⟨y, hyR, hyinf, v, hvside,
    P.mem_connectedWithinSet_of_walk q hqRect⟩




theorem PeriodicPlaneEmbedding.rectSide_measureReal_ge_hits_mul_side_sub_mergeError
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real)
    (L R : Finset V) (side : Set V) :
    mu.real (P.setHitsInfinite (R : Set V)) *
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V) side) -
      mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
        mu.real (E.rectSideConnectionEvent a b c d (R : Set V) side) := by
  let H := P.setHitsInfinite (R : Set V)
  let A := E.rectSideConnectionEvent a b c d (L : Set V) side
  let M := E.rectanglePairMergeErrorUnion a b c d L R
  have hinter : mu.real H * mu.real A ≤ mu.real (H ∩ A) :=
    hFKG H A (P.setHitsInfinite_measurableSet (R : Set V))
      (E.rectSideConnectionEvent_measurableSet a b c d (L : Set V) side)
      (P.setHitsInfinite_isIncreasing (R : Set V))
      (E.rectSideConnectionEvent_isIncreasing a b c d (L : Set V) side)
  have hdiff : mu.real (H ∩ A) - mu.real M ≤
      mu.real ((H ∩ A) \ M) := le_measureReal_diff
  have htransfer : mu.real ((H ∩ A) \ M) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V) side) :=
    measureReal_mono
      (E.setHitsInfinite_inter_rectSide_diff_mergeError_subset_rectSide
        a b c d L R side)
  dsimp only [H, A, M] at hinter hdiff htransfer ⊢
  linarith




theorem PeriodicPlaneEmbedding.verticalCrossing_ge_preferredSide_transfer
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V)
    (hOpposite :
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d))) :
    let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectBottomBoundaryVertices a b c d))
    let H := mu.real (P.setHitsInfinite (R : Set V))
    let M := mu.real (E.rectanglePairMergeErrorUnion a b c d L R)
    A * (H * A - M) - M ≤
      mu.real (E.verticalCrossingEvent a b c d) := by
  dsimp only
  have htransfer := E.rectSide_measureReal_ge_hits_mul_side_sub_mergeError
    mu hFKG a b c d L R (E.rectBottomBoundaryVertices a b c d)
  have htop :
      mu.real (P.setHitsInfinite (R : Set V)) *
        mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
          (E.rectBottomBoundaryVertices a b c d)) -
        mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d)) := htransfer.trans hOpposite
  have hAnonneg : 0 ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d)) := measureReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left htop hAnonneg
  have hcross := E.verticalCrossing_measureReal_ge_side_mul_sub_mergeError
    mu hFKG a b c d L R
  nlinarith


theorem PeriodicPlaneEmbedding.horizontalCrossing_ge_preferredSide_transfer
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V)
    (hOpposite :
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d))) :
    let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectLeftBoundaryVertices a b c d))
    let H := mu.real (P.setHitsInfinite (R : Set V))
    let M := mu.real (E.rectanglePairMergeErrorUnion a b c d L R)
    A * (H * A - M) - M ≤
      mu.real (E.horizontalCrossingEvent a b c d) := by
  dsimp only
  have htransfer := E.rectSide_measureReal_ge_hits_mul_side_sub_mergeError
    mu hFKG a b c d L R (E.rectLeftBoundaryVertices a b c d)
  have hright :
      mu.real (P.setHitsInfinite (R : Set V)) *
        mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
          (E.rectLeftBoundaryVertices a b c d)) -
        mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d)) := htransfer.trans hOpposite
  have hAnonneg : 0 ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectLeftBoundaryVertices a b c d)) := measureReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left hright hAnonneg
  have hcross := E.horizontalCrossing_measureReal_ge_side_mul_sub_mergeError
    mu hFKG a b c d L R
  nlinarith



theorem dominant_of_four_event_sqrt_trick
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {A B C D : Set (ConfigSpace (Sym2 V))}
    (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hC : IsIncreasing C) (hD : IsIncreasing D)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hCm : MeasurableSet C) (hDm : MeasurableSet D)
    (hBA : mu.real B ≤ mu.real A)
    (hCA : mu.real C ≤ mu.real A)
    (hDA : mu.real D ≤ mu.real A) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤
      mu.real A := by
  have h := four_event_sqrt_trick mu hFKG hA hB hC hD hAm hBm hCm hDm
  have hCD : max (mu.real C) (mu.real D) ≤ mu.real A :=
    max_le hCA hDA
  rw [max_eq_left hBA, max_eq_left hCD] at h
  exact h





theorem PeriodicPlaneEmbedding.dominant_bottomSide_measureReal_ge_fourthRoot
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (S : Set V)
    (hS : S ⊆ E.rectVertices a b c d)
    (hTop : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)))
    (hLeft : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)))
    (hRight : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d))) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)) := by
  let A := E.rectSideConnectionEvent a b c d S
    (E.rectBottomBoundaryVertices a b c d)
  let B := E.rectSideConnectionEvent a b c d S
    (E.rectTopBoundaryVertices a b c d)
  let C := E.rectSideConnectionEvent a b c d S
    (E.rectLeftBoundaryVertices a b c d)
  let D := E.rectSideConnectionEvent a b c d S
    (E.rectRightBoundaryVertices a b c d)
  have hdom :
      1 - Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤
        mu.real A := by
    exact dominant_of_four_event_sqrt_trick mu hFKG
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectTopBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectLeftBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectRightBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectTopBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectLeftBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectRightBoundaryVertices a b c d)) hTop hLeft hRight
  have hmass : mu.real (P.setHitsInfinite S) ≤
      mu.real (A ∪ (B ∪ (C ∪ D))) :=
    measureReal_mono
      (E.setHitsInfinite_subset_rectSideConnection_union a b c d S hS)
  have hsqrt :
      Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤
        Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) := by
    gcongr
  dsimp only [A, B, C, D] at hdom hsqrt ⊢
  linarith


theorem PeriodicPlaneEmbedding.dominant_leftSide_measureReal_ge_fourthRoot
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (S : Set V)
    (hS : S ⊆ E.rectVertices a b c d)
    (hRight : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)))
    (hBottom : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)))
    (hTop : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d))) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)) := by
  let A := E.rectSideConnectionEvent a b c d S
    (E.rectLeftBoundaryVertices a b c d)
  let B := E.rectSideConnectionEvent a b c d S
    (E.rectRightBoundaryVertices a b c d)
  let C := E.rectSideConnectionEvent a b c d S
    (E.rectBottomBoundaryVertices a b c d)
  let D := E.rectSideConnectionEvent a b c d S
    (E.rectTopBoundaryVertices a b c d)
  have hdom :
      1 - Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤
        mu.real A := by
    exact dominant_of_four_event_sqrt_trick mu hFKG
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectLeftBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectRightBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectTopBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectLeftBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectRightBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectTopBoundaryVertices a b c d)) hRight hBottom hTop
  have hmass0 : mu.real (P.setHitsInfinite S) ≤
      mu.real
        (E.rectSideConnectionEvent a b c d S
            (E.rectBottomBoundaryVertices a b c d) ∪
          (E.rectSideConnectionEvent a b c d S
              (E.rectTopBoundaryVertices a b c d) ∪
            (E.rectSideConnectionEvent a b c d S
                (E.rectLeftBoundaryVertices a b c d) ∪
              E.rectSideConnectionEvent a b c d S
                (E.rectRightBoundaryVertices a b c d)))) :=
    measureReal_mono
      (E.setHitsInfinite_subset_rectSideConnection_union a b c d S hS)
  have hmass : mu.real (P.setHitsInfinite S) ≤
      mu.real (A ∪ (B ∪ (C ∪ D))) := by
    dsimp only [A, B, C, D]
    simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using hmass0
  have hsqrt :
      Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤
        Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) := by
    gcongr
  dsimp only [A, B, C, D] at hdom hsqrt ⊢
  linarith



theorem PeriodicPlaneEmbedding.preference_max_bottom_left_ge_fourthRoot
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (S : Set V)
    (hS : S ⊆ E.rectVertices a b c d)
    (hBottomTop : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)))
    (hLeftRight : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d))) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤
      max
        (mu.real (E.rectSideConnectionEvent a b c d S
          (E.rectBottomBoundaryVertices a b c d)))
        (mu.real (E.rectSideConnectionEvent a b c d S
          (E.rectLeftBoundaryVertices a b c d))) := by
  by_cases hLeftBottom :
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d))
  · apply le_trans (E.dominant_bottomSide_measureReal_ge_fourthRoot
      mu hFKG a b c d S hS hBottomTop hLeftBottom
      (hLeftRight.trans hLeftBottom))
    exact le_max_left _ _
  · have hBottomLeft :
        mu.real (E.rectSideConnectionEvent a b c d S
          (E.rectBottomBoundaryVertices a b c d)) ≤
        mu.real (E.rectSideConnectionEvent a b c d S
          (E.rectLeftBoundaryVertices a b c d)) := le_of_not_ge hLeftBottom
    apply le_trans (E.dominant_leftSide_measureReal_ge_fourthRoot
      mu hFKG a b c d S hS hLeftRight hBottomLeft
      (hBottomTop.trans hBottomLeft))
    exact le_max_right _ _


theorem PeriodicPlaneEmbedding.dominant_translatedOrbitBox_bottomSide_ge_fourthRoot
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (z : Site 2) (N : Nat) (a b c d : Real)
    (hbox : (P.shift z '' (P.orbitBox N : Set V)) ⊆
      E.rectVertices a b c d)
    (hTop : mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices a b c d)))
    (hLeft : mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices a b c d)))
    (hRight : mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices a b c d))) :
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.orbitBoxHitsInfinite N))) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices a b c d)) := by
  have h := E.dominant_bottomSide_measureReal_ge_fourthRoot mu hFKG
    a b c d (P.shift z '' (P.orbitBox N : Set V)) hbox hTop hLeft hRight
  rw [P.setHitsInfinite_translate_measureReal_eq mu hTI z,
    P.setHitsInfinite_orbitBox] at h
  exact h




theorem PeriodicPlaneEmbedding.dominant_translatedOrbitBox_bottomSide_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hexists : mu {omega | P.HasInfiniteCluster omega} = 1)
    (z : Nat → Site 2) (a b c d : Nat → Real)
    (hbox : ∀ N, (P.shift (z N) '' (P.orbitBox N : Set V)) ⊆
      E.rectVertices (a N) (b N) (c N) (d N))
    (hTop : ∀ N, mu.real (E.rectSideConnectionEvent
        (a N) (b N) (c N) (d N)
        (P.shift (z N) '' (P.orbitBox N : Set V))
        (E.rectTopBoundaryVertices (a N) (b N) (c N) (d N))) ≤
      mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N)
        (P.shift (z N) '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices (a N) (b N) (c N) (d N))))
    (hLeft : ∀ N, mu.real (E.rectSideConnectionEvent
        (a N) (b N) (c N) (d N)
        (P.shift (z N) '' (P.orbitBox N : Set V))
        (E.rectLeftBoundaryVertices (a N) (b N) (c N) (d N))) ≤
      mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N)
        (P.shift (z N) '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices (a N) (b N) (c N) (d N))))
    (hRight : ∀ N, mu.real (E.rectSideConnectionEvent
        (a N) (b N) (c N) (d N)
        (P.shift (z N) '' (P.orbitBox N : Set V))
        (E.rectRightBoundaryVertices (a N) (b N) (c N) (d N))) ≤
      mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N)
        (P.shift (z N) '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices (a N) (b N) (c N) (d N)))) :
    Tendsto (fun N => mu.real (E.rectSideConnectionEvent
      (a N) (b N) (c N) (d N)
      (P.shift (z N) '' (P.orbitBox N : Set V))
      (E.rectBottomBoundaryVertices (a N) (b N) (c N) (d N))))
      atTop (nhds 1) := by
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hmiss : Tendsto (fun N =>
      1 - mu.real (P.orbitBoxHitsInfinite N)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hhit
  have hlower : Tendsto (fun N => 1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.orbitBoxHitsInfinite N)))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · intro N
    exact E.dominant_translatedOrbitBox_bottomSide_ge_fourthRoot
      mu hFKG hTI (z N) N (a N) (b N) (c N) (d N)
      (hbox N) (hTop N) (hLeft N) (hRight N)
  · intro N
    exact measureReal_le_one





theorem crossing_tendsto_one_of_preferredSide_transfer
    (A H M crossing : Nat → Real)
    (hA : Tendsto A atTop (nhds 1))
    (hH : Tendsto H atTop (nhds 1))
    (hM : Tendsto M atTop (nhds 0))
    (hlower : ∀ N, A N * (H N * A N - M N) - M N ≤ crossing N)
    (hupper : ∀ N, crossing N ≤ 1) :
    Tendsto crossing atTop (nhds 1) := by
  have htransfer : Tendsto
      (fun N => A N * (H N * A N - M N) - M N)
      atTop (nhds 1) := by
    convert hA.mul ((hH.mul hA).sub hM) |>.sub hM using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    htransfer tendsto_const_nhds hlower hupper





theorem crossing_max_tendsto_one_of_preferredSide_branches
    (A Hv Hh Mv Mh Cv Ch : Nat → Real)
    (hA : Tendsto A atTop (nhds 1))
    (hHv : Tendsto Hv atTop (nhds 1))
    (hHh : Tendsto Hh atTop (nhds 1))
    (hMv : Tendsto Mv atTop (nhds 0))
    (hMh : Tendsto Mh atTop (nhds 0))
    (hbranch : ∀ N,
      A N * (Hv N * A N - Mv N) - Mv N ≤ Cv N ∨
      A N * (Hh N * A N - Mh N) - Mh N ≤ Ch N)
    (hCv : ∀ N, Cv N ≤ 1) (hCh : ∀ N, Ch N ≤ 1) :
    Tendsto (fun N => max (Cv N) (Ch N)) atTop (nhds 1) := by
  let Lv := fun N => A N * (Hv N * A N - Mv N) - Mv N
  let Lh := fun N => A N * (Hh N * A N - Mh N) - Mh N
  have hLv : Tendsto Lv atTop (nhds 1) := by
    dsimp only [Lv]
    convert hA.mul ((hHv.mul hA).sub hMv) |>.sub hMv using 1 <;> norm_num
  have hLh : Tendsto Lh atTop (nhds 1) := by
    dsimp only [Lh]
    convert hA.mul ((hHh.mul hA).sub hMh) |>.sub hMh using 1 <;> norm_num
  have hmin : Tendsto (fun N => min (Lv N) (Lh N)) atTop (nhds 1) := by
    simpa using hLv.min hLh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hmin tendsto_const_nhds
  · intro N
    rcases hbranch N with hV | hH
    · exact (min_le_left _ _).trans (hV.trans (le_max_left _ _))
    · exact (min_le_right _ _).trans (hH.trans (le_max_right _ _))
  · intro N
    exact max_le (hCv N) (hCh N)

end StatMech.FK.PeriodicPlanar
