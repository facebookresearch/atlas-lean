/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.AxisSwap

/-!
# Rectangle sides, merge errors and preferred-side crossing bounds

Side-connection events of a drawn rectangle, merge-error events of two sources, and the FKG
lower bounds that turn a preferred side into a crossing of the rectangle.

## i. Overview

For a periodic graph drawn in the plane by `E` and a rectangle `[a, b] × [c, d]`, the boundary
vertex sets `rectBottomBoundaryVertices` etc. are the vertices in the rectangle with a neighbour
beyond the corresponding side. `rectSideConnectionEvent a b c d S side` is the event that some
vertex of `S` lies in an infinite cluster and is joined to `side` by an open path inside the
rectangle; it is measurable and increasing. `rectanglePairMergeErrorUnion a b c d L R` is the
event that a vertex of `L` and a vertex of `R` both lie in infinite clusters but are not joined
inside the rectangle; when the rectangle contains a buffered orbit ball it is contained in the
corresponding ball merge error, so under uniqueness of the infinite cluster its probability
tends to zero (also after lattice translations, by translation invariance).

The probabilistic core uses the FKG inequality (Harris–FKG for the random-cluster measure).
If `L` reaches the bottom side and `R` reaches the top side and the two are merged inside the
rectangle, the rectangle has a vertical crossing, so
`μ(L → bottom) μ(R → top) - μ(merge error) ≤ μ(vertical crossing)`. If `R` prefers the top side
to the bottom side, this gives the preferred-side transfer bound
`A (H A - M) - M ≤ μ(vertical crossing)` with `A = μ(L → bottom)`, `H = μ(R hits ∞)` and
`M` the merge error. The square-root trick (the fourth-root form for four increasing events)
shows that the dominant side of a source `S` is reached with probability at least
`1 - (1 - μ(S hits ∞))^{1/4}`. The last two lemmas are the real-analysis steps that turn these
bounds into crossing probabilities tending to one.

Headline fidelity: everything in this file is proved. The definitions are used throughout the
Sheffield modules (including `CanonicalSheffieldFKG`). The crossing bounds are conditional on
FKG; the merge-error limits on almost sure uniqueness of the infinite cluster (and translation
invariance for the translated forms); `dominant_translatedOrbitBox_bottomSide_tendsto_one` on
FKG, translation invariance and almost sure existence of an infinite cluster.

## ii. Key results

- `PeriodicPlaneEmbedding.rectSideConnectionEvent`,
  `PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion`
- `PeriodicPlaneEmbedding.verticalCrossing_measureReal_ge_side_mul_sub_mergeError`
- `PeriodicPlaneEmbedding.verticalCrossing_ge_preferredSide_transfer`
- `PeriodicPlaneEmbedding.dominant_bottomSide_measureReal_ge_fourthRoot`
- `PeriodicPlaneEmbedding.preference_max_bottom_left_ge_fourthRoot`
- `crossing_max_tendsto_one_of_preferredSide_branches`

## iii. Table of contents

- A. Sides of a rectangle and side-connection events
- B. Merge errors inside rectangles
- C. Joined crossing events
- D. FKG lower bounds for crossings
- E. The fourth-root bound for the dominant side
- F. Limits of the preferred-side bounds

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Ch. 3 (FKG inequality).
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999) (square-root trick).
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Sides of a rectangle and side-connection events -/

/-- Bottom boundary of the drawn rectangle `[a, b] × [c, d]`: vertices drawn in the rectangle having
a neighbour drawn strictly below height `c`. -/
def PeriodicPlaneEmbedding.rectBottomBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) : Set V :=
  {x | x ∈ E.rectVertices a b c d ∧
    ∃ y, P.graph.Adj x y ∧ E.vertexCoord y 1 < c}

/-- Top boundary of the drawn rectangle `[a, b] × [c, d]`: vertices drawn in the rectangle having a
neighbour drawn strictly above height `d`. -/
def PeriodicPlaneEmbedding.rectTopBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) : Set V :=
  {x | x ∈ E.rectVertices a b c d ∧
    ∃ y, P.graph.Adj x y ∧ d < E.vertexCoord y 1}

/-- Left boundary of the drawn rectangle `[a, b] × [c, d]`: vertices drawn in the rectangle having a
neighbour drawn strictly left of `a`. -/
def PeriodicPlaneEmbedding.rectLeftBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) : Set V :=
  {x | x ∈ E.rectVertices a b c d ∧
    ∃ y, P.graph.Adj x y ∧ E.vertexCoord y 0 < a}

/-- Right boundary of the drawn rectangle `[a, b] × [c, d]`: vertices drawn in the rectangle having
a neighbour drawn strictly right of `b`. -/
def PeriodicPlaneEmbedding.rectRightBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) : Set V :=
  {x | x ∈ E.rectVertices a b c d ∧
    ∃ y, P.graph.Adj x y ∧ b < E.vertexCoord y 0}

/-- The event that some vertex of `S` lies in an infinite open cluster and is joined to a vertex of
`side` by an open path inside the drawn rectangle `[a, b] × [c, d]`. -/
def PeriodicPlaneEmbedding.rectSideConnectionEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (S side : Set V) : Set (ConfigSpace (Sym2 V)) :=
  P.infiniteSetConnectionWithin (E.rectVertices a b c d) S side

/-- Side-connection events are measurable. This is
`PeriodicGraph.infiniteSetConnectionWithin_measurableSet` for the drawn rectangle. -/
lemma PeriodicPlaneEmbedding.rectSideConnectionEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S side : Set V) :
    MeasurableSet (E.rectSideConnectionEvent a b c d S side) :=
  P.infiniteSetConnectionWithin_measurableSet
    (E.rectVertices a b c d) S side

omit [Countable V] in
/-- Side-connection events are increasing in the configuration. This is
`PeriodicGraph.infiniteSetConnectionWithin_isIncreasing` for the drawn rectangle. -/
lemma PeriodicPlaneEmbedding.rectSideConnectionEvent_isIncreasing
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S side : Set V) :
    IsIncreasing (E.rectSideConnectionEvent a b c d S side) :=
  P.infiniteSetConnectionWithin_isIncreasing
    (E.rectVertices a b c d) S side

omit [Countable V] in
/-- If `S` lies in the rectangle and reaches the infinite cluster, its infinite cluster leaves the
rectangle, so `S` is joined inside the rectangle to one of the four sides. -/
lemma PeriodicPlaneEmbedding.setHitsInfinite_subset_rectSideConnection_union
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

/-! ## B. Merge errors inside rectangles -/

/-- Rectangle merge error: some `x ∈ L` and `y ∈ R` both lie in infinite clusters but are not joined
by an open path inside the drawn rectangle `[a, b] × [c, d]`. -/
def PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  ⋃ x ∈ L, ⋃ y ∈ R,
    (({omega | (P.cluster omega x).Infinite} ∩
      {omega | (P.cluster omega y).Infinite}) \
        P.connectedWithinSet (E.rectVertices a b c d) x y)

/-- Rectangle merge errors are measurable. -/
lemma PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    MeasurableSet (E.rectanglePairMergeErrorUnion a b c d L R) := by
  unfold PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
      ((P.measurableSet_cluster_infinite x).inter
        (P.measurableSet_cluster_infinite y)).diff
          (P.connectedWithinSet_measurableSet
            (E.rectVertices a b c d) x y)

omit [Countable V] in
/-- The rectangle merge error grows with the two source sets. -/
lemma PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_mono_sources
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

omit [Countable V] in
/-- The probability of the rectangle merge error grows with the two source sets. -/
lemma PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_mono_sources
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (a b c d : Real) {L R L' R' : Finset V}
    (hL : L ⊆ L') (hR : R ⊆ R') :
    mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
      mu.real (E.rectanglePairMergeErrorUnion a b c d L' R') :=
  measureReal_mono (E.rectanglePairMergeErrorUnion_mono_sources
    a b c d hL hR)

omit [Countable V] in
/-- A connection inside the buffered orbit ball of radius `N` is a connection inside any set `A`
containing that ball. -/
lemma PeriodicGraph.connectedWithinOrbit_subset_connectedWithinSet
    (P : PeriodicGraph V) {A : Set V} {x y : V} {N : Nat}
    (hbox : (P.orbitBox (P.bufferedRadius N) : Set V) ⊆ A) :
    P.connectedWithinOrbit x y N ⊆ P.connectedWithinSet A x y := by
  rintro omega ⟨l, hchain, hlast, hsupport⟩
  exact ⟨l, hchain, hlast, fun v hv => hbox (hsupport v hv)⟩

omit [Countable V] in
/-- If the rectangle contains the buffered orbit ball of radius `N`, the rectangle merge error is
contained in the ball merge error `P.pairMergeErrorUnion L R N`. -/
lemma PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_subset_pairMergeErrorUnion
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (L R : Finset V) (N : Nat)
    (hbox : (P.orbitBox (P.bufferedRadius N) : Set V) ⊆
      E.rectVertices a b c d) :
    E.rectanglePairMergeErrorUnion a b c d L R ⊆
      P.pairMergeErrorUnion L R N := by
  intro omega homega
  obtain ⟨x, hxL, y, hyR, hinf, hnotRect⟩ := by
    simpa only [PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion,
      Set.mem_iUnion, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_ofPred_eq] using homega
  apply Set.mem_iUnion.2
  refine ⟨x, Set.mem_iUnion.2 ⟨hxL, Set.mem_iUnion.2 ⟨y,
    Set.mem_iUnion.2 ⟨hyR, ⟨hinf, ?_⟩⟩⟩⟩⟩
  intro horbit
  exact hnotRect
    (P.connectedWithinOrbit_subset_connectedWithinSet hbox horbit)

omit [Countable V] in
/-- Probability form of `rectanglePairMergeErrorUnion_subset_pairMergeErrorUnion`. -/
lemma PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_le
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

/-- Under almost sure uniqueness of the infinite cluster, rectangles containing growing buffered
balls have rectangle merge errors tending to zero. -/
lemma PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_tendsto_zero
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

omit [Countable V] in
/-- Translating the configuration by `z` maps the rectangle merge error of the translated sources
into the ball merge error of the original sources, when the rectangle contains the translated
buffered ball. -/
lemma PeriodicPlaneEmbedding.configTranslate_preimage_rectanglePairMergeErrorUnion_subset
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
      Set.mem_iUnion, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_ofPred_eq] using homega
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

/-- Under a translation-invariant measure, the rectangle merge error of translated sources is at
most the ball merge error of the original sources. -/
lemma PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_measureReal_le
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

/-- Translated version of `rectanglePairMergeErrorUnion_measureReal_tendsto_zero`, under translation
invariance and uniqueness. -/
lemma PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_measureReal_tendsto_zero
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

/-! ## C. Joined crossing events -/

/-- `L` reaches the bottom side, `R` reaches the top side, and there is no merge error between `L`
and `R` inside the rectangle. -/
def PeriodicPlaneEmbedding.finiteRectangleJoinedVerticalEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (P.infiniteSetConnectionWithin (E.rectVertices a b c d) (L : Set V)
      (E.rectBottomBoundaryVertices a b c d) ∩
    P.infiniteSetConnectionWithin (E.rectVertices a b c d) (R : Set V)
      (E.rectTopBoundaryVertices a b c d)) \
    E.rectanglePairMergeErrorUnion a b c d L R

/-- The joined vertical event is measurable. -/
lemma PeriodicPlaneEmbedding.finiteRectangleJoinedVerticalEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    MeasurableSet (E.finiteRectangleJoinedVerticalEvent a b c d L R) :=
  ((P.infiniteSetConnectionWithin_measurableSet
      (E.rectVertices a b c d) (L : Set V)
      (E.rectBottomBoundaryVertices a b c d)).inter
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rectVertices a b c d) (R : Set V)
      (E.rectTopBoundaryVertices a b c d))).diff
    (E.rectanglePairMergeErrorUnion_measurableSet a b c d L R)

omit [Countable V] in
/-- The joined vertical event implies an open vertical crossing of the rectangle. -/
lemma PeriodicPlaneEmbedding.finiteRectangleJoinedVerticalEvent_subset_verticalCrossing
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

/-- `L` reaches the left side, `R` reaches the right side, and there is no merge error between `L`
and `R` inside the rectangle. -/
def PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (P.infiniteSetConnectionWithin (E.rectVertices a b c d) (L : Set V)
      (E.rectLeftBoundaryVertices a b c d) ∩
    P.infiniteSetConnectionWithin (E.rectVertices a b c d) (R : Set V)
      (E.rectRightBoundaryVertices a b c d)) \
    E.rectanglePairMergeErrorUnion a b c d L R

/-- The joined horizontal event is measurable. -/
lemma PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    MeasurableSet (E.finiteRectangleJoinedHorizontalEvent a b c d L R) :=
  ((P.infiniteSetConnectionWithin_measurableSet
      (E.rectVertices a b c d) (L : Set V)
      (E.rectLeftBoundaryVertices a b c d)).inter
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rectVertices a b c d) (R : Set V)
      (E.rectRightBoundaryVertices a b c d))).diff
    (E.rectanglePairMergeErrorUnion_measurableSet a b c d L R)

omit [Countable V] in
/-- The joined horizontal event implies an open horizontal crossing of the rectangle. -/
lemma PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent_subset_horizontalCrossing
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

/-! ## D. FKG lower bounds for crossings -/

/-- FKG bound: `μ(L → bottom) μ(R → top) - μ(merge error) ≤ μ(vertical crossing)`. -/
lemma PeriodicPlaneEmbedding.verticalCrossing_measureReal_ge_side_mul_sub_mergeError
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
      mu.real ((A ∩ B) \ M) := le_measureReal_sdiff
  have hjoined : mu.real ((A ∩ B) \ M) ≤
      mu.real (E.verticalCrossingEvent a b c d) :=
    measureReal_mono
      (E.finiteRectangleJoinedVerticalEvent_subset_verticalCrossing
        a b c d L R)
  dsimp only [A, B, M] at hinter hdiff hjoined ⊢
  linarith

/-- FKG bound: `μ(L → left) μ(R → right) - μ(merge error) ≤ μ(horizontal crossing)`. -/
lemma PeriodicPlaneEmbedding.horizontalCrossing_measureReal_ge_side_mul_sub_mergeError
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
      mu.real ((A ∩ B) \ M) := le_measureReal_sdiff
  have hjoined : mu.real ((A ∩ B) \ M) ≤
      mu.real (E.horizontalCrossingEvent a b c d) :=
    measureReal_mono
      (E.finiteRectangleJoinedHorizontalEvent_subset_horizontalCrossing
        a b c d L R)
  dsimp only [A, B, M] at hinter hdiff hjoined ⊢
  linarith

omit [Countable V] in
/-- If `R` reaches the infinite cluster, `L` reaches `side`, and the two are not separated, then `R`
reaches `side`. -/
lemma PeriodicPlaneEmbedding.setHitsInfinite_inter_rectSide_diff_mergeError_subset_rectSide
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

/-- FKG bound transferring a side connection from `L` to `R`: `μ(R hits ∞) μ(L → side) - μ(merge
error) ≤ μ(R → side)`. -/
lemma PeriodicPlaneEmbedding.rectSide_measureReal_ge_hits_mul_side_sub_mergeError
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
      mu.real ((H ∩ A) \ M) := le_measureReal_sdiff
  have htransfer : mu.real ((H ∩ A) \ M) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V) side) :=
    measureReal_mono
      (E.setHitsInfinite_inter_rectSide_diff_mergeError_subset_rectSide
        a b c d L R side)
  dsimp only [H, A, M] at hinter hdiff htransfer ⊢
  linarith

/-- Preferred-side transfer: if `R` reaches the top at least as often as the bottom, then `A (H A -
M) - M ≤ μ(vertical crossing)` with `A = μ(L → bottom)`, `H = μ(R hits ∞)` and `M` the merge error.
-/
lemma PeriodicPlaneEmbedding.verticalCrossing_ge_preferredSide_transfer
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

/-- Horizontal version of `verticalCrossing_ge_preferredSide_transfer`, with `A = μ(L → left)` and
`R` preferring the right side. -/
lemma PeriodicPlaneEmbedding.horizontalCrossing_ge_preferredSide_transfer
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

/-! ## E. The fourth-root bound for the dominant side -/

omit [DecidableEq V] [Countable V] in
/-- Square-root trick for four increasing events under an FKG measure, in the case where `A` is the
most likely: `1 - (1 - μ(A ∪ B ∪ C ∪ D))^{1/4} ≤ μ(A)`. See also `four_event_sqrt_trick` (stronger:
bounds the maximum) and `zhg_sqrt_trick_four` (equal probabilities). Reference: G. Grimmett,
*Percolation* (1999). -/
lemma dominant_of_four_event_sqrt_trick
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

/-- If the bottom side is the most likely side reached by `S`, then `μ(S → bottom) ≥ 1 - (1 - μ(S
hits ∞))^{1/4}`. -/
lemma PeriodicPlaneEmbedding.dominant_bottomSide_measureReal_ge_fourthRoot
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

/-- If the left side is the most likely side reached by `S`, then `μ(S → left) ≥ 1 - (1 - μ(S hits
∞))^{1/4}`. -/
lemma PeriodicPlaneEmbedding.dominant_leftSide_measureReal_ge_fourthRoot
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

/-- If `S` prefers bottom to top and left to right, the larger of its bottom and left connection
probabilities is at least `1 - (1 - μ(S hits ∞))^{1/4}`. -/
lemma PeriodicPlaneEmbedding.preference_max_bottom_left_ge_fourthRoot
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

/-- Fourth-root bound for the translated orbit box when the bottom side is dominant; translation
invariance replaces the hit probability of the translated box by that of the box. -/
lemma PeriodicPlaneEmbedding.dominant_translatedOrbitBox_bottomSide_ge_fourthRoot
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

/-- If an infinite cluster exists almost surely and the bottom side is dominant for the translated
orbit boxes of radius `N`, the bottom connection probability tends to one. -/
lemma PeriodicPlaneEmbedding.dominant_translatedOrbitBox_bottomSide_tendsto_one
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

/-! ## F. Limits of the preferred-side bounds -/

/-- If `A, H → 1`, `M → 0` and `A (H A - M) - M ≤ crossing ≤ 1`, then `crossing → 1`. -/
lemma crossing_tendsto_one_of_preferredSide_transfer
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
    convert hA.mul ((hH.mul hA).sub hM) |>.sub hM using 1; norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    htransfer tendsto_const_nhds hlower hupper

/-- Two-branch form of `crossing_tendsto_one_of_preferredSide_transfer`: if at every `N` one of the
two transfer bounds holds, the maximum of the two crossing probabilities tends to one. See also
`crossing_max_tendsto_one_of_approxPreferredSide_branches` (stronger: allows an error `ε → 0`). -/
lemma crossing_max_tendsto_one_of_preferredSide_branches
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
    convert hA.mul ((hHv.mul hA).sub hMv) |>.sub hMv using 1; norm_num
  have hLh : Tendsto Lh atTop (nhds 1) := by
    dsimp only [Lh]
    convert hA.mul ((hHh.mul hA).sub hMh) |>.sub hMh using 1; norm_num
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
