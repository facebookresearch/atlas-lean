/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.AxisNegation

/-!
# Bottom and top boundary placements by axis swap

A source connected to the infinite cluster and to the bottom (or top) side of a large box in the
upper (or lower) half-plane, with probability tending to one.

## i. Overview

Swapping the two coordinate axes of a periodic planar graph and its embedding maps orbit boxes
to orbit boxes, a rectangle `[a, b] × [c, d]` to `[c, d] × [a, b]`, its left side to the bottom
side and its right side to the top side. Applying this to the left-side placement results of
`Sheffield.NearBoundary` and `Sheffield.AxisNegation` turns them into bottom- and top-side
placements: for an edge measure that is FKG, translation invariant and has almost surely a unique
infinite cluster, there are finite sources (or translated orbit boxes, possibly with a buffer) and
box radii such that the probability that the source meets the infinite cluster and is joined to
the bottom (top) side of the box `[-R, R] × [r, r + R]` (`[-R, R] × [-r - R, -r]`) inside the box
tends to one.

Headline fidelity. Every placement result is proved conditionally on `IsFKG mu`,
`P.IsTranslationInvariant mu` and `mu {omega | P.HasUniqueInfiniteCluster omega} = 1`. These
hypotheses concern the primal measure only and are satisfiable (for example by supercritical
Bernoulli percolation on a connected periodic graph), so none of the results is vacuous.

## ii. Key results

- `PeriodicPlaneEmbedding.axisSwap_leftBoundaryEvent`, `axisSwap_rightBoundaryEvent` : the axis
  swap exchanges left/bottom and right/top side-connection events.
- `PeriodicPlaneEmbedding.exists_buffered_bottomBoundaryPlacement_tendsto_one`,
  `exists_buffered_topBoundaryPlacement_tendsto_one` : buffered translated orbit boxes joined to
  the bottom (top) side of a box with probability tending to one.

## iii. Table of contents

- A. Axis swap of boxes, rectangles and side events
- B. Bottom and top boundary placements

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Axis swap of boxes, rectangles and side events -/

omit [Countable V] in
/-- The axis swap of a periodic graph has the same orbit boxes. -/
lemma PeriodicGraph.axisSwap_orbitBox (P : PeriodicGraph V) (n : Nat) :
    P.axisSwap.orbitBox n = P.orbitBox n := by
  ext v
  rw [P.axisSwap.mem_orbitBox_iff, P.mem_orbitBox_iff]
  constructor
  · rintro ⟨z, hz, u, hu, rfl⟩
    refine ⟨siteAxisSwap z, ?_, u, hu, rfl⟩
    rw [Lattice.mem_box] at hz ⊢
    intro i
    simpa [siteAxisSwap] using hz (Fin.rev i)
  · rintro ⟨z, hz, u, hu, rfl⟩
    refine ⟨siteAxisSwap z, ?_, u, hu, ?_⟩
    · rw [Lattice.mem_box] at hz ⊢
      intro i
      simpa [siteAxisSwap] using hz (Fin.rev i)
    · simp [PeriodicGraph.axisSwap, siteAxisSwap_swap]

omit [Countable V] in
/-- After the axis swap, the rectangle `[a, b] × [c, d]` is the original rectangle `[c, d] × [a,
b]`. -/
lemma PeriodicPlaneEmbedding.axisSwap_rectVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.rectVertices a b c d = E.rectVertices c d a b := by
  ext x
  change (a ≤ E.vertexCoord x 1 ∧ E.vertexCoord x 1 ≤ b ∧
    c ≤ E.vertexCoord x 0 ∧ E.vertexCoord x 0 ≤ d) ↔
    (c ≤ E.vertexCoord x 0 ∧ E.vertexCoord x 0 ≤ d ∧
      a ≤ E.vertexCoord x 1 ∧ E.vertexCoord x 1 ≤ b)
  tauto

omit [Countable V] in
/-- The axis swap maps the left side of a rectangle to the bottom side of the swapped rectangle. -/
lemma PeriodicPlaneEmbedding.axisSwap_leftBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.rectLeftBoundaryVertices a b c d =
      E.rectBottomBoundaryVertices c d a b := by
  ext x
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩

omit [Countable V] in
/-- The axis swap maps the right side of a rectangle to the top side of the swapped rectangle. -/
lemma PeriodicPlaneEmbedding.axisSwap_rightBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.rectRightBoundaryVertices a b c d =
      E.rectTopBoundaryVertices c d a b := by
  ext x
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩

omit [Countable V] in
/-- The event that `S` meets the infinite cluster and is joined inside the rectangle to its left
side becomes, after the axis swap, the corresponding bottom-side event. -/
lemma PeriodicPlaneEmbedding.axisSwap_leftBoundaryEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S : Set V) :
    E.axisSwap.rectSideConnectionEvent a b c d S
        (E.axisSwap.rectLeftBoundaryVertices a b c d) =
      E.rectSideConnectionEvent c d a b S
        (E.rectBottomBoundaryVertices c d a b) := by
  change P.infiniteSetConnectionWithin
      (E.axisSwap.rectVertices a b c d) S
        (E.axisSwap.rectLeftBoundaryVertices a b c d) = _
  rw [E.axisSwap_rectVertices, E.axisSwap_leftBoundaryVertices]
  rfl

omit [Countable V] in
/-- The right-side connection event becomes, after the axis swap, the corresponding top-side event.
-/
lemma PeriodicPlaneEmbedding.axisSwap_rightBoundaryEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S : Set V) :
    E.axisSwap.rectSideConnectionEvent a b c d S
        (E.axisSwap.rectRightBoundaryVertices a b c d) =
      E.rectSideConnectionEvent c d a b S
        (E.rectTopBoundaryVertices c d a b) := by
  change P.infiniteSetConnectionWithin
      (E.axisSwap.rectVertices a b c d) S
        (E.axisSwap.rectRightBoundaryVertices a b c d) = _
  rw [E.axisSwap_rectVertices, E.axisSwap_rightBoundaryVertices]
  rfl

/-! ## B. Bottom and top boundary placements -/

/-- For an FKG, translation-invariant measure with a.s. unique infinite cluster, there are finite
sources in the boxes `[-R, R] × [r, r + R]` whose bottom-side connection to the infinite cluster has
probability tending to one. -/
lemma PeriodicPlaneEmbedding.exists_bottomBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) :
    ∃ source : Nat → Finset V, ∃ radius : Nat → Nat,
      (∀ N, (source N : Set V) ⊆
        E.rectVertices (-(radius N : Real)) (radius N)
          r (r + radius N)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(radius N : Real)) (radius N)
          r (r + radius N) (source N : Set V)
          (E.rectBottomBoundaryVertices (-(radius N : Real)) (radius N)
            r (r + radius N)))) atTop (nhds 1) := by
  have huniqueSwap :
      mu {omega | P.axisSwap.HasUniqueInfiniteCluster omega} = 1 := by
    exact hunique
  obtain ⟨source, radius, hsource, hlimit⟩ :=
    E.axisSwap.exists_leftBoundaryPlacement_tendsto_one
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI) huniqueSwap r
  exact ⟨source, radius, by simpa
      [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
        E.axisSwap_rectVertices] using hsource,
    by simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent,
      E.axisSwap_leftBoundaryEvent] using hlimit⟩

/-- Top-side version of `exists_bottomBoundaryPlacement_tendsto_one`, in the boxes `[-R, R] × [-r -
R, -r]`. -/
lemma PeriodicPlaneEmbedding.exists_topBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) :
    ∃ source : Nat → Finset V, ∃ radius : Nat → Nat,
      (∀ N, (source N : Set V) ⊆
        E.rectVertices (-(radius N : Real)) (radius N)
          (-(r + radius N)) (-r)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(radius N : Real)) (radius N)
          (-(r + radius N)) (-r) (source N : Set V)
          (E.rectTopBoundaryVertices (-(radius N : Real)) (radius N)
            (-(r + radius N)) (-r)))) atTop (nhds 1) := by
  have huniqueSwap :
      mu {omega | P.axisSwap.HasUniqueInfiniteCluster omega} = 1 := by
    exact hunique
  obtain ⟨source, radius, hsource, hlimit⟩ :=
    E.axisSwap.exists_rightBoundaryPlacement_tendsto_one
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI) huniqueSwap r
  exact ⟨source, radius, by simpa [E.axisSwap_rectVertices] using hsource,
    by simpa [E.axisSwap_rightBoundaryEvent] using hlimit⟩

/-- Bottom-side placement with translated orbit boxes `P.shift (base N) '' orbitBox N` as sources
(FKG, translation invariance, a.s. uniqueness). -/
lemma PeriodicPlaneEmbedding.exists_translatedOrbitBox_bottomBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      (∀ N, (P.shift (base N) '' (P.orbitBox N : Set V)) ⊆
        E.rectVertices (-(radius N : Real)) (radius N)
          r (r + radius N)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(radius N : Real)) (radius N)
          r (r + radius N)
          (P.shift (base N) '' (P.orbitBox N : Set V))
          (E.rectBottomBoundaryVertices (-(radius N : Real)) (radius N)
            r (r + radius N)))) atTop (nhds 1) := by
  have huniqueSwap :
      mu {omega | P.axisSwap.HasUniqueInfiniteCluster omega} = 1 := by
    exact hunique
  obtain ⟨base, radius, hsource, hlimit⟩ :=
    E.axisSwap.exists_translatedOrbitBox_leftBoundaryPlacement_tendsto_one
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI) huniqueSwap r
  let base' : Nat → Site 2 := fun N => siteAxisSwap (base N)
  have hset (N : Nat) :
      P.axisSwap.shift (base N) '' (P.axisSwap.orbitBox N : Set V) =
        P.shift (base' N) '' (P.orbitBox N : Set V) := by
    simp only [P.axisSwap_orbitBox]
    rfl
  refine ⟨base', radius, ?_, ?_⟩
  · intro N
    rw [← hset N]
    simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
      E.axisSwap_rectVertices] using hsource N
  · simpa only [← hset,
      PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent,
      E.axisSwap_leftBoundaryEvent] using hlimit

/-- Top-side placement with translated orbit boxes as sources (FKG, translation invariance, a.s.
uniqueness). -/
lemma PeriodicPlaneEmbedding.exists_translatedOrbitBox_topBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      (∀ N, (P.shift (base N) '' (P.orbitBox N : Set V)) ⊆
        E.rectVertices (-(radius N : Real)) (radius N)
          (-(r + radius N)) (-r)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(radius N : Real)) (radius N)
          (-(r + radius N)) (-r)
          (P.shift (base N) '' (P.orbitBox N : Set V))
          (E.rectTopBoundaryVertices (-(radius N : Real)) (radius N)
            (-(r + radius N)) (-r)))) atTop (nhds 1) := by
  have huniqueSwap :
      mu {omega | P.axisSwap.HasUniqueInfiniteCluster omega} = 1 := by
    exact hunique
  obtain ⟨base, radius, hsource, hlimit⟩ :=
    E.axisSwap.exists_translatedOrbitBox_rightBoundaryPlacement_tendsto_one
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI) huniqueSwap r
  let base' : Nat → Site 2 := fun N => siteAxisSwap (base N)
  have hset (N : Nat) :
      P.axisSwap.shift (base N) '' (P.axisSwap.orbitBox N : Set V) =
        P.shift (base' N) '' (P.orbitBox N : Set V) := by
    simp only [P.axisSwap_orbitBox]
    rfl
  refine ⟨base', radius, ?_, ?_⟩
  · intro N
    rw [← hset N]
    simpa [E.axisSwap_rectVertices] using hsource N
  · simpa only [← hset, E.axisSwap_rightBoundaryEvent] using hlimit

/-- Bottom-side placement where the enlarged orbit box of radius `buffer N ≥ N` still fits in the
box, while the orbit box of radius `N` is joined to the bottom side with probability tending to one.
-/
lemma PeriodicPlaneEmbedding.exists_buffered_bottomBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (buffer : Nat → Nat) (hbuffer : ∀ N, N ≤ buffer N) (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆
        E.rectVertices (-(radius N : Real)) (radius N)
          r (r + radius N)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(radius N : Real)) (radius N)
          r (r + radius N)
          (P.shift (base N) '' (P.orbitBox N : Set V))
          (E.rectBottomBoundaryVertices (-(radius N : Real)) (radius N)
            r (r + radius N)))) atTop (nhds 1) := by
  have huniqueSwap :
      mu {omega | P.axisSwap.HasUniqueInfiniteCluster omega} = 1 := by
    exact hunique
  obtain ⟨base, radius, hsource, hlimit⟩ :=
    E.axisSwap.exists_buffered_leftBoundaryPlacement_tendsto_one
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI) huniqueSwap
        buffer hbuffer r
  let base' : Nat → Site 2 := fun N => siteAxisSwap (base N)
  have hset (N k : Nat) :
      P.axisSwap.shift (base N) '' (P.axisSwap.orbitBox k : Set V) =
        P.shift (base' N) '' (P.orbitBox k : Set V) := by
    simp only [P.axisSwap_orbitBox]
    rfl
  refine ⟨base', radius, ?_, ?_⟩
  · intro N
    rw [← hset N (buffer N)]
    simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
      E.axisSwap_rectVertices] using hsource N
  · simpa only [← hset,
      PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent,
      E.axisSwap_leftBoundaryEvent] using hlimit

/-- Top-side version of `exists_buffered_bottomBoundaryPlacement_tendsto_one`. -/
lemma PeriodicPlaneEmbedding.exists_buffered_topBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (buffer : Nat → Nat) (hbuffer : ∀ N, N ≤ buffer N) (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆
        E.rectVertices (-(radius N : Real)) (radius N)
          (-(r + radius N)) (-r)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(radius N : Real)) (radius N)
          (-(r + radius N)) (-r)
          (P.shift (base N) '' (P.orbitBox N : Set V))
          (E.rectTopBoundaryVertices (-(radius N : Real)) (radius N)
            (-(r + radius N)) (-r)))) atTop (nhds 1) := by
  have huniqueSwap :
      mu {omega | P.axisSwap.HasUniqueInfiniteCluster omega} = 1 := by
    exact hunique
  obtain ⟨base, radius, hsource, hlimit⟩ :=
    E.axisSwap.exists_buffered_rightBoundaryPlacement_tendsto_one
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI) huniqueSwap
        buffer hbuffer r
  let base' : Nat → Site 2 := fun N => siteAxisSwap (base N)
  have hset (N k : Nat) :
      P.axisSwap.shift (base N) '' (P.axisSwap.orbitBox k : Set V) =
        P.shift (base' N) '' (P.orbitBox k : Set V) := by
    simp only [P.axisSwap_orbitBox]
    rfl
  refine ⟨base', radius, ?_, ?_⟩
  · intro N
    rw [← hset N (buffer N)]
    simpa [E.axisSwap_rectVertices] using hsource N
  · simpa only [← hset, E.axisSwap_rightBoundaryEvent] using hlimit

end StatMech.FK.PeriodicPlanar
