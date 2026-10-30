/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.NearBoundary

/-!
# Reflection of a periodic planar embedding through the origin

Negating both lattice coordinates turns statements about the left boundary of a rectangle into
statements about the right boundary.

## i. Overview

`PeriodicGraph.axisNeg` keeps the graph and replaces the lattice action `z ↦ shift z` by
`z ↦ shift (-z)`; `PeriodicPlaneEmbedding.axisNeg` composes the embedding coordinates with
`x ↦ -x`, a rotation of the plane by `π`. Translation invariance, orbit boxes and rectangle
vertex sets transform in the expected way, and the left-boundary connection event of a rectangle
becomes the right-boundary event of the reflected rectangle.

Applied to the left-boundary placement theorems of the near-boundary file, this gives
right-boundary versions: under an FKG, translation-invariant measure with an almost surely unique
infinite cluster, a finite source set placed far inside a large rectangle is connected inside
the rectangle to its right boundary with probability tending to one.

## ii. Key results

- `PeriodicPlaneEmbedding.exists_rightBoundaryPlacement_tendsto_one`,
  `PeriodicPlaneEmbedding.exists_translatedOrbitBox_rightBoundaryPlacement_tendsto_one`,
  `PeriodicPlaneEmbedding.exists_buffered_rightBoundaryPlacement_tendsto_one` : conditional on
  `IsFKG mu`, translation invariance of `mu`, and `mu`-almost-sure uniqueness of the infinite
  cluster. These hypotheses hold, for instance, for the point mass on the all-open configuration
  when the graph is connected and infinite, so the results are not vacuous.

## iii. Table of contents

- A. The reflected graph and embedding
- B. Right-boundary placements

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. The reflected graph and embedding -/

/-- The same graph with the reversed lattice action `z ↦ shift (-z)`. -/
def PeriodicGraph.axisNeg (P : PeriodicGraph V) : PeriodicGraph V where
  graph := P.graph
  shift z := P.shift (-z)
  shift_zero := by simpa using P.shift_zero
  shift_add z w v := by simpa [add_comm] using P.shift_add (-z) (-w) v
  shift_adj z x y := P.shift_adj (-z) x y
  fundamentalDomain := P.fundamentalDomain
  fundamentalDomain_nonempty := P.fundamentalDomain_nonempty
  covers v := by
    obtain ⟨z, u, hu, hzu⟩ := P.covers v
    exact ⟨-z, u, hu, by simpa [neg_neg] using hzu⟩
  locallyFinite := P.locallyFinite

/-- The embedding composed with the point reflection `x ↦ -x` of the plane; it is an embedding of
`P.axisNeg`. -/
noncomputable def PeriodicPlaneEmbedding.axisNeg
    (E : PeriodicPlaneEmbedding P) : PeriodicPlaneEmbedding P.axisNeg where
  vertex := E.vertex
  period := E.period.comp (AddEquiv.neg (Site 2)).toAddMonoidHom
  period_injective := E.period_injective.comp (AddEquiv.neg (Site 2)).injective
  coordinates := E.coordinates.trans (ContinuousLinearEquiv.neg Real)
  coordinates_period z i := by
    change -(E.coordinates (E.period (-z))) i = z i
    rw [E.coordinates_period]
    simp
  vertex_shift z x := E.vertex_shift (-z) x
  proper := E.proper
  edgeArc := E.edgeArc
  edgeArc_injective := E.edgeArc_injective
  edgeArc_symm := E.edgeArc_symm
  edgeArc_shift z x y hxy := E.edgeArc_shift (-z) hxy
  edgeArc_intersection := E.edgeArc_intersection
  edgeArc_disjoint := E.edgeArc_disjoint
  edgeArc_locallyFinite := E.edgeArc_locallyFinite

omit [Countable V] in
@[simp] lemma PeriodicPlaneEmbedding.axisNeg_vertexCoord
    (E : PeriodicPlaneEmbedding P) (x : V) (i : Fin 2) :
    E.axisNeg.vertexCoord x i = -E.vertexCoord x i := by
  simp [PeriodicPlaneEmbedding.vertexCoord, PeriodicPlaneEmbedding.axisNeg]

omit [Countable V] in
lemma PeriodicGraph.axisNeg_isTranslationInvariant
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) :
    P.axisNeg.IsTranslationInvariant mu := by
  intro z
  exact hTI (-z)

omit [Countable V] in
lemma PeriodicGraph.axisNeg_orbitBox (P : PeriodicGraph V) (n : Nat) :
    P.axisNeg.orbitBox n = P.orbitBox n := by
  ext v
  rw [P.axisNeg.mem_orbitBox_iff, P.mem_orbitBox_iff]
  constructor
  · rintro ⟨z, hz, u, hu, rfl⟩
    refine ⟨-z, ?_, u, hu, rfl⟩
    rw [Lattice.mem_box] at hz ⊢
    intro i
    simpa using hz i
  · rintro ⟨z, hz, u, hu, rfl⟩
    refine ⟨-z, ?_, u, hu, ?_⟩
    · rw [Lattice.mem_box] at hz ⊢
      intro i
      simpa using hz i
    · simp [PeriodicGraph.axisNeg]

omit [Countable V] in
lemma PeriodicPlaneEmbedding.axisNeg_rectVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisNeg.rectVertices a b c d = E.rectVertices (-b) (-a) (-d) (-c) := by
  ext x
  change (a ≤ -E.vertexCoord x 0 ∧ -E.vertexCoord x 0 ≤ b ∧
    c ≤ -E.vertexCoord x 1 ∧ -E.vertexCoord x 1 ≤ d) ↔
    (-b ≤ E.vertexCoord x 0 ∧ E.vertexCoord x 0 ≤ -a ∧
      -d ≤ E.vertexCoord x 1 ∧ E.vertexCoord x 1 ≤ -c)
  constructor <;> rintro ⟨h0, h1, h2, h3⟩ <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

omit [Countable V] in
lemma PeriodicPlaneEmbedding.axisNeg_leftBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisNeg.rectLeftBoundaryVertices a b c d =
      E.rectRightBoundaryVertices (-b) (-a) (-d) (-c) := by
  ext x
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨by simpa only [E.axisNeg_rectVertices] using hx,
      y, hxy, ?_⟩
    change -E.vertexCoord y 0 < a at hy
    linarith
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨by simpa only [E.axisNeg_rectVertices] using hx,
      y, hxy, ?_⟩
    change -E.vertexCoord y 0 < a
    linarith

omit [Countable V] in
lemma PeriodicPlaneEmbedding.axisNeg_leftBoundaryEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S : Set V) :
    E.axisNeg.rectSideConnectionEvent a b c d S
        (E.axisNeg.rectLeftBoundaryVertices a b c d) =
      E.rectSideConnectionEvent (-b) (-a) (-d) (-c) S
        (E.rectRightBoundaryVertices (-b) (-a) (-d) (-c)) := by
  change P.infiniteSetConnectionWithin
      (E.axisNeg.rectVertices a b c d) S
        (E.axisNeg.rectLeftBoundaryVertices a b c d) = _
  rw [E.axisNeg_rectVertices, E.axisNeg_leftBoundaryVertices]
  rfl

/-! ## B. Right-boundary placements -/

/-- Right-boundary placement: under FKG, translation invariance and almost-sure uniqueness of the
infinite cluster, there are finite sources in rectangles `[-(r + R_N), -r] × [-R_N, R_N]` that
connect inside the rectangle to its right boundary with probability tending to one. -/
theorem PeriodicPlaneEmbedding.exists_rightBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) :
    ∃ source : Nat → Finset V, ∃ radius : Nat → Nat,
      (∀ N, (source N : Set V) ⊆
        E.rectVertices (-(r + radius N)) (-r)
          (-(radius N : Real)) (radius N)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(r + radius N)) (-r)
          (-(radius N : Real)) (radius N) (source N : Set V)
          (E.rectRightBoundaryVertices (-(r + radius N)) (-r)
            (-(radius N : Real)) (radius N)))) atTop (nhds 1) := by
  have huniqueNeg :
      mu {omega | P.axisNeg.HasUniqueInfiniteCluster omega} = 1 := by
    exact hunique
  obtain ⟨source, radius, hsource, hlimit⟩ :=
    E.axisNeg.exists_leftBoundaryPlacement_tendsto_one
      mu hFKG (P.axisNeg_isTranslationInvariant mu hTI) huniqueNeg r
  refine ⟨source, radius, ?_, ?_⟩
  · intro N
    simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
      E.axisNeg_rectVertices] using hsource N
  · simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent,
      E.axisNeg_leftBoundaryEvent] using hlimit

/-- Right-boundary placement with the source a translated orbit box of radius `N`; same hypotheses
as `exists_rightBoundaryPlacement_tendsto_one`. -/
theorem PeriodicPlaneEmbedding.exists_translatedOrbitBox_rightBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      (∀ N, (P.shift (base N) '' (P.orbitBox N : Set V)) ⊆
        E.rectVertices (-(r + radius N)) (-r)
          (-(radius N : Real)) (radius N)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(r + radius N)) (-r)
          (-(radius N : Real)) (radius N)
          (P.shift (base N) '' (P.orbitBox N : Set V))
          (E.rectRightBoundaryVertices (-(r + radius N)) (-r)
            (-(radius N : Real)) (radius N)))) atTop (nhds 1) := by
  have huniqueNeg :
      mu {omega | P.axisNeg.HasUniqueInfiniteCluster omega} = 1 := by
    exact hunique
  obtain ⟨base, radius, hsource, hlimit⟩ :=
    E.axisNeg.exists_translatedOrbitBox_leftBoundaryPlacement_tendsto_one
      mu hFKG (P.axisNeg_isTranslationInvariant mu hTI) huniqueNeg r
  let base' : Nat → Site 2 := fun N => -(base N)
  have hset (N : Nat) :
      P.axisNeg.shift (base N) '' (P.axisNeg.orbitBox N : Set V) =
        P.shift (base' N) '' (P.orbitBox N : Set V) := by
    simp only [P.axisNeg_orbitBox]
    rfl
  refine ⟨base', radius, ?_, ?_⟩
  · intro N
    rw [← hset N]
    simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
      E.axisNeg_rectVertices] using hsource N
  · simpa only [← hset,
      PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent,
      E.axisNeg_leftBoundaryEvent, neg_neg] using hlimit

/-- Right-boundary placement where the larger orbit box of radius `buffer N` also fits in the
rectangle; same hypotheses as `exists_rightBoundaryPlacement_tendsto_one`. -/
theorem PeriodicPlaneEmbedding.exists_buffered_rightBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (buffer : Nat → Nat) (hbuffer : ∀ N, N ≤ buffer N) (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆
        E.rectVertices (-(r + radius N)) (-r)
          (-(radius N : Real)) (radius N)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(r + radius N)) (-r)
          (-(radius N : Real)) (radius N)
          (P.shift (base N) '' (P.orbitBox N : Set V))
          (E.rectRightBoundaryVertices (-(r + radius N)) (-r)
            (-(radius N : Real)) (radius N)))) atTop (nhds 1) := by
  have huniqueNeg :
      mu {omega | P.axisNeg.HasUniqueInfiniteCluster omega} = 1 := by
    exact hunique
  obtain ⟨base, radius, hsource, hlimit⟩ :=
    E.axisNeg.exists_buffered_leftBoundaryPlacement_tendsto_one
      mu hFKG (P.axisNeg_isTranslationInvariant mu hTI) huniqueNeg
        buffer hbuffer r
  let base' : Nat → Site 2 := fun N => -(base N)
  have hset (N k : Nat) :
      P.axisNeg.shift (base N) '' (P.axisNeg.orbitBox k : Set V) =
        P.shift (base' N) '' (P.orbitBox k : Set V) := by
    simp only [P.axisNeg_orbitBox]
    rfl
  refine ⟨base', radius, ?_, ?_⟩
  · intro N
    rw [← hset N (buffer N)]
    simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
      E.axisNeg_rectVertices] using hsource N
  · simpa only [← hset,
      PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent,
      E.axisNeg_leftBoundaryEvent, neg_neg] using hlimit

end StatMech.FK.PeriodicPlanar
