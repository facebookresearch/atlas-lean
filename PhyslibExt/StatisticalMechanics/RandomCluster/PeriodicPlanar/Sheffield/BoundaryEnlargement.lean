/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.OrientedBoundary
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectangleMonotonicity

/-!
# Enlargeable boundary placements

Side-connection placements that survive enlarging the box away from the chosen side.

## i. Overview

For each of the four sides of a box, the buffered placements of `Sheffield.NearBoundary`,
`Sheffield.AxisNegation` and `Sheffield.OrientedBoundary` give translated orbit boxes whose
`buffer N`-enlargement fits in a box of radius `radius N` next to a half-plane boundary, and whose
connection to the infinite cluster and to the near side of the box has probability tending to one.
Because the side-connection event only grows when the three other sides of the rectangle move
outwards (`Sheffield.RectangleMonotonicity`), the same base points and radii work uniformly for
every larger rectangle that keeps the chosen side fixed.

Headline fidelity. All four results are proved conditionally on `IsFKG mu`,
`P.IsTranslationInvariant mu` and almost-sure uniqueness of the primal infinite cluster. These
are satisfiable hypotheses on the primal measure alone (for example supercritical Bernoulli
percolation), so the results are not vacuous.

## ii. Key results

- `PeriodicPlaneEmbedding.exists_buffered_leftBoundaryPlacement_enlargeable` and its right,
  bottom and top versions.

## iii. Table of contents

- A. Placements uniform in the far sides of the rectangle

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Placements uniform in the far sides of the rectangle -/

/-- For an FKG, translation-invariant measure with a.s. unique infinite cluster: there are base
points and radii such that, for every rectangle with left side `x = r` and its other sides at least
`radius N` away, the buffered orbit box fits inside and the orbit box of radius `N` is joined to the
infinite cluster and to the left side inside the rectangle with probability tending to one. -/
lemma PeriodicPlaneEmbedding.exists_buffered_leftBoundaryPlacement_enlargeable
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (buffer : Nat → Nat) (hbuffer : ∀ N, N ≤ buffer N) (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      ∀ (b c d : Nat → Real),
        (∀ N, r + radius N ≤ b N) →
        (∀ N, c N ≤ -(radius N : Real)) →
        (∀ N, (radius N : Real) ≤ d N) →
        (∀ N, (P.shift (base N) ''
          (P.orbitBox (buffer N) : Set V)) ⊆
            E.rectVertices r (b N) (c N) (d N)) ∧
        Tendsto (fun N => mu.real
          (E.rectSideConnectionEvent r (b N) (c N) (d N)
            (P.shift (base N) '' (P.orbitBox N : Set V))
            (E.rectLeftBoundaryVertices r (b N) (c N) (d N))))
          atTop (nhds 1) := by
  obtain ⟨base, radius, hsource, hlimit⟩ :=
    E.exists_buffered_leftBoundaryPlacement_tendsto_one
      mu hFKG hTI hunique buffer hbuffer r
  refine ⟨base, radius, ?_⟩
  intro b c d hb hc hd
  constructor
  · intro N
    exact fun _ hv => E.rectVertices_mono
      (le_refl r) (hb N) (hc N) (hd N) (hsource N hv)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlimit tendsto_const_nhds
    · intro N
      exact measureReal_mono
        (E.rectLeftConnectionEvent_mono_otherBounds
          (P.shift (base N) '' (P.orbitBox N : Set V))
          (hb N) (hc N) (hd N))
    · intro N
      exact measureReal_le_one

/-- For an FKG, translation-invariant measure with a.s. unique infinite cluster: there are base
points and radii such that, for every rectangle with right side `x = -r` and its other sides at
least `radius N` away, the buffered orbit box fits inside and the orbit box of radius `N` is joined
to the infinite cluster and to the right side inside the rectangle with probability tending to one.
-/
lemma PeriodicPlaneEmbedding.exists_buffered_rightBoundaryPlacement_enlargeable
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (buffer : Nat → Nat) (hbuffer : ∀ N, N ≤ buffer N) (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      ∀ (a c d : Nat → Real),
        (∀ N, a N ≤ -(r + radius N)) →
        (∀ N, c N ≤ -(radius N : Real)) →
        (∀ N, (radius N : Real) ≤ d N) →
        (∀ N, (P.shift (base N) ''
          (P.orbitBox (buffer N) : Set V)) ⊆
            E.rectVertices (a N) (-r) (c N) (d N)) ∧
        Tendsto (fun N => mu.real
          (E.rectSideConnectionEvent (a N) (-r) (c N) (d N)
            (P.shift (base N) '' (P.orbitBox N : Set V))
            (E.rectRightBoundaryVertices (a N) (-r) (c N) (d N))))
          atTop (nhds 1) := by
  obtain ⟨base, radius, hsource, hlimit⟩ :=
    E.exists_buffered_rightBoundaryPlacement_tendsto_one
      mu hFKG hTI hunique buffer hbuffer r
  refine ⟨base, radius, ?_⟩
  intro a c d ha hc hd
  constructor
  · intro N
    exact fun _ hv => E.rectVertices_mono
      (ha N) (le_refl (-r)) (hc N) (hd N) (hsource N hv)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlimit tendsto_const_nhds
    · intro N
      exact measureReal_mono
        (E.rectRightConnectionEvent_mono_otherBounds
          (P.shift (base N) '' (P.orbitBox N : Set V))
          (ha N) (hc N) (hd N))
    · intro N
      exact measureReal_le_one

/-- For an FKG, translation-invariant measure with a.s. unique infinite cluster: there are base
points and radii such that, for every rectangle with bottom side `y = r` and its other sides at
least `radius N` away, the buffered orbit box fits inside and the orbit box of radius `N` is joined
to the infinite cluster and to the bottom side inside the rectangle with probability tending to one.
-/
lemma PeriodicPlaneEmbedding.exists_buffered_bottomBoundaryPlacement_enlargeable
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (buffer : Nat → Nat) (hbuffer : ∀ N, N ≤ buffer N) (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      ∀ (a b d : Nat → Real),
        (∀ N, a N ≤ -(radius N : Real)) →
        (∀ N, (radius N : Real) ≤ b N) →
        (∀ N, r + radius N ≤ d N) →
        (∀ N, (P.shift (base N) ''
          (P.orbitBox (buffer N) : Set V)) ⊆
            E.rectVertices (a N) (b N) r (d N)) ∧
        Tendsto (fun N => mu.real
          (E.rectSideConnectionEvent (a N) (b N) r (d N)
            (P.shift (base N) '' (P.orbitBox N : Set V))
            (E.rectBottomBoundaryVertices (a N) (b N) r (d N))))
          atTop (nhds 1) := by
  obtain ⟨base, radius, hsource, hlimit⟩ :=
    E.exists_buffered_bottomBoundaryPlacement_tendsto_one
      mu hFKG hTI hunique buffer hbuffer r
  refine ⟨base, radius, ?_⟩
  intro a b d ha hb hd
  constructor
  · intro N
    exact fun _ hv => E.rectVertices_mono
      (ha N) (hb N) (le_refl r) (hd N) (hsource N hv)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlimit tendsto_const_nhds
    · intro N
      exact measureReal_mono
        (E.rectBottomConnectionEvent_mono_otherBounds
          (P.shift (base N) '' (P.orbitBox N : Set V))
          (ha N) (hb N) (hd N))
    · intro N
      exact measureReal_le_one

/-- For an FKG, translation-invariant measure with a.s. unique infinite cluster: there are base
points and radii such that, for every rectangle with top side `y = -r` and its other sides at least
`radius N` away, the buffered orbit box fits inside and the orbit box of radius `N` is joined to the
infinite cluster and to the top side inside the rectangle with probability tending to one. -/
lemma PeriodicPlaneEmbedding.exists_buffered_topBoundaryPlacement_enlargeable
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (buffer : Nat → Nat) (hbuffer : ∀ N, N ≤ buffer N) (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      ∀ (a b c : Nat → Real),
        (∀ N, a N ≤ -(radius N : Real)) →
        (∀ N, (radius N : Real) ≤ b N) →
        (∀ N, c N ≤ -(r + radius N)) →
        (∀ N, (P.shift (base N) ''
          (P.orbitBox (buffer N) : Set V)) ⊆
            E.rectVertices (a N) (b N) (c N) (-r)) ∧
        Tendsto (fun N => mu.real
          (E.rectSideConnectionEvent (a N) (b N) (c N) (-r)
            (P.shift (base N) '' (P.orbitBox N : Set V))
            (E.rectTopBoundaryVertices (a N) (b N) (c N) (-r))))
          atTop (nhds 1) := by
  obtain ⟨base, radius, hsource, hlimit⟩ :=
    E.exists_buffered_topBoundaryPlacement_tendsto_one
      mu hFKG hTI hunique buffer hbuffer r
  refine ⟨base, radius, ?_⟩
  intro a b c ha hb hc
  constructor
  · intro N
    exact fun _ hv => E.rectVertices_mono
      (ha N) (hb N) (hc N) (le_refl (-r)) (hsource N hv)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlimit tendsto_const_nhds
    · intro N
      exact measureReal_mono
        (E.rectTopConnectionEvent_mono_otherBounds
          (P.shift (base N) '' (P.orbitBox N : Set V))
          (ha N) (hb N) (hc N))
    · intro N
      exact measureReal_le_one

end StatMech.FK.PeriodicPlanar
