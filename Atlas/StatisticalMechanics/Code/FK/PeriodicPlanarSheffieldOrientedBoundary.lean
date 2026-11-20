/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldAxisNegation










open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicGraph.axisSwap_orbitBox (P : PeriodicGraph V) (n : Nat) :
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

theorem PeriodicPlaneEmbedding.axisSwap_rectVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.rectVertices a b c d = E.rectVertices c d a b := by
  ext x
  change (a ≤ E.vertexCoord x 1 ∧ E.vertexCoord x 1 ≤ b ∧
    c ≤ E.vertexCoord x 0 ∧ E.vertexCoord x 0 ≤ d) ↔
    (c ≤ E.vertexCoord x 0 ∧ E.vertexCoord x 0 ≤ d ∧
      a ≤ E.vertexCoord x 1 ∧ E.vertexCoord x 1 ≤ b)
  tauto

theorem PeriodicPlaneEmbedding.axisSwap_leftBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.rectLeftBoundaryVertices a b c d =
      E.rectBottomBoundaryVertices c d a b := by
  ext x
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩

theorem PeriodicPlaneEmbedding.axisSwap_rightBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.rectRightBoundaryVertices a b c d =
      E.rectTopBoundaryVertices c d a b := by
  ext x
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩

theorem PeriodicPlaneEmbedding.axisSwap_leftBoundaryEvent
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

theorem PeriodicPlaneEmbedding.axisSwap_rightBoundaryEvent
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



theorem PeriodicPlaneEmbedding.exists_bottomBoundaryPlacement_tendsto_one
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
    simpa [PeriodicGraph.axisSwap] using hunique
  obtain ⟨source, radius, hsource, hlimit⟩ :=
    E.axisSwap.exists_leftBoundaryPlacement_tendsto_one
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI) huniqueSwap r
  exact ⟨source, radius, by simpa
      [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
        E.axisSwap_rectVertices] using hsource,
    by simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent,
      E.axisSwap_leftBoundaryEvent] using hlimit⟩



theorem PeriodicPlaneEmbedding.exists_topBoundaryPlacement_tendsto_one
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
    simpa [PeriodicGraph.axisSwap] using hunique
  obtain ⟨source, radius, hsource, hlimit⟩ :=
    E.axisSwap.exists_rightBoundaryPlacement_tendsto_one
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI) huniqueSwap r
  exact ⟨source, radius, by simpa [E.axisSwap_rectVertices] using hsource,
    by simpa [E.axisSwap_rightBoundaryEvent] using hlimit⟩


theorem PeriodicPlaneEmbedding.exists_translatedOrbitBox_bottomBoundaryPlacement_tendsto_one
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
    simpa [PeriodicGraph.axisSwap] using hunique
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


theorem PeriodicPlaneEmbedding.exists_translatedOrbitBox_topBoundaryPlacement_tendsto_one
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
    simpa [PeriodicGraph.axisSwap] using hunique
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




theorem PeriodicPlaneEmbedding.exists_buffered_bottomBoundaryPlacement_tendsto_one
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
    simpa [PeriodicGraph.axisSwap] using hunique
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




theorem PeriodicPlaneEmbedding.exists_buffered_topBoundaryPlacement_tendsto_one
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
    simpa [PeriodicGraph.axisSwap] using hunique
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
