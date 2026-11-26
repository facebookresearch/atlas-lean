/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.BoundaryGrid

/-!
# Side-connection limits under tangential translation

A side-connection probability that tends to one keeps tending to one after translating the
source parallel to that side and enlarging the other three sides of the rectangle.

## i. Overview

For a translation-invariant measure `μ` on a periodic planar graph, the event that a source set
`S` is joined inside the rectangle `[a, b] × [c, d]` to one of its sides is moved by a lattice
translation `z` to the same event for `S + z` in the translated rectangle. If `z` is parallel to
the chosen side (for the left side: `z 0 = 0`), the translated side lies on the original side
line, and enlarging the three other bounds only enlarges the event. Hence a limit `→ 1` for the
original sequence of rectangles transfers to the translated, enlarged sequence. There is one
statement per side.

Headline fidelity: the four results are unconditional apart from translation invariance of `μ`
and the stated inequalities between the rectangle bounds.

## ii. Key results

- `PeriodicPlaneEmbedding.rectLeftConnection_tangential_tendsto_one`
- `PeriodicPlaneEmbedding.rectRightConnection_tangential_tendsto_one`
- `PeriodicPlaneEmbedding.rectBottomConnection_tangential_tendsto_one`
- `PeriodicPlaneEmbedding.rectTopConnection_tangential_tendsto_one`

## iii. Table of contents

- A. Vertical sides moved vertically
- B. Horizontal sides moved horizontally

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Vertical sides moved vertically -/

/-- Under a translation-invariant measure, if the source `S n` reaches the left side of `[a n, b n]
× [c n, d n]` with probability tending to one, then so does `S n` translated by a vertical vector `z
n`, inside the rectangle with the same left side and the other three bounds enlarged. -/
lemma PeriodicPlaneEmbedding.rectLeftConnection_tangential_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Nat → Site 2) (hz : ∀ n, z n 0 = 0)
    (a b c d b' c' d' : Nat → Real) (S : Nat → Set V)
    (hb : ∀ n, b n + (z n 0 : Real) ≤ b' n)
    (hc : ∀ n, c' n ≤ c n + (z n 1 : Real))
    (hd : ∀ n, d n + (z n 1 : Real) ≤ d' n)
    (hlimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (S n)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a n) (b' n) (c' n) (d' n)
        (P.shift (z n) '' S n)
        (E.rectLeftBoundaryVertices (a n) (b' n) (c' n) (d' n))))
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlimit tendsto_const_nhds
  · intro n
    exact E.rectLeftConnection_tangential_measureReal_le
      mu hTI (z n) (hz n) (a n) (b n) (c n) (d n)
        (b' n) (c' n) (d' n) (S n) (hb n) (hc n) (hd n)
  · intro n
    exact measureReal_le_one

/-- Right-side version of `PeriodicPlaneEmbedding.rectLeftConnection_tangential_tendsto_one`:
vertical translations of the source preserve a right-side connection limit when the left, bottom and
top bounds are enlarged. -/
lemma PeriodicPlaneEmbedding.rectRightConnection_tangential_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Nat → Site 2) (hz : ∀ n, z n 0 = 0)
    (a b c d a' c' d' : Nat → Real) (S : Nat → Set V)
    (ha : ∀ n, a' n ≤ a n + (z n 0 : Real))
    (hc : ∀ n, c' n ≤ c n + (z n 1 : Real))
    (hd : ∀ n, d n + (z n 1 : Real) ≤ d' n)
    (hlimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (S n)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a' n) (b n) (c' n) (d' n)
        (P.shift (z n) '' S n)
        (E.rectRightBoundaryVertices (a' n) (b n) (c' n) (d' n))))
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlimit tendsto_const_nhds
  · intro n
    exact E.rectRightConnection_tangential_measureReal_le
      mu hTI (z n) (hz n) (a n) (b n) (c n) (d n)
        (a' n) (c' n) (d' n) (S n) (ha n) (hc n) (hd n)
  · intro n
    exact measureReal_le_one

/-! ## B. Horizontal sides moved horizontally -/

/-- Bottom-side version of `PeriodicPlaneEmbedding.rectLeftConnection_tangential_tendsto_one`:
horizontal translations of the source preserve a bottom-side connection limit when the left, right
and top bounds are enlarged. -/
lemma PeriodicPlaneEmbedding.rectBottomConnection_tangential_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Nat → Site 2) (hz : ∀ n, z n 1 = 0)
    (a b c d a' b' d' : Nat → Real) (S : Nat → Set V)
    (ha : ∀ n, a' n ≤ a n + (z n 0 : Real))
    (hb : ∀ n, b n + (z n 0 : Real) ≤ b' n)
    (hd : ∀ n, d n + (z n 1 : Real) ≤ d' n)
    (hlimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (S n)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a' n) (b' n) (c n) (d' n)
        (P.shift (z n) '' S n)
        (E.rectBottomBoundaryVertices (a' n) (b' n) (c n) (d' n))))
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlimit tendsto_const_nhds
  · intro n
    exact E.rectBottomConnection_tangential_measureReal_le
      mu hTI (z n) (hz n) (a n) (b n) (c n) (d n)
        (a' n) (b' n) (d' n) (S n) (ha n) (hb n) (hd n)
  · intro n
    exact measureReal_le_one

/-- Top-side version of `PeriodicPlaneEmbedding.rectLeftConnection_tangential_tendsto_one`:
horizontal translations of the source preserve a top-side connection limit when the left, right and
bottom bounds are enlarged. -/
lemma PeriodicPlaneEmbedding.rectTopConnection_tangential_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Nat → Site 2) (hz : ∀ n, z n 1 = 0)
    (a b c d a' b' c' : Nat → Real) (S : Nat → Set V)
    (ha : ∀ n, a' n ≤ a n + (z n 0 : Real))
    (hb : ∀ n, b n + (z n 0 : Real) ≤ b' n)
    (hc : ∀ n, c' n ≤ c n + (z n 1 : Real))
    (hlimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (S n)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a' n) (b' n) (c' n) (d n)
        (P.shift (z n) '' S n)
        (E.rectTopBoundaryVertices (a' n) (b' n) (c' n) (d n))))
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlimit tendsto_const_nhds
  · intro n
    exact E.rectTopConnection_tangential_measureReal_le
      mu hTI (z n) (hz n) (a n) (b n) (c n) (d n)
        (a' n) (b' n) (c' n) (S n) (ha n) (hb n) (hc n)
  · intro n
    exact measureReal_le_one

end StatMech.FK.PeriodicPlanar
