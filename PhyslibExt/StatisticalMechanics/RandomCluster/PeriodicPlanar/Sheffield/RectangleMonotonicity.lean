/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectanglePreference

/-!
# Monotonicity of rectangle side-connection events

Enlarging a rectangle while keeping one side fixed enlarges the event that a source is joined
to that side inside the rectangle.

## i. Overview

`rectVertices a b c d` is the set of vertices drawn in `[a, b] × [c, d]`; it grows when the
rectangle grows. A path inside the smaller rectangle that ends on its left side `x = a` ends on
the left side of every larger rectangle with the same left bound, so the left side-connection
event grows when `b`, `d` grow and `c` shrinks. The same holds for the other three sides.

Headline fidelity: all results are unconditional set inclusions.

## ii. Key results

- `PeriodicPlaneEmbedding.rectVertices_mono`
- `PeriodicPlaneEmbedding.rectLeftConnectionEvent_mono_otherBounds` and its right, bottom and
  top analogues.

## iii. Table of contents

- A. Monotonicity in the rectangle

## iv. References

None beyond those in the imported modules.
-/

@[expose] public section

open Set

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Monotonicity in the rectangle -/

omit [Countable V] in
/-- The vertices drawn in a rectangle form a monotone family: `[a, b] × [c, d] ⊆ [a', b'] × [c',
d']` gives the inclusion of drawn vertex sets. -/
lemma PeriodicPlaneEmbedding.rectVertices_mono
    (E : PeriodicPlaneEmbedding P) {a b c d a' b' c' d' : Real}
    (ha : a' ≤ a) (hb : b ≤ b') (hc : c' ≤ c) (hd : d ≤ d') :
    E.rectVertices a b c d ⊆ E.rectVertices a' b' c' d' := by
  rintro x ⟨hxa, hxb, hxc, hxd⟩
  exact ⟨ha.trans hxa, hxb.trans hb, hc.trans hxc, hxd.trans hd⟩

omit [Countable V] in
/-- Keeping the left bound `a` and enlarging the three other bounds enlarges the event that `S` is
joined to the left side inside the rectangle. -/
lemma PeriodicPlaneEmbedding.rectLeftConnectionEvent_mono_otherBounds
    (E : PeriodicPlaneEmbedding P) (S : Set V)
    {a b c d b' c' d' : Real}
    (hb : b ≤ b') (hc : c' ≤ c) (hd : d ≤ d') :
    E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d) ⊆
      E.rectSideConnectionEvent a b' c' d' S
        (E.rectLeftBoundaryVertices a b' c' d') := by
  have hregion := E.rectVertices_mono (a' := a)
    (le_refl a) hb hc hd
  have hside : E.rectLeftBoundaryVertices a b c d ⊆
      E.rectLeftBoundaryVertices a b' c' d' := by
    rintro x ⟨hx, y, hxy, hy⟩
    exact ⟨hregion hx, y, hxy, hy⟩
  exact fun _ h => P.infiniteSetConnectionWithin_mono_target
    (E.rectVertices a b' c' d') S hside
      (P.infiniteSetConnectionWithin_mono_region hregion S
        (E.rectLeftBoundaryVertices a b c d) h)

omit [Countable V] in
/-- Keeping the right bound `b` and enlarging the three other bounds enlarges the event that `S` is
joined to the right side inside the rectangle. -/
lemma PeriodicPlaneEmbedding.rectRightConnectionEvent_mono_otherBounds
    (E : PeriodicPlaneEmbedding P) (S : Set V)
    {a b c d a' c' d' : Real}
    (ha : a' ≤ a) (hc : c' ≤ c) (hd : d ≤ d') :
    E.rectSideConnectionEvent a b c d S
        (E.rectRightBoundaryVertices a b c d) ⊆
      E.rectSideConnectionEvent a' b c' d' S
        (E.rectRightBoundaryVertices a' b c' d') := by
  have hregion := E.rectVertices_mono (b' := b)
    ha (le_refl b) hc hd
  have hside : E.rectRightBoundaryVertices a b c d ⊆
      E.rectRightBoundaryVertices a' b c' d' := by
    rintro x ⟨hx, y, hxy, hy⟩
    exact ⟨hregion hx, y, hxy, hy⟩
  exact fun _ h => P.infiniteSetConnectionWithin_mono_target
    (E.rectVertices a' b c' d') S hside
      (P.infiniteSetConnectionWithin_mono_region hregion S
        (E.rectRightBoundaryVertices a b c d) h)

omit [Countable V] in
/-- Keeping the bottom bound `c` and enlarging the three other bounds enlarges the event that `S` is
joined to the bottom side inside the rectangle. -/
lemma PeriodicPlaneEmbedding.rectBottomConnectionEvent_mono_otherBounds
    (E : PeriodicPlaneEmbedding P) (S : Set V)
    {a b c d a' b' d' : Real}
    (ha : a' ≤ a) (hb : b ≤ b') (hd : d ≤ d') :
    E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d) ⊆
      E.rectSideConnectionEvent a' b' c d' S
        (E.rectBottomBoundaryVertices a' b' c d') := by
  have hregion := E.rectVertices_mono (c' := c)
    ha hb (le_refl c) hd
  have hside : E.rectBottomBoundaryVertices a b c d ⊆
      E.rectBottomBoundaryVertices a' b' c d' := by
    rintro x ⟨hx, y, hxy, hy⟩
    exact ⟨hregion hx, y, hxy, hy⟩
  exact fun _ h => P.infiniteSetConnectionWithin_mono_target
    (E.rectVertices a' b' c d') S hside
      (P.infiniteSetConnectionWithin_mono_region hregion S
        (E.rectBottomBoundaryVertices a b c d) h)

omit [Countable V] in
/-- Keeping the top bound `d` and enlarging the three other bounds enlarges the event that `S` is
joined to the top side inside the rectangle. -/
lemma PeriodicPlaneEmbedding.rectTopConnectionEvent_mono_otherBounds
    (E : PeriodicPlaneEmbedding P) (S : Set V)
    {a b c d a' b' c' : Real}
    (ha : a' ≤ a) (hb : b ≤ b') (hc : c' ≤ c) :
    E.rectSideConnectionEvent a b c d S
        (E.rectTopBoundaryVertices a b c d) ⊆
      E.rectSideConnectionEvent a' b' c' d S
        (E.rectTopBoundaryVertices a' b' c' d) := by
  have hregion := E.rectVertices_mono (d' := d)
    ha hb hc (le_refl d)
  have hside : E.rectTopBoundaryVertices a b c d ⊆
      E.rectTopBoundaryVertices a' b' c' d := by
    rintro x ⟨hx, y, hxy, hy⟩
    exact ⟨hregion hx, y, hxy, hy⟩
  exact fun _ h => P.infiniteSetConnectionWithin_mono_target
    (E.rectVertices a' b' c' d) S hside
      (P.infiniteSetConnectionWithin_mono_region hregion S
        (E.rectTopBoundaryVertices a b c d) h)

end StatMech.FK.PeriodicPlanar
