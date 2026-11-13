/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldRectanglePreference









open Set

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.rectVertices_mono
    (E : PeriodicPlaneEmbedding P) {a b c d a' b' c' d' : Real}
    (ha : a' ≤ a) (hb : b ≤ b') (hc : c' ≤ c) (hd : d ≤ d') :
    E.rectVertices a b c d ⊆ E.rectVertices a' b' c' d' := by
  rintro x ⟨hxa, hxb, hxc, hxd⟩
  exact ⟨ha.trans hxa, hxb.trans hb, hc.trans hxc, hxd.trans hd⟩

theorem PeriodicPlaneEmbedding.rectLeftConnectionEvent_mono_otherBounds
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

theorem PeriodicPlaneEmbedding.rectRightConnectionEvent_mono_otherBounds
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

theorem PeriodicPlaneEmbedding.rectBottomConnectionEvent_mono_otherBounds
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

theorem PeriodicPlaneEmbedding.rectTopConnectionEvent_mono_otherBounds
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
