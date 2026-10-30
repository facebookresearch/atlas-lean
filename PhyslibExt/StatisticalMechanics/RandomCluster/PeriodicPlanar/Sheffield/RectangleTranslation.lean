/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectanglePreference
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneInfiniteArm

/-!
# Translating rectangles and side-connection events

A lattice translation of the periodic graph maps the vertices drawn in a rectangle, and each of
its four boundary sets, onto those of the translated rectangle; under a translation-invariant
measure, side-connection probabilities are unchanged.

## i. Overview

For `z ∈ ℤ²`, `P.shift z` moves every drawn vertex by `z` (the embedding is periodic). Hence
`x ∈ rectVertices a b c d` iff `P.shift z x` is in the rectangle translated by `z`, and the same
holds for the bottom, top, left and right boundary vertex sets; the images of these sets under
`P.shift z` are exactly the translated sets. Since the side-connection event of the translated
source in the translated rectangle is the preimage of the original event under the configuration
translation, translation invariance of `μ` gives equal probabilities, for a general target side
and for each of the four boundary sides.

Headline fidelity: all results are unconditional (the probability identities assume translation
invariance of `μ`, which is stated as a hypothesis).

## ii. Key results

- `PeriodicPlaneEmbedding.shift_image_rectVertices`
- `PeriodicPlaneEmbedding.rectSideConnectionEvent_translate_measureReal_eq`
- `PeriodicPlaneEmbedding.rectLeftConnection_translate_measureReal_eq` and its right, bottom and
  top analogues.

## iii. Table of contents

- A. Translating drawn vertex sets
- B. Translating boundary sets
- C. Translation invariance of side-connection probabilities

## iv. References

None beyond those in the imported modules.
-/

@[expose] public section

open MeasureTheory Set

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Translating drawn vertex sets -/

omit [Countable V] in
/-- A vertex lies in a rectangle iff its translate by `z` lies in the rectangle translated by `z`.
-/
lemma PeriodicPlaneEmbedding.shift_mem_rectVertices
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (a b c d : Real) (x : V) :
    P.shift z x ∈ E.rectVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) ↔
      x ∈ E.rectVertices a b c d := by
  simp only [PeriodicPlaneEmbedding.rectVertices, Set.mem_ofPred_eq,
    E.vertexCoord_shift]
  constructor
  · rintro ⟨hxa, hxb, hxc, hxd⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hxa, hxb, hxc, hxd⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

omit [Countable V] in
/-- If `P.shift z x ∈ B ↔ x ∈ A` for all `x`, then the image of `A` under `P.shift z` is `B` (the
shift is a bijection). -/
private lemma shift_image_eq_of_mem_iff
    (P : PeriodicGraph V) (z : Site 2) (A B : Set V)
    (hmem : ∀ x, P.shift z x ∈ B ↔ x ∈ A) :
    P.shift z '' A = B := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hmem y).2 hy
  · intro hx
    refine ⟨P.shift (-z) x, ?_, ?_⟩
    · apply (hmem (P.shift (-z) x)).1
      simpa using hx
    · exact P.shift_shift_neg z x

omit [Countable V] in
/-- The image of the vertices drawn in a rectangle under `P.shift z` is the set of vertices drawn in
the translated rectangle. -/
lemma PeriodicPlaneEmbedding.shift_image_rectVertices
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (a b c d : Real) :
    P.shift z '' E.rectVertices a b c d =
      E.rectVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) := by
  apply shift_image_eq_of_mem_iff P z
  exact E.shift_mem_rectVertices z a b c d

/-! ## B. Translating boundary sets -/

omit [Countable V] in
/-- Translation commutes with the bottom boundary vertex set (membership form). -/
lemma PeriodicPlaneEmbedding.shift_mem_rectBottomBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (a b c d : Real) (x : V) :
    P.shift z x ∈ E.rectBottomBoundaryVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) ↔
      x ∈ E.rectBottomBoundaryVertices a b c d := by
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨(E.shift_mem_rectVertices z a b c d x).1 hx,
      P.shift (-z) y, ?_, ?_⟩
    · simpa using (P.shift_adj (-z) (P.shift z x) y).2 hxy
    · rw [E.vertexCoord_shift]
      change E.vertexCoord y 1 < c + (z 1 : Real) at hy
      simp only [Pi.neg_apply, Int.cast_neg]
      linarith
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨(E.shift_mem_rectVertices z a b c d x).2 hx,
      P.shift z y, (P.shift_adj z x y).2 hxy, ?_⟩
    rw [E.vertexCoord_shift]
    linarith

omit [Countable V] in
/-- Translation commutes with the top boundary vertex set (membership form). -/
lemma PeriodicPlaneEmbedding.shift_mem_rectTopBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (a b c d : Real) (x : V) :
    P.shift z x ∈ E.rectTopBoundaryVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) ↔
      x ∈ E.rectTopBoundaryVertices a b c d := by
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨(E.shift_mem_rectVertices z a b c d x).1 hx,
      P.shift (-z) y, ?_, ?_⟩
    · simpa using (P.shift_adj (-z) (P.shift z x) y).2 hxy
    · rw [E.vertexCoord_shift]
      change d + (z 1 : Real) < E.vertexCoord y 1 at hy
      simp only [Pi.neg_apply, Int.cast_neg]
      linarith
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨(E.shift_mem_rectVertices z a b c d x).2 hx,
      P.shift z y, (P.shift_adj z x y).2 hxy, ?_⟩
    rw [E.vertexCoord_shift]
    linarith

omit [Countable V] in
/-- Translation commutes with the left boundary vertex set (membership form). -/
lemma PeriodicPlaneEmbedding.shift_mem_rectLeftBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (a b c d : Real) (x : V) :
    P.shift z x ∈ E.rectLeftBoundaryVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) ↔
      x ∈ E.rectLeftBoundaryVertices a b c d := by
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨(E.shift_mem_rectVertices z a b c d x).1 hx,
      P.shift (-z) y, ?_, ?_⟩
    · simpa using (P.shift_adj (-z) (P.shift z x) y).2 hxy
    · rw [E.vertexCoord_shift]
      change E.vertexCoord y 0 < a + (z 0 : Real) at hy
      simp only [Pi.neg_apply, Int.cast_neg]
      linarith
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨(E.shift_mem_rectVertices z a b c d x).2 hx,
      P.shift z y, (P.shift_adj z x y).2 hxy, ?_⟩
    rw [E.vertexCoord_shift]
    linarith

omit [Countable V] in
/-- Translation commutes with the right boundary vertex set (membership form). -/
lemma PeriodicPlaneEmbedding.shift_mem_rectRightBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (a b c d : Real) (x : V) :
    P.shift z x ∈ E.rectRightBoundaryVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) ↔
      x ∈ E.rectRightBoundaryVertices a b c d := by
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨(E.shift_mem_rectVertices z a b c d x).1 hx,
      P.shift (-z) y, ?_, ?_⟩
    · simpa using (P.shift_adj (-z) (P.shift z x) y).2 hxy
    · rw [E.vertexCoord_shift]
      change b + (z 0 : Real) < E.vertexCoord y 0 at hy
      simp only [Pi.neg_apply, Int.cast_neg]
      linarith
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨(E.shift_mem_rectVertices z a b c d x).2 hx,
      P.shift z y, (P.shift_adj z x y).2 hxy, ?_⟩
    rw [E.vertexCoord_shift]
    linarith

omit [Countable V] in
/-- The image of the bottom boundary set under `P.shift z` is the bottom boundary set of the
translated rectangle. -/
lemma PeriodicPlaneEmbedding.shift_image_rectBottomBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (a b c d : Real) :
    P.shift z '' E.rectBottomBoundaryVertices a b c d =
      E.rectBottomBoundaryVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) := by
  apply shift_image_eq_of_mem_iff P z
  exact E.shift_mem_rectBottomBoundaryVertices z a b c d

omit [Countable V] in
/-- The image of the top boundary set under `P.shift z` is the top boundary set of the translated
rectangle. -/
lemma PeriodicPlaneEmbedding.shift_image_rectTopBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (a b c d : Real) :
    P.shift z '' E.rectTopBoundaryVertices a b c d =
      E.rectTopBoundaryVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) := by
  apply shift_image_eq_of_mem_iff P z
  exact E.shift_mem_rectTopBoundaryVertices z a b c d

omit [Countable V] in
/-- The image of the left boundary set under `P.shift z` is the left boundary set of the translated
rectangle. -/
lemma PeriodicPlaneEmbedding.shift_image_rectLeftBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (a b c d : Real) :
    P.shift z '' E.rectLeftBoundaryVertices a b c d =
      E.rectLeftBoundaryVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) := by
  apply shift_image_eq_of_mem_iff P z
  exact E.shift_mem_rectLeftBoundaryVertices z a b c d

omit [Countable V] in
/-- The image of the right boundary set under `P.shift z` is the right boundary set of the
translated rectangle. -/
lemma PeriodicPlaneEmbedding.shift_image_rectRightBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (a b c d : Real) :
    P.shift z '' E.rectRightBoundaryVertices a b c d =
      E.rectRightBoundaryVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) := by
  apply shift_image_eq_of_mem_iff P z
  exact E.shift_mem_rectRightBoundaryVertices z a b c d

/-! ## C. Translation invariance of side-connection probabilities -/

/-- Under a translation-invariant measure, translating the rectangle, the source and the target side
by `z` does not change the side-connection probability. -/
lemma PeriodicPlaneEmbedding.rectSideConnectionEvent_translate_measureReal_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) (S side : Set V) :
    mu.real (E.rectSideConnectionEvent
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
        (P.shift z '' S) (P.shift z '' side)) =
      mu.real (E.rectSideConnectionEvent a b c d S side) := by
  unfold PeriodicPlaneEmbedding.rectSideConnectionEvent
  rw [← E.shift_image_rectVertices]
  exact P.infiniteSetConnectionWithin_translate_measureReal_eq
    mu hTI z (E.rectVertices a b c d) S side

/-- Left-side connection probabilities are invariant under lattice translations of the rectangle and
the source. -/
lemma PeriodicPlaneEmbedding.rectLeftConnection_translate_measureReal_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) (S : Set V) :
    mu.real (E.rectSideConnectionEvent
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
        (P.shift z '' S)
        (E.rectLeftBoundaryVertices
          (a + (z 0 : Real)) (b + (z 0 : Real))
          (c + (z 1 : Real)) (d + (z 1 : Real)))) =
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)) := by
  rw [← E.shift_image_rectLeftBoundaryVertices]
  exact E.rectSideConnectionEvent_translate_measureReal_eq mu hTI z
    a b c d S (E.rectLeftBoundaryVertices a b c d)

/-- Right-side connection probabilities are invariant under lattice translations of the rectangle
and the source. -/
lemma PeriodicPlaneEmbedding.rectRightConnection_translate_measureReal_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) (S : Set V) :
    mu.real (E.rectSideConnectionEvent
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
        (P.shift z '' S)
        (E.rectRightBoundaryVertices
          (a + (z 0 : Real)) (b + (z 0 : Real))
          (c + (z 1 : Real)) (d + (z 1 : Real)))) =
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectRightBoundaryVertices a b c d)) := by
  rw [← E.shift_image_rectRightBoundaryVertices]
  exact E.rectSideConnectionEvent_translate_measureReal_eq mu hTI z
    a b c d S (E.rectRightBoundaryVertices a b c d)

/-- Bottom-side connection probabilities are invariant under lattice translations of the rectangle
and the source. -/
lemma PeriodicPlaneEmbedding.rectBottomConnection_translate_measureReal_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) (S : Set V) :
    mu.real (E.rectSideConnectionEvent
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
        (P.shift z '' S)
        (E.rectBottomBoundaryVertices
          (a + (z 0 : Real)) (b + (z 0 : Real))
          (c + (z 1 : Real)) (d + (z 1 : Real)))) =
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)) := by
  rw [← E.shift_image_rectBottomBoundaryVertices]
  exact E.rectSideConnectionEvent_translate_measureReal_eq mu hTI z
    a b c d S (E.rectBottomBoundaryVertices a b c d)

/-- Top-side connection probabilities are invariant under lattice translations of the rectangle and
the source. -/
lemma PeriodicPlaneEmbedding.rectTopConnection_translate_measureReal_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) (S : Set V) :
    mu.real (E.rectSideConnectionEvent
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
        (P.shift z '' S)
        (E.rectTopBoundaryVertices
          (a + (z 0 : Real)) (b + (z 0 : Real))
          (c + (z 1 : Real)) (d + (z 1 : Real)))) =
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectTopBoundaryVertices a b c d)) := by
  rw [← E.shift_image_rectTopBoundaryVertices]
  exact E.rectSideConnectionEvent_translate_measureReal_eq mu hTI z
    a b c d S (E.rectTopBoundaryVertices a b c d)

end StatMech.FK.PeriodicPlanar
