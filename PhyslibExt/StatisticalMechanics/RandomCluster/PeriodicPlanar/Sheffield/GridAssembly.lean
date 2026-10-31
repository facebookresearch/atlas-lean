/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.PreferenceClosure
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectangleLimit

/-!
# Rectangle crossings from a grid of side preferences

Side preferences of translated box clusters on a grid of sites inside a rectangle force one
crossing direction of the rectangle to have probability tending to one.

## i. Overview

For a box `P.orbitBox N` translated to a site `z`, `E.BottomPreferred mu N a b c d z` says that,
inside the rectangle `[a, b] × [c, d]`, the translated box is at least as likely to be connected
to the bottom side as to the top side; `TopPreferred`, `LeftPreferred` and `RightPreferred` are
the other three comparisons.

Label the vertices of a `width × height` grid of sites by two Boolean fields: `vertical` (`true`
on the bottom row, `false` on the top row) and `horizontal` (`true` on the left column, `false`
on the right column), and assume every `true` (resp. `false`) label is backed by the matching
side preference. A discrete topological argument on the grid
(`exists_common_preference_grid_witness`) produces a grid vertex preferring bottom and left with
one king-move neighbor preferring top and one preferring right. Feeding this local
configuration to the uniform connector bound of `RectangleLimit` shows that the larger of the
vertical and horizontal crossing probabilities of the rectangle tends to `1`.

## ii. Key results

- `PeriodicPlaneEmbedding.exists_uniformRadius_gridPreference_crossing_max_tendsto_one` :
  there is a connector radius, uniform over all grids, rectangles and labelings, such that a
  consistently labeled grid of buffered connectors inside the rectangles forces
  `max (vertical crossing) (horizontal crossing) → 1`. Conditional on: `mu` a probability
  measure that is FKG (`hFKG`), translation invariant (`hTI`), with an almost surely unique
  infinite cluster (`hunique`), plus the grid labeling and containment hypotheses in the
  conclusion. Not vacuous. Implied by the `margin = 0` case of
  `exists_uniformRadius_deepGridPreference_crossing_max_tendsto_one` (`Sheffield.CommonArray`).

## iii. Table of contents

- A. Side preferences of a translated box
- B. Crossing bound from a labeled grid

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Side preferences of a translated box -/

/-- In the rectangle `[a, b] × [c, d]`, the box `P.orbitBox N` translated by `z` is at least as
likely to be connected to the bottom side as to the top side. -/
def PeriodicPlaneEmbedding.BottomPreferred
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (N : Nat) (a b c d : Real) (z : Site 2) : Prop :=
  mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectTopBoundaryVertices a b c d)) <=
    mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectBottomBoundaryVertices a b c d))

/-- In the rectangle `[a, b] × [c, d]`, the box `P.orbitBox N` translated by `z` is at least as
likely to be connected to the top side as to the bottom side. -/
def PeriodicPlaneEmbedding.TopPreferred
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (N : Nat) (a b c d : Real) (z : Site 2) : Prop :=
  mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectBottomBoundaryVertices a b c d)) <=
    mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectTopBoundaryVertices a b c d))

/-- In the rectangle `[a, b] × [c, d]`, the box `P.orbitBox N` translated by `z` is at least as
likely to be connected to the left side as to the right side. -/
def PeriodicPlaneEmbedding.LeftPreferred
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (N : Nat) (a b c d : Real) (z : Site 2) : Prop :=
  mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectRightBoundaryVertices a b c d)) <=
    mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectLeftBoundaryVertices a b c d))

/-- In the rectangle `[a, b] × [c, d]`, the box `P.orbitBox N` translated by `z` is at least as
likely to be connected to the right side as to the left side. -/
def PeriodicPlaneEmbedding.RightPreferred
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (N : Nat) (a b c d : Real) (z : Site 2) : Prop :=
  mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectLeftBoundaryVertices a b c d)) <=
    mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectRightBoundaryVertices a b c d))

/-! ## B. Crossing bound from a labeled grid -/

/-- Crossing bound from a labeled preference grid: under FKG, translation invariance and an almost
surely unique infinite cluster, there is a connector radius such that any grid of buffered
connectors inside the rectangles, labeled bottom/top and left/right consistently with the side
preferences and with the boundary rows and columns, forces the larger of the two crossing
probabilities to tend to `1` (Sheffield, *Random Surfaces*, Ch. 9). See also
`exists_uniformRadius_deepGridPreference_crossing_max_tendsto_one`, which implies this. -/
theorem PeriodicPlaneEmbedding.exists_uniformRadius_gridPreference_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    exists radius : Nat -> Nat,
      forall (width height : Nat -> Nat)
        (_hwidth : forall n, 0 < width n)
        (base : Nat -> Site 2)
        (vertical : (n : Nat) ->
          PreferenceGridVertex (width n) (height n) -> Bool)
        (horizontal : (n : Nat) ->
          PreferenceGridVertex (width n) (height n) -> Bool)
        (a b c d : Nat -> Real),
      (forall n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) ->
      (forall n i, vertical n (i, 0) = true) ->
      (forall n i, vertical n (i, Fin.last (height n)) = false) ->
      (forall n j, horizontal n (0, j) = true) ->
      (forall n j, horizontal n (Fin.last (width n), j) = false) ->
      (forall n v, vertical n v = true ->
        E.BottomPreferred mu n (a n) (b n) (c n) (d n)
          (base n + preferenceGridSite v)) ->
      (forall n v, vertical n v = false ->
        E.TopPreferred mu n (a n) (b n) (c n) (d n)
          (base n + preferenceGridSite v)) ->
      (forall n v, horizontal n v = true ->
        E.LeftPreferred mu n (a n) (b n) (c n) (d n)
          (base n + preferenceGridSite v)) ->
      (forall n v, horizontal n v = false ->
        E.RightPreferred mu n (a n) (b n) (c n) (d n)
          (base n + preferenceGridSite v)) ->
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
        (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
        atTop (nhds 1) := by
  classical
  obtain ⟨radius, huniform⟩ :=
    E.exists_uniform_connectorRadius_crossing_max_tendsto_one
      mu hFKG hTI hunique
  refine ⟨radius, ?_⟩
  intro width height hwidth base vertical horizontal a b c d hrect
    hVbottom hVtop hHleft hHright hVtrue hVfalse hHtrue hHfalse
  have hwitness (n : Nat) := exists_common_preference_grid_witness
    (hwidth n) (vertical n) (horizontal n) true false
    (hVbottom n) (hVtop n) (by decide) (hHleft n) (hHright n)
  choose x hx using hwitness
  have hxV (n : Nat) := (hx n).1
  have hxH (n : Nat) := (hx n).2.1
  have hwitnessV (n : Nat) := (hx n).2.2.1
  have hwitnessH (n : Nat) := (hx n).2.2.2
  choose xV hxVadj hxVfalse using hwitnessV
  choose xH hxHadj hxHfalse using hwitnessH
  have hoffV (n : Nat) := exists_preferenceKingOffset_of_kingAdj (hxVadj n)
  have hoffH (n : Nat) := exists_preferenceKingOffset_of_kingAdj (hxHadj n)
  choose ijV hijV using hoffV
  choose ijH hijH using hoffH
  let z : Nat -> Site 2 := fun n => base n + preferenceGridSite (x n)
  have hzV (n : Nat) :
      z n + preferenceKingOffset (ijV n) =
        base n + preferenceGridSite (xV n) := by
    dsimp only [z]
    rw [hijV n]
    simp only [add_assoc]
  have hzH (n : Nat) :
      z n + preferenceKingOffset (ijH n) =
        base n + preferenceGridSite (xH n) := by
    dsimp only [z]
    rw [hijH n]
    simp only [add_assoc]
  apply huniform z ijV ijH a b c d
  · intro n
    exact hrect n (x n)
  · intro n
    exact hVtrue n (x n) (hxV n)
  · intro n
    exact hHtrue n (x n) (hxH n)
  · intro n
    rw [hzV n]
    exact hVfalse n (xV n) (hxVfalse n)
  · intro n
    rw [hzH n]
    exact hHfalse n (xH n) (hxHfalse n)

end StatMech.FK.PeriodicPlanar
