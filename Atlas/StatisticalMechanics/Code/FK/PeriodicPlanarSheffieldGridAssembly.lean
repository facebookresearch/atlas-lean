/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldPreferenceClosure
import Code.FK.PeriodicPlanarSheffieldRectangleLimit









open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

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



theorem PeriodicPlaneEmbedding.exists_uniformRadius_gridPreference_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    exists radius : Nat -> Nat,
      forall (width height : Nat -> Nat)
        (hwidth : forall n, 0 < width n)
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
