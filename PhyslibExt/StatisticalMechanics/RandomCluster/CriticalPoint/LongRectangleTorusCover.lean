/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleGeometry
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusSquareCrossingCover

/-!
# Torus windings and long-rectangle covers

Relates vertical windings on the discrete torus to crossings of the periodic long rectangles,
through the planar pullback of torus configurations.

## i. Overview

The planar pullback of a torus configuration is periodic and injective. A vertical winding of the
torus cannot be read off a single period square (`torusSquareHorizontalCrossing_period_false`). A
thin-crossing cover `BdcTorusWindingToThinCover` turns windings into crossings of the long
rectangles, so the planar lift of the winding event is contained in the long-rectangle union. That
containment is conditional on the cover hypothesis; `LongRectangleTranslationClosure` refutes the
cover for the translation-closure event at `L = 8`.

## ii. Key results

- `torusPlanarPullback_injective`: the pullback is injective.
- `BdcTorusWindingToThinCover.planarLift_subset_longRectangleUnion`: windings lift into the union,
  given a thin cover.

## iii. Table of contents

- A. Periodicity of the planar pullback
- B. Windings and thin crossings
- C. Thin covers

## iv. References

* V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster model is
  critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012).
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.Universality

/-! ## A. Periodicity of the planar pullback -/

@[simp] lemma torusReduceSite_add_period_x
    (L : ℕ) [Fact (2 < L)] (z : Site 2) :
    torusReduceSite L (z + ![(L : ℤ), 0]) = torusReduceSite L z := by
  apply Prod.ext <;> simp [torusReduceSite]

@[simp] lemma torusReduceSite_add_period_y
    (L : ℕ) [Fact (2 < L)] (z : Site 2) :
    torusReduceSite L (z + ![0, (L : ℤ)]) = torusReduceSite L z := by
  apply Prod.ext <;> simp [torusReduceSite]

lemma torusPlanarPullback_translate_period_x
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    translateConfig ![(L : ℤ), 0] (torusPlanarPullback L omega) =
      torusPlanarPullback L omega := by
  funext e
  unfold translateConfig torusPlanarPullback
  rw [Sym2.map_map]
  congr 1
  apply Sym2.map_congr
  intro z _
  exact torusReduceSite_add_period_x L z

lemma torusPlanarPullback_translate_period_y
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    translateConfig ![0, (L : ℤ)] (torusPlanarPullback L omega) =
      torusPlanarPullback L omega := by
  funext e
  unfold translateConfig torusPlanarPullback
  rw [Sym2.map_map]
  congr 1
  apply Sym2.map_congr
  intro z _
  exact torusReduceSite_add_period_y L z

lemma torusPlanarPullback_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (torusPlanarPullback L) := by
  intro omega eta h
  funext e
  obtain ⟨c, rfl⟩ := torusEdgeOfCode_surjective L e
  rcases c with ⟨⟨x, y⟩, o⟩
  cases o with
  | horizontal =>
      have heq := congrFun h
        s(![(x.val : ℤ), (y.val : ℤ)],
          ![(x.val : ℤ) + 1, (y.val : ℤ)])
      rw [torusPlanarPullback_horizontal,
        torusPlanarPullback_horizontal] at heq
      simpa [torusEdgeOfCode] using heq
  | vertical =>
      have heq := congrFun h
        s(![(x.val : ℤ), (y.val : ℤ)],
          ![(x.val : ℤ), (y.val : ℤ) + 1])
      rw [torusPlanarPullback_vertical,
        torusPlanarPullback_vertical] at heq
      simpa [torusEdgeOfCode] using heq

/-! ## B. Windings and thin crossings -/

/-- The torus configuration has a vertical winding: some site is connected in the planar pullback to
  its translate by one vertical period. -/
def bdcTorusVerticalWinding (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : Prop :=
  ∃ x : Site 2,
    Connected 2 (torusPlanarPullback L omega) x
      (x + ![0, (L : ℤ)])

lemma bdcTorusVerticalWinding_projects_to_closed_torus
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    (h : bdcTorusVerticalWinding L omega) :
    ∃ x y : Site 2,
      Connected 2 (torusPlanarPullback L omega) x y ∧
      torusReduceSite L x = torusReduceSite L y ∧ x ≠ y := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x, x + ![0, (L : ℤ)], hx, ?_, ?_⟩
  · exact (torusReduceSite_add_period_y L x).symm
  · intro heq
    have hcoord := congrFun heq 1
    simp at hcoord
    have hL : (0 : ℤ) < L := by
      exact_mod_cast (show 0 < L by have := (Fact.out : 2 < L); omega)
    omega

lemma torusSquareHorizontalCrossing_period_false
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    ¬ torusSquareHorizontalCrossing L L omega := by
  rintro ⟨x, y, hx, hy, hx0, hyL, hconn⟩
  have hlt := ZMod.val_lt y.1
  omega

lemma bdcTorusVerticalWinding_not_representable_by_periodSquare
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    (_h : bdcTorusVerticalWinding L omega) :
    ¬ torusSquareHorizontalCrossing L L omega :=
  torusSquareHorizontalCrossing_period_false L omega

/-- Some long-rectangle translate is crossed vertically in the planar pullback of the torus
  configuration. -/
def bdcTorusThinCrossing (L alpha n : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : Prop :=
  ∃ k : BdcLongRectangleIndex alpha,
    VerticalCrossing (torusPlanarPullback L omega)
      (bdcLongRectangleXOffset n k : ℤ)
      ((bdcLongRectangleXOffset n k : ℤ) + 2 * (n : ℤ))
      (bdcLongRectangleYOffset n k : ℤ)
      ((bdcLongRectangleYOffset n k : ℤ) +
        2 * (alpha : ℤ) * (n : ℤ))

/-- The thin-crossing event, as a `Finset` of torus configurations. -/
noncomputable def bdcTorusThinCrossingEvent
    (L alpha n : ℕ) [Fact (2 < L)] : Finset (TorusAmbientConfig L) := by
  classical
  exact Finset.univ.filter (bdcTorusThinCrossing L alpha n)

@[simp] lemma mem_bdcTorusThinCrossingEvent
    (L alpha n : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    omega ∈ bdcTorusThinCrossingEvent L alpha n ↔
      bdcTorusThinCrossing L alpha n omega := by
  classical
  simp [bdcTorusThinCrossingEvent]

lemma bdcTorusThinCrossing_iff_pullback_mem_union
    (L alpha n : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    bdcTorusThinCrossing L alpha n omega ↔
      torusPlanarPullback L omega ∈ bdcLongRectangleUnion alpha n := by
  simp [bdcTorusThinCrossing, bdcLongRectangleUnion,
    bdcLongRectangleIndices, bdcLongRectangleEvent]

/-- The planar lift of a set of torus configurations: its image under the planar pullback. -/
def bdcTorusPlanarLiftEvent (L : ℕ) [Fact (2 < L)]
    (A : Set (TorusAmbientConfig L)) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  torusPlanarPullback L '' A

lemma bdcTorusThinCrossing_planarLift_subset_longRectangleUnion
    (L alpha n : ℕ) [Fact (2 < L)] :
    bdcTorusPlanarLiftEvent L
        {omega | bdcTorusThinCrossing L alpha n omega} ⊆
      bdcLongRectangleUnion alpha n := by
  rintro eta ⟨omega, homega, rfl⟩
  exact (bdcTorusThinCrossing_iff_pullback_mem_union
    L alpha n omega).mp homega

/-! ## C. Thin covers -/

/-- A cover hypothesis: every configuration in `W` has a thin crossing. -/
structure BdcTorusWindingToThinCover
    (L alpha n : ℕ) [Fact (2 < L)]
    (W : Set (TorusAmbientConfig L)) : Prop where
  toThin : ∀ omega, omega ∈ W → bdcTorusThinCrossing L alpha n omega

lemma BdcTorusWindingToThinCover.planarLift_subset_longRectangleUnion
    {L alpha n : ℕ} [Fact (2 < L)]
    {W : Set (TorusAmbientConfig L)}
    (h : BdcTorusWindingToThinCover L alpha n W) :
    bdcTorusPlanarLiftEvent L W ⊆ bdcLongRectangleUnion alpha n := by
  rintro eta ⟨omega, homega, rfl⟩
  exact (bdcTorusThinCrossing_iff_pullback_mem_union
    L alpha n omega).mp (h.toThin omega homega)

/-- The thin-cover hypothesis for the vertical-winding event at the long-rectangle period. -/
abbrev BdcTorusVerticalWindingThinCover
    (alpha n : ℕ) [Fact (2 < bdcLongRectanglePeriod alpha n)] :=
  BdcTorusWindingToThinCover (bdcLongRectanglePeriod alpha n) alpha n
    {omega |
      bdcTorusVerticalWinding (bdcLongRectanglePeriod alpha n) omega}

lemma bdcTorusVerticalWinding_planarLift_subset_longRectangleUnion
    {alpha n : ℕ} [Fact (2 < bdcLongRectanglePeriod alpha n)]
    (h : BdcTorusVerticalWindingThinCover alpha n) :
    bdcTorusPlanarLiftEvent (bdcLongRectanglePeriod alpha n)
        {omega |
          bdcTorusVerticalWinding (bdcLongRectanglePeriod alpha n) omega} ⊆
      bdcLongRectangleUnion alpha n :=
  h.planarLift_subset_longRectangleUnion

end StatMech.BeffaraDC
