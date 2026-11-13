/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























import Code.BeffaraDC.LongRectangleGeometry
import Code.BeffaraDC.TorusSquareCrossingCover

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.Universality



@[simp] theorem torusReduceSite_add_period_x
    (L : ℕ) [Fact (2 < L)] (z : Site 2) :
    torusReduceSite L (z + ![(L : ℤ), 0]) = torusReduceSite L z := by
  apply Prod.ext <;> simp [torusReduceSite]

@[simp] theorem torusReduceSite_add_period_y
    (L : ℕ) [Fact (2 < L)] (z : Site 2) :
    torusReduceSite L (z + ![0, (L : ℤ)]) = torusReduceSite L z := by
  apply Prod.ext <;> simp [torusReduceSite]



theorem torusPlanarPullback_translate_period_x
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



theorem torusPlanarPullback_translate_period_y
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



theorem torusPlanarPullback_injective (L : ℕ) [Fact (2 < L)] :
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
      simpa using heq
  | vertical =>
      have heq := congrFun h
        s(![(x.val : ℤ), (y.val : ℤ)],
          ![(x.val : ℤ), (y.val : ℤ) + 1])
      rw [torusPlanarPullback_vertical,
        torusPlanarPullback_vertical] at heq
      simpa using heq







def bdcTorusVerticalWinding (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : Prop :=
  ∃ x : Site 2,
    Connected 2 (torusPlanarPullback L omega) x
      (x + ![0, (L : ℤ)])



theorem bdcTorusVerticalWinding_projects_to_closed_torus
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




theorem torusSquareHorizontalCrossing_period_false
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    ¬ torusSquareHorizontalCrossing L L omega := by
  rintro ⟨x, y, hx, hy, hx0, hyL, hconn⟩
  have hlt := ZMod.val_lt y.1
  omega



theorem bdcTorusVerticalWinding_not_representable_by_periodSquare
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    (_h : bdcTorusVerticalWinding L omega) :
    ¬ torusSquareHorizontalCrossing L L omega :=
  torusSquareHorizontalCrossing_period_false L omega




def bdcTorusThinCrossing (L alpha n : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : Prop :=
  ∃ k : BdcLongRectangleIndex alpha,
    VerticalCrossing (torusPlanarPullback L omega)
      (bdcLongRectangleXOffset n k : ℤ)
      ((bdcLongRectangleXOffset n k : ℤ) + 2 * (n : ℤ))
      (bdcLongRectangleYOffset n k : ℤ)
      ((bdcLongRectangleYOffset n k : ℤ) +
        2 * (alpha : ℤ) * (n : ℤ))


noncomputable def bdcTorusThinCrossingEvent
    (L alpha n : ℕ) [Fact (2 < L)] : Finset (TorusAmbientConfig L) := by
  classical
  exact Finset.univ.filter (bdcTorusThinCrossing L alpha n)

@[simp] theorem mem_bdcTorusThinCrossingEvent
    (L alpha n : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    omega ∈ bdcTorusThinCrossingEvent L alpha n ↔
      bdcTorusThinCrossing L alpha n omega := by
  classical
  simp [bdcTorusThinCrossingEvent]




theorem bdcTorusThinCrossing_iff_pullback_mem_union
    (L alpha n : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    bdcTorusThinCrossing L alpha n omega ↔
      torusPlanarPullback L omega ∈ bdcLongRectangleUnion alpha n := by
  simp [bdcTorusThinCrossing, bdcLongRectangleUnion,
    bdcLongRectangleIndices, bdcLongRectangleEvent]



def bdcTorusPlanarLiftEvent (L : ℕ) [Fact (2 < L)]
    (A : Set (TorusAmbientConfig L)) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  torusPlanarPullback L '' A



theorem bdcTorusThinCrossing_planarLift_subset_longRectangleUnion
    (L alpha n : ℕ) [Fact (2 < L)] :
    bdcTorusPlanarLiftEvent L
        {omega | bdcTorusThinCrossing L alpha n omega} ⊆
      bdcLongRectangleUnion alpha n := by
  rintro eta ⟨omega, homega, rfl⟩
  exact (bdcTorusThinCrossing_iff_pullback_mem_union
    L alpha n omega).mp homega





structure BdcTorusWindingToThinCover
    (L alpha n : ℕ) [Fact (2 < L)]
    (W : Set (TorusAmbientConfig L)) : Prop where
  toThin : ∀ omega, omega ∈ W → bdcTorusThinCrossing L alpha n omega



theorem BdcTorusWindingToThinCover.planarLift_subset_longRectangleUnion
    {L alpha n : ℕ} [Fact (2 < L)]
    {W : Set (TorusAmbientConfig L)}
    (h : BdcTorusWindingToThinCover L alpha n W) :
    bdcTorusPlanarLiftEvent L W ⊆ bdcLongRectangleUnion alpha n := by
  rintro eta ⟨omega, homega, rfl⟩
  exact (bdcTorusThinCrossing_iff_pullback_mem_union
    L alpha n omega).mp (h.toThin omega homega)





abbrev BdcTorusVerticalWindingThinCover
    (alpha n : ℕ) [Fact (2 < bdcLongRectanglePeriod alpha n)] :=
  BdcTorusWindingToThinCover (bdcLongRectanglePeriod alpha n) alpha n
    {omega |
      bdcTorusVerticalWinding (bdcLongRectanglePeriod alpha n) omega}





theorem bdcTorusVerticalWinding_planarLift_subset_longRectangleUnion
    {alpha n : ℕ} [Fact (2 < bdcLongRectanglePeriod alpha n)]
    (h : BdcTorusVerticalWindingThinCover alpha n) :
    bdcTorusPlanarLiftEvent (bdcLongRectanglePeriod alpha n)
        {omega |
          bdcTorusVerticalWinding (bdcLongRectanglePeriod alpha n) omega} ⊆
      bdcLongRectangleUnion alpha n :=
  h.planarLift_subset_longRectangleUnion

end StatMech.BeffaraDC
