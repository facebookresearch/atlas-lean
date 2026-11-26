/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.BoundaryGrid
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.GridAssembly

/-!
# Boundary preference grids in a common rectangle

The preference grid spanned by four boundary placements, its alignment with the placements,
and the crossing bound for labeled grids with margins.

## i. Overview

Given four base sites `baseLeft`, `baseRight`, `baseBottom`, `baseTop` (one per side of a common
square) and horizontal and vertical extents, `boundaryGridBase` is the lower-left corner of a
`boundaryGridWidth × boundaryGridHeight` grid of sites whose left column passes through the
left placement, whose bottom row passes through the bottom placement, and whose right column
and top row pass through the right and top placements translated by the extents. The shifts
`boundaryGridLeftShift` and its three siblings move each placement onto its row or column of
the grid; translation invariance then transports side-connection probabilities from a placement
to every vertex of the corresponding boundary row or column, in rectangles enlarged by the
shift.

`exists_deep_common_preference_grid_witness` is the combinatorial core: on a grid whose
Boolean labels `vertical` and `horizontal` are fixed within distance `margin` of the boundary,
there is a vertex at distance more than `margin` from the boundary labeled bottom/left with
king-move neighbors labeled top and right. Combined with the uniform connector bound of
`RectangleLimit`, this gives the crossing bound for labeled grids where buffered connectors are
required only at deep vertices.

## ii. Key results

- `boundaryGridBase`, `boundaryGridWidth`, `boundaryGridHeight` : the grid spanned by four
  boundary placements.
- `PeriodicPlaneEmbedding.preferenceGrid_translatedSet_subset_rect_of_commonSquare` : the
  translated grid lies in `[-M, M + extentX] × [-M, M + extentY]` when the four placements lie
  in `[-M, M]²`.
- `exists_deep_common_preference_grid_witness` : a deep bottom/left vertex with top and right
  king-move neighbors. Unconditional (pure combinatorics, `0 < width`).
- `PeriodicPlaneEmbedding.exists_uniformRadius_deepGridPreference_crossing_max_tendsto_one` :
  the crossing bound for labeled grids with margins. Conditional on `mu` a probability measure
  that is FKG (`hFKG`), translation invariant (`hTI`) and has an almost surely unique infinite
  cluster (`hunique`), plus the labeling, preference and containment hypotheses in the
  conclusion. Not vacuous. With `margin = 0` it implies
  `exists_uniformRadius_gridPreference_crossing_max_tendsto_one` (`Sheffield.GridAssembly`).
- `exists_commonPreferenceExtents_ge` : extents, at least given minima, for which the primal and
  dual grids are both nondegenerate. Unconditional.

## iii. Table of contents

- A. Axis translations and the grid base
- B. Grid size and alignment of the four placements
- C. Transport of side connections to boundary rows and columns
- D. Grid containment in a common rectangle
- E. Crossing bound for labeled grids with margins
- F. Common extents for primal and dual grids

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Axis translations and the grid base -/

/-- The site `(t, 0)` of `ℤ²`: translation by `t` along the horizontal axis. Propositionally equal
to `Pi.single 0 t`. -/
def horizontalShift (t : Int) : Site 2 :=
  fun i => if i = 0 then t else 0

@[simp] lemma horizontalShift_zero_apply (t : Int) :
    horizontalShift t 0 = t := by
  simp [horizontalShift]

@[simp] lemma horizontalShift_one_apply (t : Int) :
    horizontalShift t 1 = 0 := by
  simp [horizontalShift]

/-- The lower-left corner of the boundary preference grid: the horizontal coordinate of the left
placement and the vertical coordinate of the bottom placement. -/
def boundaryGridBase (baseLeft baseBottom : Site 2) : Site 2 :=
  fun i => if i = 0 then baseLeft 0 else baseBottom 1

@[simp] lemma boundaryGridBase_zero_apply
    (baseLeft baseBottom : Site 2) :
    boundaryGridBase baseLeft baseBottom 0 = baseLeft 0 := by
  simp [boundaryGridBase]

@[simp] lemma boundaryGridBase_one_apply
    (baseLeft baseBottom : Site 2) :
    boundaryGridBase baseLeft baseBottom 1 = baseBottom 1 := by
  simp [boundaryGridBase]

/-! ## B. Grid size and alignment of the four placements -/

/-- The vertical translation moving the left placement onto the bottom-left corner of the boundary
grid. -/
def boundaryGridLeftShift (baseLeft baseBottom : Site 2) : Site 2 :=
  verticalShift (baseBottom 1 - baseLeft 1)

/-- The horizontal translation moving the bottom placement onto the bottom-left corner of the
boundary grid. -/
def boundaryGridBottomShift (baseLeft baseBottom : Site 2) : Site 2 :=
  horizontalShift (baseLeft 0 - baseBottom 0)

/-- The translation moving the right placement, shifted right by `extent`, onto the bottom row of
the boundary grid. -/
def boundaryGridRightShift
    (extent : Int) (baseRight baseBottom : Site 2) : Site 2 :=
  horizontalShift extent + verticalShift (baseBottom 1 - baseRight 1)

/-- The translation moving the top placement, shifted up by `extent`, onto the left column of the
boundary grid. -/
def boundaryGridTopShift
    (extent : Int) (baseLeft baseTop : Site 2) : Site 2 :=
  horizontalShift (baseLeft 0 - baseTop 0) + verticalShift extent

@[simp] lemma boundaryGridLeftShift_zero_apply
    (baseLeft baseBottom : Site 2) :
    boundaryGridLeftShift baseLeft baseBottom 0 = 0 := by
  simp [boundaryGridLeftShift]

@[simp] lemma boundaryGridBottomShift_one_apply
    (baseLeft baseBottom : Site 2) :
    boundaryGridBottomShift baseLeft baseBottom 1 = 0 := by
  simp [boundaryGridBottomShift]

@[simp] lemma boundaryGridRightShift_zero_apply
    (extent : Int) (baseRight baseBottom : Site 2) :
    boundaryGridRightShift extent baseRight baseBottom 0 = extent := by
  simp [boundaryGridRightShift]

@[simp] lemma boundaryGridTopShift_one_apply
    (extent : Int) (baseLeft baseTop : Site 2) :
    boundaryGridTopShift extent baseLeft baseTop 1 = extent := by
  simp [boundaryGridTopShift]

/-- The width of the boundary grid: the horizontal distance from the left placement to the right
placement shifted right by `extent`, truncated at `0`. -/
def boundaryGridWidth
    (extent : Nat) (baseLeft baseRight : Site 2) : Nat :=
  (baseRight 0 + (extent : Int) - baseLeft 0).toNat

/-- The height of the boundary grid: the vertical distance from the bottom placement to the top
placement shifted up by `extent`, truncated at `0`. -/
def boundaryGridHeight
    (extent : Nat) (baseBottom baseTop : Site 2) : Nat :=
  (baseTop 1 + (extent : Int) - baseBottom 1).toNat

lemma boundaryGridWidth_pos
    (extent : Nat) (baseLeft baseRight : Site 2)
    (hpos : 0 < baseRight 0 + (extent : Int) - baseLeft 0) :
    0 < boundaryGridWidth extent baseLeft baseRight := by
  simp only [boundaryGridWidth]
  omega

lemma boundaryGridHeight_pos
    (extent : Nat) (baseBottom baseTop : Site 2)
    (hpos : 0 < baseTop 1 + (extent : Int) - baseBottom 1) :
    0 < boundaryGridHeight extent baseBottom baseTop := by
  simp only [boundaryGridHeight]
  omega

lemma boundaryGrid_left_aligned
    (baseLeft baseBottom : Site 2) :
    baseLeft + boundaryGridLeftShift baseLeft baseBottom =
      boundaryGridBase baseLeft baseBottom := by
  funext i
  fin_cases i <;>
    simp [boundaryGridLeftShift, boundaryGridBase, verticalShift]

lemma boundaryGrid_bottom_aligned
    (baseLeft baseBottom : Site 2) :
    baseBottom + boundaryGridBottomShift baseLeft baseBottom =
      boundaryGridBase baseLeft baseBottom := by
  funext i
  fin_cases i <;>
    simp [boundaryGridBottomShift, boundaryGridBase, horizontalShift]

lemma boundaryGrid_right_aligned
    (extent : Nat) (baseLeft baseRight baseBottom : Site 2)
    (hpos : 0 < baseRight 0 + (extent : Int) - baseLeft 0) :
    baseRight + boundaryGridRightShift extent baseRight baseBottom =
      boundaryGridBase baseLeft baseBottom +
        preferenceGridSite
          (Fin.last (boundaryGridWidth extent baseLeft baseRight),
            (0 : Fin (0 + 1))) := by
  have htoNat :
      ((baseRight 0 + (extent : Int) - baseLeft 0).toNat : Int) =
        baseRight 0 + (extent : Int) - baseLeft 0 := by
    exact Int.toNat_of_nonneg (le_of_lt hpos)
  funext i
  fin_cases i
  · simp [boundaryGridRightShift, boundaryGridWidth, boundaryGridBase,
      preferenceGridSite, horizontalShift, verticalShift, htoNat]
  · simp [boundaryGridRightShift, boundaryGridWidth, boundaryGridBase,
      preferenceGridSite, horizontalShift, verticalShift]

lemma boundaryGrid_top_aligned
    (extent : Nat) (baseLeft baseBottom baseTop : Site 2)
    (hpos : 0 < baseTop 1 + (extent : Int) - baseBottom 1) :
    baseTop + boundaryGridTopShift extent baseLeft baseTop =
      boundaryGridBase baseLeft baseBottom +
        preferenceGridSite
          ((0 : Fin (0 + 1)),
            Fin.last (boundaryGridHeight extent baseBottom baseTop)) := by
  have htoNat :
      ((baseTop 1 + (extent : Int) - baseBottom 1).toNat : Int) =
        baseTop 1 + (extent : Int) - baseBottom 1 := by
    exact Int.toNat_of_nonneg (le_of_lt hpos)
  funext i
  fin_cases i
  · simp [boundaryGridTopShift, boundaryGridHeight, boundaryGridBase,
      preferenceGridSite, horizontalShift, verticalShift]
  · simp [boundaryGridTopShift, boundaryGridHeight, boundaryGridBase,
      preferenceGridSite, horizontalShift, verticalShift, htoNat]

lemma boundaryGrid_bottom_row_aligned
    (width height : Nat) (baseLeft baseBottom : Site 2)
    (i : Fin (width + 1)) :
    baseBottom + boundaryGridBottomShift baseLeft baseBottom +
        horizontalShift i.val =
      boundaryGridBase baseLeft baseBottom + preferenceGridSite
        (i, (0 : Fin (height + 1))) := by
  funext k
  fin_cases k <;>
    simp [boundaryGridBottomShift, boundaryGridBase, horizontalShift,
      preferenceGridSite]

lemma boundaryGrid_left_column_aligned
    (width height : Nat) (baseLeft baseBottom : Site 2)
    (j : Fin (height + 1)) :
    baseLeft + boundaryGridLeftShift baseLeft baseBottom +
        verticalShift j.val =
      boundaryGridBase baseLeft baseBottom + preferenceGridSite
        ((0 : Fin (width + 1)), j) := by
  funext k
  fin_cases k <;>
    simp [boundaryGridLeftShift, boundaryGridBase, preferenceGridSite,
      verticalShift]

lemma boundaryGrid_right_column_aligned
    (extent height : Nat) (baseLeft baseRight baseBottom : Site 2)
    (hpos : 0 < baseRight 0 + (extent : Int) - baseLeft 0)
    (j : Fin (height + 1)) :
    baseRight + boundaryGridRightShift extent baseRight baseBottom +
        verticalShift j.val =
      boundaryGridBase baseLeft baseBottom + preferenceGridSite
        (Fin.last (boundaryGridWidth extent baseLeft baseRight), j) := by
  have htoNat :
      ((baseRight 0 + (extent : Int) - baseLeft 0).toNat : Int) =
        baseRight 0 + (extent : Int) - baseLeft 0 :=
    Int.toNat_of_nonneg (le_of_lt hpos)
  funext k
  fin_cases k <;>
    simp [boundaryGridRightShift, boundaryGridWidth, boundaryGridBase,
      preferenceGridSite, horizontalShift, verticalShift, htoNat]

lemma boundaryGrid_top_row_aligned
    (extent width : Nat) (baseLeft baseBottom baseTop : Site 2)
    (hpos : 0 < baseTop 1 + (extent : Int) - baseBottom 1)
    (i : Fin (width + 1)) :
    baseTop + boundaryGridTopShift extent baseLeft baseTop +
        horizontalShift i.val =
      boundaryGridBase baseLeft baseBottom + preferenceGridSite
        (i, Fin.last (boundaryGridHeight extent baseBottom baseTop)) := by
  have htoNat :
      ((baseTop 1 + (extent : Int) - baseBottom 1).toNat : Int) =
        baseTop 1 + (extent : Int) - baseBottom 1 :=
    Int.toNat_of_nonneg (le_of_lt hpos)
  funext k
  fin_cases k <;>
    simp [boundaryGridTopShift, boundaryGridHeight, boundaryGridBase,
      preferenceGridSite, horizontalShift, verticalShift, htoNat]

/-! ## C. Transport of side connections to boundary rows and columns -/

lemma PeriodicPlaneEmbedding.rectBottomConnection_boundaryGrid_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (width height : Nat) (baseLeft baseBottom : Site 2)
    (i : Fin (width + 1)) (a b c d a' b' d' : Real) (S : Set V)
    (ha : a' ≤ a +
      ((boundaryGridBottomShift baseLeft baseBottom +
        horizontalShift i.val) 0 : Int))
    (hb : b + ((boundaryGridBottomShift baseLeft baseBottom +
        horizontalShift i.val) 0 : Int) ≤ b')
    (hd : d + ((boundaryGridBottomShift baseLeft baseBottom +
        horizontalShift i.val) 1 : Int) ≤ d') :
    mu.real (E.rectSideConnectionEvent a b c d
        (P.shift baseBottom '' S)
        (E.rectBottomBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a' b' c d'
        (P.shift (boundaryGridBase baseLeft baseBottom +
          preferenceGridSite (i, (0 : Fin (height + 1)))) '' S)
        (E.rectBottomBoundaryVertices a' b' c d')) := by
  let z := boundaryGridBottomShift baseLeft baseBottom +
    horizontalShift i.val
  have hz : z 1 = 0 := by
    simp [z, boundaryGridBottomShift, horizontalShift]
  have himage :
      P.shift z '' (P.shift baseBottom '' S) =
        P.shift (boundaryGridBase baseLeft baseBottom +
          preferenceGridSite (i, (0 : Fin (height + 1)))) '' S := by
    rw [P.shift_image_shift]
    apply congrArg (fun w : Site 2 => P.shift w '' S)
    simpa only [z, add_assoc] using
      boundaryGrid_bottom_row_aligned width height baseLeft baseBottom i
  have hle := E.rectBottomConnection_tangential_measureReal_le
    mu hTI z hz a b c d a' b' d' (P.shift baseBottom '' S) ha hb hd
  simpa only [himage] using hle

lemma PeriodicPlaneEmbedding.rectLeftConnection_boundaryGrid_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (width height : Nat) (baseLeft baseBottom : Site 2)
    (j : Fin (height + 1)) (a b c d b' c' d' : Real) (S : Set V)
    (hb : b + ((boundaryGridLeftShift baseLeft baseBottom +
        verticalShift j.val) 0 : Int) ≤ b')
    (hc : c' ≤ c + ((boundaryGridLeftShift baseLeft baseBottom +
        verticalShift j.val) 1 : Int))
    (hd : d + ((boundaryGridLeftShift baseLeft baseBottom +
        verticalShift j.val) 1 : Int) ≤ d') :
    mu.real (E.rectSideConnectionEvent a b c d
        (P.shift baseLeft '' S)
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b' c' d'
        (P.shift (boundaryGridBase baseLeft baseBottom +
          preferenceGridSite ((0 : Fin (width + 1)), j)) '' S)
        (E.rectLeftBoundaryVertices a b' c' d')) := by
  let z := boundaryGridLeftShift baseLeft baseBottom + verticalShift j.val
  have hz : z 0 = 0 := by
    simp [z, boundaryGridLeftShift, verticalShift]
  have himage :
      P.shift z '' (P.shift baseLeft '' S) =
        P.shift (boundaryGridBase baseLeft baseBottom +
          preferenceGridSite ((0 : Fin (width + 1)), j)) '' S := by
    rw [P.shift_image_shift]
    apply congrArg (fun w : Site 2 => P.shift w '' S)
    simpa only [z, add_assoc] using
      boundaryGrid_left_column_aligned width height baseLeft baseBottom j
  have hle := E.rectLeftConnection_tangential_measureReal_le
    mu hTI z hz a b c d b' c' d' (P.shift baseLeft '' S) hb hc hd
  simpa only [himage] using hle

lemma PeriodicPlaneEmbedding.rectRightConnection_boundaryGrid_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (extent height : Nat) (baseLeft baseRight baseBottom : Site 2)
    (hpos : 0 < baseRight 0 + (extent : Int) - baseLeft 0)
    (j : Fin (height + 1)) (a b c d a' c' d' : Real) (S : Set V)
    (ha : a' ≤ a + ((boundaryGridRightShift extent baseRight baseBottom +
        verticalShift j.val) 0 : Int))
    (hc : c' ≤ c + ((boundaryGridRightShift extent baseRight baseBottom +
        verticalShift j.val) 1 : Int))
    (hd : d + ((boundaryGridRightShift extent baseRight baseBottom +
        verticalShift j.val) 1 : Int) ≤ d') :
    mu.real (E.rectSideConnectionEvent a b c d
        (P.shift baseRight '' S)
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a'
        (b + ((boundaryGridRightShift extent baseRight baseBottom +
          verticalShift j.val) 0 : Int)) c' d'
        (P.shift (boundaryGridBase baseLeft baseBottom +
          preferenceGridSite
            (Fin.last (boundaryGridWidth extent baseLeft baseRight), j)) '' S)
        (E.rectRightBoundaryVertices a'
          (b + ((boundaryGridRightShift extent baseRight baseBottom +
            verticalShift j.val) 0 : Int)) c' d')) := by
  let z := boundaryGridRightShift extent baseRight baseBottom +
    verticalShift j.val
  have himage :
      P.shift z '' (P.shift baseRight '' S) =
        P.shift (boundaryGridBase baseLeft baseBottom + preferenceGridSite
          (Fin.last (boundaryGridWidth extent baseLeft baseRight), j)) '' S := by
    rw [P.shift_image_shift]
    apply congrArg (fun w : Site 2 => P.shift w '' S)
    simpa only [z, add_assoc] using
      boundaryGrid_right_column_aligned extent height baseLeft baseRight
        baseBottom hpos j
  have htranslate := E.rectRightConnection_translate_measureReal_eq
    mu hTI z a b c d (P.shift baseRight '' S)
  rw [himage] at htranslate
  rw [← htranslate]
  exact measureReal_mono
    (E.rectRightConnectionEvent_mono_otherBounds
      (P.shift (boundaryGridBase baseLeft baseBottom + preferenceGridSite
        (Fin.last (boundaryGridWidth extent baseLeft baseRight), j)) '' S)
      ha hc hd)

lemma PeriodicPlaneEmbedding.rectTopConnection_boundaryGrid_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (extent width : Nat) (baseLeft baseBottom baseTop : Site 2)
    (hpos : 0 < baseTop 1 + (extent : Int) - baseBottom 1)
    (i : Fin (width + 1)) (a b c d a' b' c' : Real) (S : Set V)
    (ha : a' ≤ a + ((boundaryGridTopShift extent baseLeft baseTop +
        horizontalShift i.val) 0 : Int))
    (hb : b + ((boundaryGridTopShift extent baseLeft baseTop +
        horizontalShift i.val) 0 : Int) ≤ b')
    (hc : c' ≤ c + ((boundaryGridTopShift extent baseLeft baseTop +
        horizontalShift i.val) 1 : Int)) :
    mu.real (E.rectSideConnectionEvent a b c d
        (P.shift baseTop '' S)
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a' b' c'
        (d + ((boundaryGridTopShift extent baseLeft baseTop +
          horizontalShift i.val) 1 : Int))
        (P.shift (boundaryGridBase baseLeft baseBottom + preferenceGridSite
          (i, Fin.last (boundaryGridHeight extent baseBottom baseTop))) '' S)
        (E.rectTopBoundaryVertices a' b' c'
          (d + ((boundaryGridTopShift extent baseLeft baseTop +
            horizontalShift i.val) 1 : Int)))) := by
  let z := boundaryGridTopShift extent baseLeft baseTop +
    horizontalShift i.val
  have himage :
      P.shift z '' (P.shift baseTop '' S) =
        P.shift (boundaryGridBase baseLeft baseBottom + preferenceGridSite
          (i, Fin.last (boundaryGridHeight extent baseBottom baseTop))) '' S := by
    rw [P.shift_image_shift]
    apply congrArg (fun w : Site 2 => P.shift w '' S)
    simpa only [z, add_assoc] using
      boundaryGrid_top_row_aligned extent width baseLeft baseBottom baseTop
        hpos i
  have htranslate := E.rectTopConnection_translate_measureReal_eq
    mu hTI z a b c d (P.shift baseTop '' S)
  rw [himage] at htranslate
  rw [← htranslate]
  exact measureReal_mono
    (E.rectTopConnectionEvent_mono_otherBounds
      (P.shift (boundaryGridBase baseLeft baseBottom + preferenceGridSite
        (i, Fin.last (boundaryGridHeight extent baseBottom baseTop))) '' S)
      ha hb hc)

/-! ## D. Grid containment in a common rectangle -/

omit [Countable V] in
lemma PeriodicPlaneEmbedding.preferenceGrid_translatedSet_subset_rect_of_corners
    (E : PeriodicPlaneEmbedding P)
    {width height : Nat} (base : Site 2) (S : Set V)
    (a b c d : Real)
    (hleft : ∀ u ∈ S, a ≤ E.vertexCoord (P.shift base u) 0)
    (hright : ∀ u ∈ S,
      E.vertexCoord (P.shift
        (base + preferenceGridSite
          (Fin.last width, (0 : Fin (0 + 1)))) u) 0 ≤ b)
    (hbottom : ∀ u ∈ S, c ≤ E.vertexCoord (P.shift base u) 1)
    (htop : ∀ u ∈ S,
      E.vertexCoord (P.shift
        (base + preferenceGridSite
          ((0 : Fin (0 + 1)), Fin.last height)) u) 1 ≤ d) :
    ∀ v : PreferenceGridVertex width height,
      P.shift (base + preferenceGridSite v) '' S ⊆
        E.rectVertices a b c d := by
  intro v x hx
  obtain ⟨u, hu, rfl⟩ := hx
  change a ≤ E.vertexCoord
      (P.shift (base + preferenceGridSite v) u) 0 ∧
    E.vertexCoord (P.shift (base + preferenceGridSite v) u) 0 ≤ b ∧
    c ≤ E.vertexCoord (P.shift (base + preferenceGridSite v) u) 1 ∧
    E.vertexCoord (P.shift (base + preferenceGridSite v) u) 1 ≤ d
  have hL := hleft u hu
  have hR := hright u hu
  have hB := hbottom u hu
  have hT := htop u hu
  have hi0 : 0 ≤ (v.1.val : Real) := by positivity
  have hiW : (v.1.val : Real) ≤ width := by
    exact_mod_cast Nat.le_of_lt_succ v.1.isLt
  have hj0 : 0 ≤ (v.2.val : Real) := by positivity
  have hjH : (v.2.val : Real) ≤ height := by
    exact_mod_cast Nat.le_of_lt_succ v.2.isLt
  simp only [P.shift_add, E.vertexCoord_shift] at hL hR hB hT ⊢
  simp only [preferenceGridSite] at hR hT ⊢
  norm_num at hR hT ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

omit [Countable V] in
theorem PeriodicPlaneEmbedding.preferenceGrid_translatedSet_subset_rect_of_commonSquare
    (E : PeriodicPlaneEmbedding P)
    (M extentX extentY : Nat)
    (baseLeft baseRight baseBottom baseTop : Site 2)
    (hposX : 0 < baseRight 0 + (extentX : Int) - baseLeft 0)
    (hposY : 0 < baseTop 1 + (extentY : Int) - baseBottom 1)
    (S : Set V)
    (hleft : P.shift baseLeft '' S ⊆ E.rectVertices
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))
    (hright : P.shift baseRight '' S ⊆ E.rectVertices
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))
    (hbottom : P.shift baseBottom '' S ⊆ E.rectVertices
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))
    (htop : P.shift baseTop '' S ⊆ E.rectVertices
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)) :
    ∀ v : PreferenceGridVertex
        (boundaryGridWidth extentX baseLeft baseRight)
        (boundaryGridHeight extentY baseBottom baseTop),
      P.shift (boundaryGridBase baseLeft baseBottom + preferenceGridSite v) '' S ⊆
        E.rectVertices (-(M : Real)) (M + extentX : Real)
          (-(M : Real)) (M + extentY : Real) := by
  apply E.preferenceGrid_translatedSet_subset_rect_of_corners
  · intro u hu
    have hmem := hleft ⟨u, hu, rfl⟩
    have hcoord := hmem.1
    rw [← boundaryGrid_left_aligned baseLeft baseBottom,
      P.shift_add, E.vertexCoord_shift]
    simpa [boundaryGridLeftShift] using hcoord
  · intro u hu
    have hmem := hright ⟨u, hu, rfl⟩
    have hcoord := hmem.2.1
    rw [← boundaryGrid_right_aligned extentX baseLeft baseRight
      baseBottom hposX, P.shift_add, E.vertexCoord_shift]
    simpa [boundaryGridRightShift] using
      (show E.vertexCoord (P.shift baseRight u) 0 ≤ M from hcoord)
  · intro u hu
    have hmem := hbottom ⟨u, hu, rfl⟩
    have hcoord := hmem.2.2.1
    rw [← boundaryGrid_bottom_aligned baseLeft baseBottom,
      P.shift_add, E.vertexCoord_shift]
    simpa [boundaryGridBottomShift] using hcoord
  · intro u hu
    have hmem := htop ⟨u, hu, rfl⟩
    have hcoord := hmem.2.2.2
    rw [← boundaryGrid_top_aligned extentY baseLeft baseBottom baseTop
      hposY, P.shift_add, E.vertexCoord_shift]
    simpa [boundaryGridTopShift] using
      (show E.vertexCoord (P.shift baseTop u) 1 ≤ M from hcoord)

/-! ## E. Crossing bound for labeled grids with margins -/

/-- Deep preference-grid witness: on a grid of positive width whose labels `vertical` and
`horizontal` are fixed within distance `margin` of the four sides, some vertex at distance more than
`margin` from the boundary is labeled bottom and left and has one king-move neighbor labeled top and
one labeled right. The margin-free form is `exists_common_preference_grid_witness`. -/
theorem exists_deep_common_preference_grid_witness
    {width height margin : Nat} (hwidth : 0 < width)
    (vertical horizontal : PreferenceGridVertex width height → Bool)
    (hverticalBottom : ∀ v, v.2.val ≤ margin → vertical v = true)
    (hverticalTop : ∀ v, height ≤ v.2.val + margin → vertical v = false)
    (hhorizontalLeft : ∀ v, v.1.val ≤ margin → horizontal v = true)
    (hhorizontalRight : ∀ v, width ≤ v.1.val + margin → horizontal v = false) :
    ∃ x xVertical xHorizontal : PreferenceGridVertex width height,
      vertical x = true ∧ horizontal x = true ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧
      vertical xVertical = false ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧
      horizontal xHorizontal = false ∧
      margin ≤ x.1.val ∧ x.1.val + margin < width ∧
      margin ≤ x.2.val ∧ x.2.val + margin < height := by
  have hbottom (i : Fin (width + 1)) : vertical (i, 0) = true :=
    hverticalBottom (i, 0) (Nat.zero_le _)
  have htop (i : Fin (width + 1)) :
      vertical (i, Fin.last height) = false := by
    apply hverticalTop
    simp
  have hleft (j : Fin (height + 1)) : horizontal (0, j) = true :=
    hhorizontalLeft (0, j) (Nat.zero_le _)
  have hright (j : Fin (height + 1)) :
      horizontal (Fin.last width, j) = false := by
    apply hhorizontalRight
    simp
  obtain ⟨x, hxV, hxH, hVertical, hHorizontal⟩ :=
      exists_common_preference_grid_witness hwidth vertical horizontal
        true false hbottom htop (by decide) hleft hright
  obtain ⟨xVertical, hxVadj, hxVfalse⟩ := hVertical
  obtain ⟨xHorizontal, hxHadj, hxHfalse⟩ := hHorizontal
  have hxVerticalDeep : margin < xVertical.2.val := by
    by_contra hnot
    have hle : xVertical.2.val ≤ margin := Nat.le_of_not_gt hnot
    have := hverticalBottom xVertical hle
    simp [hxVfalse] at this
  have hxHorizontalDeep : margin < xHorizontal.1.val := by
    by_contra hnot
    have hle : xHorizontal.1.val ≤ margin := Nat.le_of_not_gt hnot
    have := hhorizontalLeft xHorizontal hle
    simp [hxHfalse] at this
  have hVcoord := hxVadj.2 (1 : Fin 2)
  have hHcoord := hxHadj.2 (0 : Fin 2)
  simp only [preferenceGridSite] at hVcoord hHcoord
  have hVsquare :
      ((x.2.val : Int) - xVertical.2.val) *
          ((x.2.val : Int) - xVertical.2.val) ≤ (1 : Int) * 1 :=
    (Int.natAbs_le_iff_mul_self_le (a :=
      (x.2.val : Int) - xVertical.2.val) (b := 1)).mp
        (by simpa using hVcoord)
  have hHsquare :
      ((x.1.val : Int) - xHorizontal.1.val) *
          ((x.1.val : Int) - xHorizontal.1.val) ≤ (1 : Int) * 1 :=
    (Int.natAbs_le_iff_mul_self_le (a :=
      (x.1.val : Int) - xHorizontal.1.val) (b := 1)).mp
        (by simpa using hHcoord)
  have hxBottom : margin ≤ x.2.val := by
    omega
  have hxLeft : margin ≤ x.1.val := by
    omega
  have hxTop : x.2.val + margin < height := by
    by_contra hnot
    have hge : height ≤ x.2.val + margin := Nat.le_of_not_gt hnot
    have := hverticalTop x hge
    simp [hxV] at this
  have hxRight : x.1.val + margin < width := by
    by_contra hnot
    have hge : width ≤ x.1.val + margin := Nat.le_of_not_gt hnot
    have := hhorizontalRight x hge
    simp [hxH] at this
  exact ⟨x, xVertical, xHorizontal, hxV, hxH, hxVadj, hxVfalse,
    hxHadj, hxHfalse, hxLeft, hxRight, hxBottom, hxTop⟩

/-- Crossing bound for labeled grids with margins: under FKG, translation invariance and an almost
surely unique infinite cluster, there is a connector radius such that any labeled grid whose labels
are backed by side preferences, with buffered connectors inside the rectangle at deep vertices,
forces the larger crossing probability to tend to `1` (Sheffield, *Random Surfaces*, Ch. 9). See
also `exists_uniformRadius_gridPreference_crossing_max_tendsto_one`, the `margin = 0` case with
containment required at every vertex, which this implies. -/
theorem PeriodicPlaneEmbedding.exists_uniformRadius_deepGridPreference_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    ∃ radius : Nat → Nat, ∀
      (width height margin : Nat → Nat)
      (_hwidth : ∀ n, 0 < width n)
      (base : Nat → Site 2)
      (vertical horizontal : (n : Nat) →
        PreferenceGridVertex (width n) (height n) → Bool)
      (a b c d : Nat → Real),
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        margin n ≤ v.1.val → v.1.val + margin n < width n →
        margin n ≤ v.2.val → v.2.val + margin n < height n →
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n v, v.2.val ≤ margin n → vertical n v = true) →
      (∀ n v, height n ≤ v.2.val + margin n → vertical n v = false) →
      (∀ n v, v.1.val ≤ margin n → horizontal n v = true) →
      (∀ n v, width n ≤ v.1.val + margin n → horizontal n v = false) →
      (∀ n v, vertical n v = true →
        E.BottomPreferred mu n (a n) (b n) (c n) (d n)
          (base n + preferenceGridSite v)) →
      (∀ n v, vertical n v = false →
        E.TopPreferred mu n (a n) (b n) (c n) (d n)
          (base n + preferenceGridSite v)) →
      (∀ n v, horizontal n v = true →
        E.LeftPreferred mu n (a n) (b n) (c n) (d n)
          (base n + preferenceGridSite v)) →
      (∀ n v, horizontal n v = false →
        E.RightPreferred mu n (a n) (b n) (c n) (d n)
          (base n + preferenceGridSite v)) →
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
        (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
        atTop (nhds 1) := by
  classical
  obtain ⟨radius, huniform⟩ :=
    E.exists_uniform_connectorRadius_crossing_max_tendsto_one
      mu hFKG hTI hunique
  refine ⟨radius, ?_⟩
  intro width height margin hwidth base vertical horizontal a b c d
    hrect hVbottom hVtop hHleft hHright hVtrue hVfalse hHtrue hHfalse
  have hwitness (n : Nat) := exists_deep_common_preference_grid_witness
    (hwidth n) (vertical n) (horizontal n)
      (hVbottom n) (hVtop n) (hHleft n) (hHright n)
  choose x xVertical xHorizontal hxV hxH hxVadj hxVfalse
    hxHadj hxHfalse hxLeft hxRight hxBottom hxTop using hwitness
  choose ijV hijV using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxVadj n)
  choose ijH hijH using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxHadj n)
  let z : Nat → Site 2 := fun n => base n + preferenceGridSite (x n)
  have hzV (n : Nat) :
      z n + preferenceKingOffset (ijV n) =
        base n + preferenceGridSite (xVertical n) := by
    dsimp only [z]
    rw [hijV n]
    simp only [add_assoc]
  have hzH (n : Nat) :
      z n + preferenceKingOffset (ijH n) =
        base n + preferenceGridSite (xHorizontal n) := by
    dsimp only [z]
    rw [hijH n]
    simp only [add_assoc]
  apply huniform z ijV ijH a b c d
  · intro n
    exact hrect n (x n) (hxLeft n) (hxRight n)
      (hxBottom n) (hxTop n)
  · intro n
    exact hVtrue n (x n) (hxV n)
  · intro n
    exact hHtrue n (x n) (hxH n)
  · intro n
    rw [hzV n]
    exact hVfalse n (xVertical n) (hxVfalse n)
  · intro n
    rw [hzH n]
    exact hHfalse n (xHorizontal n) (hxHfalse n)

/-! ## F. Common extents for primal and dual grids -/

theorem exists_commonPreferenceExtents_ge
    (baseLeft baseRight baseBottom baseTop : Site 2)
    (baseLeftDual baseRightDual baseBottomDual baseTopDual : Site 2)
    (minimumX minimumY : Nat) :
    ∃ extentX extentY : Nat,
      minimumX ≤ extentX ∧ minimumY ≤ extentY ∧
      0 < baseRight 0 + (extentX : Int) - baseLeft 0 ∧
      0 < baseRightDual 0 + (extentX : Int) - baseLeftDual 0 ∧
      0 < baseTop 1 + (extentY : Int) - baseBottom 1 ∧
      0 < baseTopDual 1 + (extentY : Int) - baseBottomDual 1 := by
  let extentX : Nat :=
    (baseLeft 0 - baseRight 0).natAbs +
      (baseLeftDual 0 - baseRightDual 0).natAbs + minimumX + 1
  let extentY : Nat :=
    (baseBottom 1 - baseTop 1).natAbs +
      (baseBottomDual 1 - baseTopDual 1).natAbs + minimumY + 1
  have hminimumX : minimumX ≤ extentX := by
    simp only [extentX]
    omega
  have hminimumY : minimumY ≤ extentY := by
    simp only [extentY]
    omega
  have hx : baseLeft 0 - baseRight 0 < (extentX : Int) := by
    calc
      baseLeft 0 - baseRight 0 ≤
          ((baseLeft 0 - baseRight 0).natAbs : Int) := Int.le_natAbs
      _ < ((baseLeft 0 - baseRight 0).natAbs : Int) +
          ((baseLeftDual 0 - baseRightDual 0).natAbs : Int) +
            (minimumX : Int) + 1 := by
            omega
      _ = (extentX : Int) := by simp [extentX]
  have hxDual : baseLeftDual 0 - baseRightDual 0 < (extentX : Int) := by
    calc
      baseLeftDual 0 - baseRightDual 0 ≤
          ((baseLeftDual 0 - baseRightDual 0).natAbs : Int) := Int.le_natAbs
      _ < ((baseLeft 0 - baseRight 0).natAbs : Int) +
          ((baseLeftDual 0 - baseRightDual 0).natAbs : Int) +
            (minimumX : Int) + 1 := by
            omega
      _ = (extentX : Int) := by simp [extentX]
  have hy : baseBottom 1 - baseTop 1 < (extentY : Int) := by
    calc
      baseBottom 1 - baseTop 1 ≤
          ((baseBottom 1 - baseTop 1).natAbs : Int) := Int.le_natAbs
      _ < ((baseBottom 1 - baseTop 1).natAbs : Int) +
          ((baseBottomDual 1 - baseTopDual 1).natAbs : Int) +
            (minimumY : Int) + 1 := by
            omega
      _ = (extentY : Int) := by simp [extentY]
  have hyDual :
      baseBottomDual 1 - baseTopDual 1 < (extentY : Int) := by
    calc
      baseBottomDual 1 - baseTopDual 1 ≤
          ((baseBottomDual 1 - baseTopDual 1).natAbs : Int) := Int.le_natAbs
      _ < ((baseBottom 1 - baseTop 1).natAbs : Int) +
          ((baseBottomDual 1 - baseTopDual 1).natAbs : Int) +
            (minimumY : Int) + 1 := by
            omega
      _ = (extentY : Int) := by simp [extentY]
  exact ⟨extentX, extentY, hminimumX, hminimumY,
    by omega, by omega, by omega, by omega⟩

/-- Horizontal and vertical extents making the primal and the dual boundary grids nondegenerate. See
also `exists_commonPreferenceExtents_ge`, which also bounds the extents below. -/
lemma exists_commonPositivePreferenceExtents
    (baseLeft baseRight baseBottom baseTop : Site 2)
    (baseLeftDual baseRightDual baseBottomDual baseTopDual : Site 2) :
    ∃ extentX extentY : Nat,
      0 < baseRight 0 + (extentX : Int) - baseLeft 0 ∧
      0 < baseRightDual 0 + (extentX : Int) - baseLeftDual 0 ∧
      0 < baseTop 1 + (extentY : Int) - baseBottom 1 ∧
      0 < baseTopDual 1 + (extentY : Int) - baseBottomDual 1 := by
  obtain ⟨extentX, extentY, _hX, _hY, hpX, hdX, hpY, hdY⟩ :=
    exists_commonPreferenceExtents_ge baseLeft baseRight baseBottom baseTop
      baseLeftDual baseRightDual baseBottomDual baseTopDual 0 0
  exact ⟨extentX, extentY, hpX, hdX, hpY, hdY⟩

end StatMech.FK.PeriodicPlanar
