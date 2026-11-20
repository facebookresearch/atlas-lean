/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldRecursiveLimits
import Code.FK.PeriodicPlanarSheffieldNormalBoundaryBandAssembly
import Code.FK.PeriodicPlanarSheffieldCommonSquareEnlarge









open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}




structure PairedAlignedMarginSchedule
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    (verticalRequirement horizontalRequirement : Nat → Nat) where
  horizontal : Nat → Nat
  vertical : Nat → Nat
  horizontal_tendsto : Tendsto horizontal atTop atTop
  vertical_tendsto : Tendsto vertical atTop atTop
  vertical_requirement : ∀ n,
    verticalRequirement (horizontal n) ≤ vertical n
  horizontal_requirement : ∀ n,
    horizontalRequirement (vertical n) ≤ horizontal (n + 1)
  primal_left_bottom : ∀ n,
    (family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 ≤
      family.baseBottom 1 + vertical n
  primal_right_bottom : ∀ n,
    (family.radiusRight (horizontal n) : Int) + family.baseRight 1 ≤
      family.baseBottom 1 + vertical n
  primal_left_top : ∀ n,
    (family.radiusLeft (horizontal n) : Int) + family.baseTop 1 ≤
      family.baseLeft 1 + vertical n
  primal_right_top : ∀ n,
    (family.radiusRight (horizontal n) : Int) + family.baseTop 1 ≤
      family.baseRight 1 + vertical n
  primal_bottom_left : ∀ n,
    (family.radiusBottom (vertical n) : Int) + family.baseBottom 0 ≤
      family.baseLeft 0 + horizontal (n + 1)
  primal_top_left : ∀ n,
    (family.radiusTop (vertical n) : Int) + family.baseTop 0 ≤
      family.baseLeft 0 + horizontal (n + 1)
  primal_bottom_right : ∀ n,
    (family.radiusBottom (vertical n) : Int) + family.baseRight 0 ≤
      family.baseBottom 0 + horizontal (n + 1)
  primal_top_right : ∀ n,
    (family.radiusTop (vertical n) : Int) + family.baseRight 0 ≤
      family.baseTop 0 + horizontal (n + 1)
  dual_left_bottom : ∀ n,
    (familyDual.radiusLeft (horizontal n) : Int) + familyDual.baseLeft 1 ≤
      familyDual.baseBottom 1 + vertical n
  dual_right_bottom : ∀ n,
    (familyDual.radiusRight (horizontal n) : Int) +
      familyDual.baseRight 1 ≤ familyDual.baseBottom 1 + vertical n
  dual_left_top : ∀ n,
    (familyDual.radiusLeft (horizontal n) : Int) + familyDual.baseTop 1 ≤
      familyDual.baseLeft 1 + vertical n
  dual_right_top : ∀ n,
    (familyDual.radiusRight (horizontal n) : Int) + familyDual.baseTop 1 ≤
      familyDual.baseRight 1 + vertical n
  dual_bottom_left : ∀ n,
    (familyDual.radiusBottom (vertical n) : Int) +
      familyDual.baseBottom 0 ≤ familyDual.baseLeft 0 + horizontal (n + 1)
  dual_top_left : ∀ n,
    (familyDual.radiusTop (vertical n) : Int) + familyDual.baseTop 0 ≤
      familyDual.baseLeft 0 + horizontal (n + 1)
  dual_bottom_right : ∀ n,
    (familyDual.radiusBottom (vertical n) : Int) +
      familyDual.baseRight 0 ≤ familyDual.baseBottom 0 + horizontal (n + 1)
  dual_top_right : ∀ n,
    (familyDual.radiusTop (vertical n) : Int) + familyDual.baseRight 0 ≤
      familyDual.baseTop 0 + horizontal (n + 1)

private theorem int_le_nat_of_toNat_le_paired {x : Int} {n : Nat}
    (h : x.toNat ≤ n) : x ≤ n := by
  by_cases hx : 0 ≤ x
  · have h' : (x.toNat : Int) ≤ (n : Int) := by exact_mod_cast h
    rwa [Int.toNat_of_nonneg hx] at h'
  · omega




theorem exists_pairedAlignedMarginSchedule
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    (verticalRequirement horizontalRequirement : Nat → Nat) :
    Nonempty (PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement) := by
  let verticalStep : Nat → Nat := fun h ↦ max
    (max (family.fullVerticalRequirement E h)
      (familyDual.fullVerticalRequirement Edual h))
    (verticalRequirement h)
  let horizontalStep : Nat → Nat := fun v ↦ max
    (max (family.fullHorizontalRequirement E v)
      (familyDual.fullHorizontalRequirement Edual v))
    (horizontalRequirement v)
  obtain ⟨horizontal, vertical, hh, hv, hhv, hvh⟩ :=
    exists_alternating_dominating_sequences verticalStep horizontalStep
  have hPV (n : Nat) : family.fullVerticalRequirement E (horizontal n) ≤
      vertical n :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans (hhv n))
  have hDV (n : Nat) :
      familyDual.fullVerticalRequirement Edual (horizontal n) ≤ vertical n :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans (hhv n))
  have hPH (n : Nat) : family.fullHorizontalRequirement E (vertical n) ≤
      horizontal (n + 1) :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans (hvh n))
  have hDH (n : Nat) :
      familyDual.fullHorizontalRequirement Edual (vertical n) ≤
        horizontal (n + 1) :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans (hvh n))
  have verticalReq (n : Nat) :
      verticalRequirement (horizontal n) ≤ vertical n :=
    (Nat.le_max_right _ _).trans (hhv n)
  have horizontalReq (n : Nat) :
      horizontalRequirement (vertical n) ≤ horizontal (n + 1) :=
    (Nat.le_max_right _ _).trans (hvh n)
  refine ⟨{
    horizontal := horizontal
    vertical := vertical
    horizontal_tendsto := hh
    vertical_tendsto := hv
    vertical_requirement := verticalReq
    horizontal_requirement := horizontalReq
    primal_left_bottom := ?_
    primal_right_bottom := ?_
    primal_left_top := ?_
    primal_right_top := ?_
    primal_bottom_left := ?_
    primal_top_left := ?_
    primal_bottom_right := ?_
    primal_top_right := ?_
    dual_left_bottom := ?_
    dual_right_bottom := ?_
    dual_left_top := ?_
    dual_right_top := ?_
    dual_bottom_left := ?_
    dual_top_left := ?_
    dual_bottom_right := ?_
    dual_top_right := ?_ }⟩
  all_goals intro n
  · have h := (Nat.le_max_left
      (max (((family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 - family.baseBottom 1).toNat)
        (((family.radiusRight (horizontal n) : Int) +
          family.baseRight 1 - family.baseBottom 1).toNat)) _).trans (hPV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_left
      (max (((family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 - family.baseBottom 1).toNat)
        (((family.radiusRight (horizontal n) : Int) +
          family.baseRight 1 - family.baseBottom 1).toNat)) _).trans (hPV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hPV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hPV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_left _ _).trans (hPH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_left _ _).trans (hPH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hPH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hPH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_left
      (max (((familyDual.radiusLeft (horizontal n) : Int) +
        familyDual.baseLeft 1 - familyDual.baseBottom 1).toNat)
        (((familyDual.radiusRight (horizontal n) : Int) +
          familyDual.baseRight 1 - familyDual.baseBottom 1).toNat)) _).trans
      (hDV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_left
      (max (((familyDual.radiusLeft (horizontal n) : Int) +
        familyDual.baseLeft 1 - familyDual.baseBottom 1).toNat)
        (((familyDual.radiusRight (horizontal n) : Int) +
          familyDual.baseRight 1 - familyDual.baseBottom 1).toNat)) _).trans
      (hDV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hDV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hDV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_left _ _).trans (hDH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_left _ _).trans (hDH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hDH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hDH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega




theorem exists_pairedMixedGridDimensions
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    (horizontalMargin verticalMargin minimumX minimumY : Nat) :
    ∃ extentX extentY width height widthDual heightDual : Nat,
      minimumX ≤ extentX ∧ minimumY ≤ extentY ∧
      0 < width ∧ 0 < height ∧ 0 < widthDual ∧ 0 < heightDual ∧
      (family.baseLeft 0 + horizontalMargin + width -
        (family.baseRight 0 - horizontalMargin) : Int) = extentX ∧
      (familyDual.baseLeft 0 + horizontalMargin + widthDual -
        (familyDual.baseRight 0 - horizontalMargin) : Int) = extentX ∧
      (family.baseBottom 1 + verticalMargin + height -
        (family.baseTop 1 - verticalMargin) : Int) = extentY ∧
      (familyDual.baseBottom 1 + verticalMargin + heightDual -
        (familyDual.baseTop 1 - verticalMargin) : Int) = extentY := by
  let left : Site 2 := family.baseLeft + horizontalShift horizontalMargin
  let right : Site 2 := family.baseRight +
    horizontalShift (-(horizontalMargin : Int))
  let bottom : Site 2 := family.baseBottom + verticalShift verticalMargin
  let top : Site 2 := family.baseTop +
    verticalShift (-(verticalMargin : Int))
  let leftDual : Site 2 :=
    familyDual.baseLeft + horizontalShift horizontalMargin
  let rightDual : Site 2 := familyDual.baseRight +
    horizontalShift (-(horizontalMargin : Int))
  let bottomDual : Site 2 :=
    familyDual.baseBottom + verticalShift verticalMargin
  let topDual : Site 2 := familyDual.baseTop +
    verticalShift (-(verticalMargin : Int))
  obtain ⟨extentX, extentY, hminX, hminY,
      hx, hxDual, hy, hyDual⟩ :=
    exists_commonPreferenceExtents_ge left right bottom top
      leftDual rightDual bottomDual topDual minimumX minimumY
  let width := boundaryGridWidth extentX left right
  let height := boundaryGridHeight extentY bottom top
  let widthDual := boundaryGridWidth extentX leftDual rightDual
  let heightDual := boundaryGridHeight extentY bottomDual topDual
  have hwidth : 0 < width := boundaryGridWidth_pos _ _ _ hx
  have hheight : 0 < height := boundaryGridHeight_pos _ _ _ hy
  have hwidthDual : 0 < widthDual :=
    boundaryGridWidth_pos _ _ _ hxDual
  have hheightDual : 0 < heightDual :=
    boundaryGridHeight_pos _ _ _ hyDual
  refine ⟨extentX, extentY, width, height, widthDual, heightDual,
    hminX, hminY, hwidth, hheight, hwidthDual, hheightDual,
    ?_, ?_, ?_, ?_⟩
  · have hnonneg : 0 ≤ right 0 + (extentX : Int) - left 0 := hx.le
    have hwidthCast : (width : Int) = right 0 + extentX - left 0 := by
      dsimp only [width, boundaryGridWidth]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hwidthCast]
    simp [left, right]
    omega
  · have hnonneg :
      0 ≤ rightDual 0 + (extentX : Int) - leftDual 0 := hxDual.le
    have hwidthCast :
        (widthDual : Int) = rightDual 0 + extentX - leftDual 0 := by
      dsimp only [widthDual, boundaryGridWidth]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hwidthCast]
    simp [leftDual, rightDual]
    omega
  · have hnonneg : 0 ≤ top 1 + (extentY : Int) - bottom 1 := hy.le
    have hheightCast : (height : Int) = top 1 + extentY - bottom 1 := by
      dsimp only [height, boundaryGridHeight]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hheightCast]
    simp [bottom, top]
    omega
  · have hnonneg :
      0 ≤ topDual 1 + (extentY : Int) - bottomDual 1 := hyDual.le
    have hheightCast :
        (heightDual : Int) = topDual 1 + extentY - bottomDual 1 := by
      dsimp only [heightDual, boundaryGridHeight]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hheightCast]
    simp [bottomDual, topDual]
    omega



structure PairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real) where
  width : Nat
  height : Nat
  widthDual : Nat
  heightDual : Nat
  width_pos : 0 < width
  height_pos : 0 < height
  widthDual_pos : 0 < widthDual
  heightDual_pos : 0 < heightDual
  base : Site 2
  baseDual : Site 2
  narrowRight : Real
  shortTop : Real
  wideLeft : Real
  wideRight : Real
  tallTop : Real
  wideLeft_le : wideLeft ≤ 0
  narrowRight_le : narrowRight ≤ wideRight
  shortTop_le : shortTop ≤ tallTop
  primal_bottom : ∀ i : Fin (width + 1), p < mu.real
    (E.rectSideConnectionEvent wideLeft wideRight 0 shortTop
      (P.shift (base + preferenceGridSite
        (i, (0 : Fin (height + 1)))) '' (S : Set V))
      (E.rectBottomBoundaryVertices wideLeft wideRight 0 shortTop))
  primal_top : ∀ i : Fin (width + 1), p < mu.real
    (E.rectSideConnectionEvent wideLeft wideRight 0 shortTop
      (P.shift (base + preferenceGridSite
        (i, Fin.last height)) '' (S : Set V))
      (E.rectTopBoundaryVertices wideLeft wideRight 0 shortTop))
  primal_left : ∀ j : Fin (height + 1), p < mu.real
    (E.rectSideConnectionEvent 0 narrowRight 0 tallTop
      (P.shift (base + preferenceGridSite
        ((0 : Fin (width + 1)), j)) '' (S : Set V))
      (E.rectLeftBoundaryVertices 0 narrowRight 0 tallTop))
  primal_right : ∀ j : Fin (height + 1), p < mu.real
    (E.rectSideConnectionEvent 0 narrowRight 0 tallTop
      (P.shift (base + preferenceGridSite
        (Fin.last width, j)) '' (S : Set V))
      (E.rectRightBoundaryVertices 0 narrowRight 0 tallTop))
  dual_bottom : ∀ i : Fin (widthDual + 1), pDual < muDual.real
    (Edual.rectSideConnectionEvent wideLeft wideRight 0 shortTop
      (Pdual.shift (baseDual + preferenceGridSite
        (i, (0 : Fin (heightDual + 1)))) '' (Sdual : Set W))
      (Edual.rectBottomBoundaryVertices wideLeft wideRight 0 shortTop))
  dual_top : ∀ i : Fin (widthDual + 1), pDual < muDual.real
    (Edual.rectSideConnectionEvent wideLeft wideRight 0 shortTop
      (Pdual.shift (baseDual + preferenceGridSite
        (i, Fin.last heightDual)) '' (Sdual : Set W))
      (Edual.rectTopBoundaryVertices wideLeft wideRight 0 shortTop))
  dual_left : ∀ j : Fin (heightDual + 1), pDual < muDual.real
    (Edual.rectSideConnectionEvent 0 narrowRight 0 tallTop
      (Pdual.shift (baseDual + preferenceGridSite
        ((0 : Fin (widthDual + 1)), j)) '' (Sdual : Set W))
      (Edual.rectLeftBoundaryVertices 0 narrowRight 0 tallTop))
  dual_right : ∀ j : Fin (heightDual + 1), pDual < muDual.real
    (Edual.rectSideConnectionEvent 0 narrowRight 0 tallTop
      (Pdual.shift (baseDual + preferenceGridSite
        (Fin.last widthDual, j)) '' (Sdual : Set W))
      (Edual.rectRightBoundaryVertices 0 narrowRight 0 tallTop))



theorem exists_pairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat → Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k : Nat) :
    Nonempty (PairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual) := by
  let h := schedule.horizontal k
  let v := schedule.vertical k
  let minimumX := max
    (max (family.radiusLeft h) (family.radiusRight h))
    (max (familyDual.radiusLeft h) (familyDual.radiusRight h))
  let minimumY := max
    (max (family.radiusBottom v) (family.radiusTop v))
    (max (familyDual.radiusBottom v) (familyDual.radiusTop v))
  obtain ⟨extentX, extentY, width, height, widthDual, heightDual,
      hminX, hminY, hwidth, hheight, hwidthDual, hheightDual,
      hb, hbDual, hd, hdDual⟩ :=
    exists_pairedMixedGridDimensions E Edual family familyDual
      h v minimumX minimumY
  let base : Site 2 := fun i ↦ if i = 0 then
    family.baseLeft 0 + h else family.baseBottom 1 + v
  let baseDual : Site 2 := fun i ↦ if i = 0 then
    familyDual.baseLeft 0 + h else familyDual.baseBottom 1 + v
  let bottomLower : Int := base 0 - family.baseBottom 0 -
    family.radiusBottom v
  let topLower : Int := base 0 - family.baseTop 0 - family.radiusTop v
  let aP : Int := min 0 (min bottomLower topLower)
  let bottomUpper : Int := base 0 + width - family.baseBottom 0 +
    family.radiusBottom v
  let topUpper : Int := base 0 + width - family.baseTop 0 +
    family.radiusTop v
  let bP : Int := max extentX (max bottomUpper topUpper)
  let leftUpper : Int := base 1 + height - family.baseLeft 1 +
    family.radiusLeft h
  let rightUpper : Int := base 1 + height - family.baseRight 1 +
    family.radiusRight h
  let dP : Int := max extentY (max leftUpper rightUpper)
  let bottomLowerDual : Int := baseDual 0 - familyDual.baseBottom 0 -
    familyDual.radiusBottom v
  let topLowerDual : Int := baseDual 0 - familyDual.baseTop 0 -
    familyDual.radiusTop v
  let aD : Int := min 0 (min bottomLowerDual topLowerDual)
  let bottomUpperDual : Int := baseDual 0 + widthDual -
    familyDual.baseBottom 0 + familyDual.radiusBottom v
  let topUpperDual : Int := baseDual 0 + widthDual -
    familyDual.baseTop 0 + familyDual.radiusTop v
  let bD : Int := max extentX (max bottomUpperDual topUpperDual)
  let leftUpperDual : Int := baseDual 1 + heightDual -
    familyDual.baseLeft 1 + familyDual.radiusLeft h
  let rightUpperDual : Int := baseDual 1 + heightDual -
    familyDual.baseRight 1 + familyDual.radiusRight h
  let dD : Int := max extentY (max leftUpperDual rightUpperDual)
  let a := min aP aD
  let b := max bP bD
  let d := max dP dD
  have hleftP : (family.radiusLeft h : Int) ≤ extentX := by
    exact_mod_cast (Nat.le_max_left _ _ |>.trans
      (Nat.le_max_left _ _) |>.trans hminX)
  have hrightP : (family.radiusRight h : Int) ≤ extentX := by
    exact_mod_cast (Nat.le_max_right _ _ |>.trans
      (Nat.le_max_left _ _) |>.trans hminX)
  have hbottomP : (family.radiusBottom v : Int) ≤ extentY := by
    exact_mod_cast (Nat.le_max_left _ _ |>.trans
      (Nat.le_max_left _ _) |>.trans hminY)
  have htopP : (family.radiusTop v : Int) ≤ extentY := by
    exact_mod_cast (Nat.le_max_right _ _ |>.trans
      (Nat.le_max_left _ _) |>.trans hminY)
  have hleftD : (familyDual.radiusLeft h : Int) ≤ extentX := by
    exact_mod_cast (Nat.le_max_left _ _ |>.trans
      (Nat.le_max_right _ _) |>.trans hminX)
  have hrightD : (familyDual.radiusRight h : Int) ≤ extentX := by
    exact_mod_cast (Nat.le_max_right _ _ |>.trans
      (Nat.le_max_right _ _) |>.trans hminX)
  have hbottomD : (familyDual.radiusBottom v : Int) ≤ extentY := by
    exact_mod_cast (Nat.le_max_left _ _ |>.trans
      (Nat.le_max_right _ _) |>.trans hminY)
  have htopD : (familyDual.radiusTop v : Int) ≤ extentY := by
    exact_mod_cast (Nat.le_max_right _ _ |>.trans
      (Nat.le_max_right _ _) |>.trans hminY)
  have hmixedP := family.mixedBoundaryScores E mu hTI h v width height
    (schedule.primal_left_bottom k) (schedule.primal_right_bottom k)
    (by simpa [base, hb] using hleftP)
    (by simpa [base, hb] using hrightP)
    (by simpa [base, hd] using hbottomP)
    (by simpa [base, hd] using htopP)
  have hmixedD := familyDual.mixedBoundaryScores Edual muDual hTIDual
    h v widthDual heightDual (schedule.dual_left_bottom k)
    (schedule.dual_right_bottom k)
    (by simpa [baseDual, hbDual] using hleftD)
    (by simpa [baseDual, hbDual] using hrightD)
    (by simpa [baseDual, hdDual] using hbottomD)
    (by simpa [baseDual, hdDual] using htopD)
  dsimp only at hmixedP hmixedD
  simp only [if_pos (rfl : (0 : Fin 2) = 0),
    if_neg (by decide : (1 : Fin 2) ≠ 0), if_true, if_false]
      at hmixedP hmixedD
  rw [hb, hd] at hmixedP
  rw [hbDual, hdDual] at hmixedD
  change (((aP : Real) ≤ 0 ∧ (extentX : Real) ≤ bP ∧
      (0 : Real) ≤ 0 ∧ (extentY : Real) ≤ dP) ∧ _) at hmixedP
  change (((aD : Real) ≤ 0 ∧ (extentX : Real) ≤ bD ∧
      (0 : Real) ≤ 0 ∧ (extentY : Real) ≤ dD) ∧ _) at hmixedD
  refine ⟨{
    width := width
    height := height
    widthDual := widthDual
    heightDual := heightDual
    width_pos := hwidth
    height_pos := hheight
    widthDual_pos := hwidthDual
    heightDual_pos := hheightDual
    base := base
    baseDual := baseDual
    narrowRight := extentX
    shortTop := extentY
    wideLeft := a
    wideRight := b
    tallTop := d
    wideLeft_le := by
      have hmin : (a : Real) ≤ (aP : Real) := by
        exact_mod_cast min_le_left aP aD
      exact hmin.trans hmixedP.1.1
    narrowRight_le := by
      have hmax : (bP : Real) ≤ (b : Real) := by
        exact_mod_cast le_max_left bP bD
      exact hmixedP.1.2.1.trans hmax
    shortTop_le := by
      have hmax : (dP : Real) ≤ (d : Real) := by
        exact_mod_cast le_max_left dP dD
      exact hmixedP.1.2.2.2.trans hmax
    primal_bottom := ?_
    primal_top := ?_
    primal_left := ?_
    primal_right := ?_
    dual_bottom := ?_
    dual_top := ?_
    dual_left := ?_
    dual_right := ?_ }⟩
  · intro i
    exact (hmixedP.2.1 i).trans_le (measureReal_mono
      (E.rectBottomConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_left aP aD)
        (by exact_mod_cast le_max_left bP bD) le_rfl))
  · intro i
    exact (hmixedP.2.2.1 i).trans_le (measureReal_mono
      (E.rectTopConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_left aP aD)
        (by exact_mod_cast le_max_left bP bD) le_rfl))
  · intro j
    exact (hmixedP.2.2.2.1 j).trans_le (measureReal_mono
      (E.rectLeftConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_left dP dD)))
  · intro j
    exact (hmixedP.2.2.2.2 j).trans_le (measureReal_mono
      (E.rectRightConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_left dP dD)))
  · intro i
    exact (hmixedD.2.1 i).trans_le (measureReal_mono
      (Edual.rectBottomConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_right aP aD)
        (by exact_mod_cast le_max_right bP bD) le_rfl))
  · intro i
    exact (hmixedD.2.2.1 i).trans_le (measureReal_mono
      (Edual.rectTopConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_right aP aD)
        (by exact_mod_cast le_max_right bP bD) le_rfl))
  · intro j
    exact (hmixedD.2.2.2.1 j).trans_le (measureReal_mono
      (Edual.rectLeftConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_right dP dD)))
  · intro j
    exact (hmixedD.2.2.2.2 j).trans_le (measureReal_mono
      (Edual.rectRightConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_right dP dD)))



theorem exists_pairedCofinalNormalBoundaryBandFamilies_bounded
    (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W))) [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
    ∃ (p pDual : Nat → Real)
      (family : ∀ m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m))
      (familyDual : ∀ m,
        Edual.NormalBoundaryBandFamily muDual
          (Pdual.orbitBox m) (pDual m)),
      Tendsto p atTop (nhds 1) ∧
      (∀ m, p m ≤ 1) ∧
      Tendsto pDual atTop (nhds 1) ∧
      (∀ m, pDual m ≤ 1) := by
  obtain ⟨p, family, hp, hp_le⟩ :=
    E.exists_cofinalNormalBoundaryBandFamilies_bounded
      mu hFKG hTI hunique
  obtain ⟨pDual, familyDual, hpDual, hpDual_le⟩ :=
    Edual.exists_cofinalNormalBoundaryBandFamilies_bounded
      muDual hFKGDual hTIDual huniqueDual
  exact ⟨p, pDual, family, familyDual,
    hp, hp_le, hpDual, hpDual_le⟩



theorem exists_pairedCofinalMatchedCommonSquareNormalBoundaryBandData
    (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W))) [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (margin : Nat → Nat) :
    ∃ (p pDual : Nat → Real)
      (family : ∀ m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m))
      (familyDual : ∀ m,
        Edual.NormalBoundaryBandFamily muDual
          (Pdual.orbitBox m) (pDual m))
      (M : Nat → Nat),
      (∀ m, Nonempty (E.CommonSquareNormalBoundaryBandData
        mu (P.orbitBox m) (margin m) (M m) (p m))) ∧
      (∀ m, Nonempty (Edual.CommonSquareNormalBoundaryBandData
        muDual (Pdual.orbitBox m) (margin m) (M m) (pDual m))) ∧
      Tendsto p atTop (nhds 1) ∧
      (∀ m, p m ≤ 1) ∧
      Tendsto pDual atTop (nhds 1) ∧
      (∀ m, pDual m ≤ 1) := by
  obtain ⟨p, pDual, family, familyDual,
      hp, hp_le, hpDual, hpDual_le⟩ :=
    exists_pairedCofinalNormalBoundaryBandFamilies_bounded
      E Edual mu muDual hFKG hTI hunique hFKGDual hTIDual huniqueDual
  have hmatched (m : Nat) :
      ∃ M : Nat,
        Nonempty (E.CommonSquareNormalBoundaryBandData
          mu (P.orbitBox m) (margin m) M (p m)) ∧
        Nonempty (Edual.CommonSquareNormalBoundaryBandData
          muDual (Pdual.orbitBox m) (margin m) M (pDual m)) :=
    exists_matched_commonSquareNormalBoundaryBandData E Edual mu muDual
      hTI hTIDual ((family m).seed E (margin m))
        ((familyDual m).seed Edual (margin m))
  let M : Nat → Nat := fun m ↦ Classical.choose (hmatched m)
  have hdata (m : Nat) := Classical.choose_spec (hmatched m)
  exact ⟨p, pDual, family, familyDual, M,
    fun m ↦ (hdata m).1, fun m ↦ (hdata m).2,
    hp, hp_le, hpDual, hpDual_le⟩



theorem exists_pairedUniformConnectorRadii_with_commonHalfWidthData
    (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W))) [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
    ∃ (radius radiusDual : Nat → Nat),
      E.UniformConnectorCrossingRadius mu radius ∧
      Edual.UniformConnectorCrossingRadius muDual radiusDual ∧
      ∃ (primal : E.ConnectorReadyCommonSquareData mu radius)
        (dual : Edual.ConnectorReadyCommonSquareData muDual radiusDual),
        primal.M = dual.M := by
  obtain ⟨radius, hradius, ⟨primal⟩⟩ :=
    E.exists_uniformConnectorRadius_with_commonSquare
      mu hFKG hTI hunique
  obtain ⟨radiusDual, hradiusDual, ⟨dual⟩⟩ :=
    Edual.exists_uniformConnectorRadius_with_commonSquare
      muDual hFKGDual hTIDual huniqueDual
  obtain ⟨primal', dual', hprimalM, hdualM⟩ :=
    exists_commonHalfWidth_connectorReadyData
      E Edual hTI hTIDual primal dual
  exact ⟨radius, radiusDual, hradius, hradiusDual,
    primal', dual', hprimalM.trans hdualM.symm⟩




theorem PeriodicPlanarDualPair.exists_canonicalMatchedBoundaryBands_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hcommon :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1)
    (margin : Nat → Nat) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    let muDual : Measure (ConfigSpace (Sym2 W)) := D.dualMeasure mu
    ∃ (score scoreDual : Nat → Real)
      (family : ∀ m, D.primalEmbedding.NormalBoundaryBandFamily
        mu (P.orbitBox m) (score m))
      (familyDual : ∀ m, D.dualEmbedding.NormalBoundaryBandFamily
        muDual (Pdual.orbitBox m) (scoreDual m))
      (M : Nat → Nat),
      (∀ m, Nonempty
        (D.primalEmbedding.CommonSquareNormalBoundaryBandData
          mu (P.orbitBox m) (margin m) (M m) (score m))) ∧
      (∀ m, Nonempty
        (D.dualEmbedding.CommonSquareNormalBoundaryBandData
          muDual (Pdual.orbitBox m) (margin m) (M m) (scoreDual m))) ∧
      Tendsto score atTop (nhds 1) ∧
      (∀ m, score m ≤ 1) ∧
      Tendsto scoreDual atTop (nhds 1) ∧
      (∀ m, scoreDual m ≤ 1) := by
  dsimp only
  letI : IsProbabilityMeasure
      (D.dualMeasure
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V)))) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  have hdata := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  exact exists_pairedCofinalMatchedCommonSquareNormalBoundaryBandData
    D.primalEmbedding D.dualEmbedding _ _
      hdata.1 hdata.2.1 hdata.2.2.2.2.1
      hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.2
      margin



theorem PeriodicPlanarDualPair.exists_canonicalConnectorReadyData_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hcommon :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    let muDual : Measure (ConfigSpace (Sym2 W)) := D.dualMeasure mu
    ∃ (radius radiusDual : Nat → Nat),
      D.primalEmbedding.UniformConnectorCrossingRadius mu radius ∧
      D.dualEmbedding.UniformConnectorCrossingRadius muDual radiusDual ∧
      ∃ (primal : D.primalEmbedding.ConnectorReadyCommonSquareData
          mu radius)
        (dual : D.dualEmbedding.ConnectorReadyCommonSquareData
          muDual radiusDual),
        primal.M = dual.M := by
  dsimp only
  letI : IsProbabilityMeasure
      (D.dualMeasure
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V)))) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  have hdata := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  exact exists_pairedUniformConnectorRadii_with_commonHalfWidthData
    D.primalEmbedding D.dualEmbedding _ _
      hdata.1 hdata.2.1 hdata.2.2.2.2.1
      hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.2

end StatMech.FK.PeriodicPlanar
