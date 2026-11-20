/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.BoxConnectionFullConnection
import Code.FrontierD.FKQgt4RadialDecay




















open MeasureTheory SimpleGraph
open scoped BigOperators

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section


abbrev fkQgt4CriticalFreeMeasure {q : Real} (hq : 4 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site 2))) :=
  FK.freeInfiniteVolume 2
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    (by linarith : (0 : Real) < q)




theorem fkQgt4CriticalFree_infiniteTwoPointReal_eq_displacement
    {q : Real} (hq : 4 < q) (x y : Site 2) :
    FK.infiniteTwoPointReal
        (fkQgt4CriticalFreeMeasure hq :
          Measure (ConfigSpace (Sym2 (Site 2)))) x y =
      fkQgt4CriticalFreeTwoPoint hq (y - x) := by
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).1
  let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) <= q := by linarith
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  have htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site 2)) mu := by
    simpa [mu, hp, hp1, hq0] using
      (FK.fkgqt_freeIV_isTranslationInvariant
        (d := 2) hp hp1 hq1)
  have h := infiniteTwoPointReal_add_eq_of_translationInvariant
    mu htrans x (origin 2) (y - x)
  have hx0 : x + origin 2 = x := by
    funext i
    simp [origin]
  have hxy : x + (y - x) = y := by
    funext i
    simp
  rw [hx0, hxy] at h
  simpa [mu, hp, hp1, hq0, fkQgt4CriticalFreeMeasure,
    fkQgt4CriticalFreeTwoPoint] using h




theorem fkQgt4CriticalFree_boxConnEvent_le_displacement
    {q : Real} (hq : 4 < q) (radius : Nat)
    (x y : FK.boxVerts 2 radius) :
    ((fkQgt4CriticalFreeMeasure hq :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxConnEvent 2 radius x y) <=
      fkQgt4CriticalFreeTwoPoint hq (y.1 - x.1) := by
  calc
    _ <= FK.infiniteTwoPointReal
          (fkQgt4CriticalFreeMeasure hq :
            Measure (ConfigSpace (Sym2 (Site 2)))) x.1 y.1 :=
      FK.measureReal_boxConnEvent_le_infiniteTwoPointReal
        2 radius (fkQgt4CriticalFreeMeasure hq) x y
    _ = _ :=
      fkQgt4CriticalFree_infiniteTwoPointReal_eq_displacement hq x.1 y.1


def fkRectHorizontalCylinderLiftedDisplacement
    (dx : Int) (height : Nat) : Site 2 :=
  ![dx, (height : Int) - 1]


def fkRectHorizontalCylinderCorrection (dx : Int) : Site 2 :=
  ![-dx, 1]


def fkRectHorizontalCylinderVerticalDisplacement (height : Nat) : Site 2 :=
  ![0, (height : Int)]

theorem fkRectHorizontalCylinder_displacement_add_correction
    (dx : Int) (height : Nat) :
    fkRectHorizontalCylinderLiftedDisplacement dx height +
        fkRectHorizontalCylinderCorrection dx =
      fkRectHorizontalCylinderVerticalDisplacement height := by
  funext i
  fin_cases i <;>
    simp [fkRectHorizontalCylinderLiftedDisplacement,
      fkRectHorizontalCylinderCorrection,
      fkRectHorizontalCylinderVerticalDisplacement]



theorem fkQgt4CriticalFreeTwoPoint_horizontalCylinder_mul_correction_le_vertical
    {q : Real} (hq : 4 < q) (dx : Int) (height : Nat) :
    fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderLiftedDisplacement dx height) *
        fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderCorrection dx) <=
      fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderVerticalDisplacement height) := by
  have h := fkQgt4CriticalFreeTwoPoint_add_supermultiplicative hq
    (fkRectHorizontalCylinderLiftedDisplacement dx height)
    (fkRectHorizontalCylinderCorrection dx)
  rwa [fkRectHorizontalCylinder_displacement_add_correction] at h



theorem fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_vertical_div
    {q : Real} (hq : 4 < q) (dx : Int) (height : Nat) :
    fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderLiftedDisplacement dx height) <=
      fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderVerticalDisplacement height) /
        fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderCorrection dx) := by
  rw [le_div_iff₀ (fkQgt4CriticalFreeTwoPoint_pos hq
    (fkRectHorizontalCylinderCorrection dx))]
  exact
    fkQgt4CriticalFreeTwoPoint_horizontalCylinder_mul_correction_le_vertical
      hq dx height





noncomputable def fkRectHorizontalCylinderCorrectionFloor
    {q : Real} (hq : 4 < q) (width : Nat) : Real :=
  ∏ dx ∈ Finset.Icc (-(width : Int)) (width : Int),
    fkQgt4CriticalFreeTwoPoint hq
      (fkRectHorizontalCylinderCorrection dx)

theorem fkRectHorizontalCylinderCorrectionFloor_pos
    {q : Real} (hq : 4 < q) (width : Nat) :
    0 < fkRectHorizontalCylinderCorrectionFloor hq width := by
  unfold fkRectHorizontalCylinderCorrectionFloor
  exact Finset.prod_pos fun dx _ =>
    fkQgt4CriticalFreeTwoPoint_pos hq
      (fkRectHorizontalCylinderCorrection dx)


noncomputable def fkRectHorizontalCylinderTwoPointFactor
    {q : Real} (hq : 4 < q) (width : Nat) : Real :=
  (fkRectHorizontalCylinderCorrectionFloor hq width)⁻¹

theorem fkRectHorizontalCylinderTwoPointFactor_pos
    {q : Real} (hq : 4 < q) (width : Nat) :
    0 < fkRectHorizontalCylinderTwoPointFactor hq width := by
  exact inv_pos.mpr (fkRectHorizontalCylinderCorrectionFloor_pos hq width)

private theorem int_mem_Icc_neg_natCast_of_natAbs_le
    {dx : Int} {width : Nat} (h : dx.natAbs <= width) :
    dx ∈ Finset.Icc (-(width : Int)) (width : Int) := by
  rw [Finset.mem_Icc]
  rcases Int.natAbs_eq dx with hdx | hdx
  · omega
  · omega



theorem fkRectHorizontalCylinderCorrectionFloor_le
    {q : Real} (hq : 4 < q) {width : Nat} {dx : Int}
    (hdx : dx.natAbs <= width) :
    fkRectHorizontalCylinderCorrectionFloor hq width <=
      fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderCorrection dx) := by
  let s := Finset.Icc (-(width : Int)) (width : Int)
  let f : Int -> Real := fun a => fkQgt4CriticalFreeTwoPoint hq
    (fkRectHorizontalCylinderCorrection a)
  have hmem : dx ∈ s :=
    int_mem_Icc_neg_natCast_of_natAbs_le hdx
  have hf0 : forall a, 0 <= f a := fun a =>
    (fkQgt4CriticalFreeTwoPoint_pos hq
      (fkRectHorizontalCylinderCorrection a)).le
  have hf1 : forall a, f a <= 1 := fun a => by
    unfold f fkQgt4CriticalFreeTwoPoint FK.infiniteTwoPointReal
    exact measureReal_le_one
  have herase : (∏ a ∈ s.erase dx, f a) <= 1 :=
    Finset.prod_le_one
      (fun a _ => hf0 a)
      (fun a _ => hf1 a)
  change (∏ a ∈ s, f a) <= f dx
  rw [← Finset.prod_erase_mul s f hmem]
  exact mul_le_of_le_one_left (hf0 dx) herase


theorem fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_vertical_div_floor
    {q : Real} (hq : 4 < q) {width : Nat} {dx : Int}
    (hdx : dx.natAbs <= width) (height : Nat) :
    fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderLiftedDisplacement dx height) <=
      fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderVerticalDisplacement height) /
        fkRectHorizontalCylinderCorrectionFloor hq width := by
  have hfloor := fkRectHorizontalCylinderCorrectionFloor_le hq hdx
  have hpoint : 0 <= fkQgt4CriticalFreeTwoPoint hq
      (fkRectHorizontalCylinderLiftedDisplacement dx height) :=
    (fkQgt4CriticalFreeTwoPoint_pos hq _).le
  rw [le_div_iff₀ (fkRectHorizontalCylinderCorrectionFloor_pos hq width)]
  calc
    fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderLiftedDisplacement dx height) *
        fkRectHorizontalCylinderCorrectionFloor hq width <=
      fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderLiftedDisplacement dx height) *
        fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderCorrection dx) :=
      mul_le_mul_of_nonneg_left hfloor hpoint
    _ <= _ :=
      fkQgt4CriticalFreeTwoPoint_horizontalCylinder_mul_correction_le_vertical
        hq dx height


theorem fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_factor_mul_vertical
    {q : Real} (hq : 4 < q) {width : Nat} {dx : Int}
    (hdx : dx.natAbs <= width) (height : Nat) :
    fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderLiftedDisplacement dx height) <=
      fkRectHorizontalCylinderTwoPointFactor hq width *
        fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderVerticalDisplacement height) := by
  simpa [fkRectHorizontalCylinderTwoPointFactor, div_eq_inv_mul] using
    fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_vertical_div_floor
      hq hdx height




theorem fkQgt4CriticalFree_boxConnEvent_le_vertical_div_floor
    {q : Real} (hq : 4 < q) (radius : Nat)
    (x y : FK.boxVerts 2 radius) {width height : Nat} {dx : Int}
    (hdisp : y.1 - x.1 =
      fkRectHorizontalCylinderLiftedDisplacement dx height)
    (hdx : dx.natAbs <= width) :
    ((fkQgt4CriticalFreeMeasure hq :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxConnEvent 2 radius x y) <=
      fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderVerticalDisplacement height) /
        fkRectHorizontalCylinderCorrectionFloor hq width := by
  calc
    _ <= fkQgt4CriticalFreeTwoPoint hq (y.1 - x.1) :=
      fkQgt4CriticalFree_boxConnEvent_le_displacement hq radius x y
    _ = fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderLiftedDisplacement dx height) := by rw [hdisp]
    _ <= _ :=
      fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_vertical_div_floor
        hq hdx height


theorem fkQgt4CriticalFree_boxConnEvent_le_factor_mul_vertical
    {q : Real} (hq : 4 < q) (radius : Nat)
    (x y : FK.boxVerts 2 radius) {width height : Nat} {dx : Int}
    (hdisp : y.1 - x.1 =
      fkRectHorizontalCylinderLiftedDisplacement dx height)
    (hdx : dx.natAbs <= width) :
    ((fkQgt4CriticalFreeMeasure hq :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxConnEvent 2 radius x y) <=
      fkRectHorizontalCylinderTwoPointFactor hq width *
        fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderVerticalDisplacement height) := by
  simpa [fkRectHorizontalCylinderTwoPointFactor, div_eq_inv_mul] using
    fkQgt4CriticalFree_boxConnEvent_le_vertical_div_floor
      hq radius x y hdisp hdx

end

end StatMech.FrontierD
