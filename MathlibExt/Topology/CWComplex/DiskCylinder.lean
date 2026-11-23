/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ClosedBall.NDR
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Homotopy.Affine

/-!
# Both collapses of the actual classical disk cylinder

The constructed disk-boundary NDR supplies the bottom-plus-side retraction.
Affine interpolation in the original disk and interval gives an ordinary
relative homotopy. Spatial interval reflection constructs the other collapse,
leaving deformation time unchanged.
-/

public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace Topology.CWComplex

/-- The actual bottom-plus-side rim in the classical disk cylinder. -/
abbrev classicalDiskCylinderBottomPair (n : ℕ) : TopPair.{u} :=
  TopPair.hurewiczCylinderPair (classicalCellDiskPair.{u} n)

/-- The actual top-plus-side rim in the same classical disk cylinder. -/
abbrev classicalDiskCylinderTopPair (n : ℕ) : TopPair.{u} :=
  TopPair.ofSubset
    (X := TopCat.of ((classicalCellDiskPair.{u} n).fst × TopCat.I.{u}))
    ((Set.range (classicalCellDiskPair.{u} n).map).unionProd
      ({(1 : TopCat.I.{u})} : Set TopCat.I.{u}))

private abbrev Cylinder (n : ℕ) := (classicalDiskCylinderBottomPair.{u} n).fst

/-- Reflection of the spatial interval in the literal classical disk cylinder. -/
def classicalDiskCylinderReflection (n : ℕ) :
    (classicalDiskCylinderBottomPair.{u} n).fst ≃ₜ
      (classicalDiskCylinderBottomPair.{u} n).fst :=
  (Homeomorph.refl (classicalCellDiskPair.{u} n).fst).prodCongr
    ((TopCat.I.homeomorph.trans unitInterval.symmHomeomorph).trans
      TopCat.I.homeomorph.symm)

private theorem reflection_apply (n : ℕ) (z : Cylinder.{u} n) :
    classicalDiskCylinderReflection.{u} n z = (z.1, TopCat.I.symm z.2) := rfl

private theorem reflection_involutive (n : ℕ) :
    Function.Involutive (classicalDiskCylinderReflection.{u} n) := by
  intro z
  apply Prod.ext
  · rfl
  · apply TopCat.I.ext
    change unitInterval.symm (unitInterval.symm (TopCat.I.homeomorph z.2)) =
      TopCat.I.homeomorph z.2
    exact unitInterval.symm_symm _

private def rimReflection (n : ℕ) :
    (classicalDiskCylinderBottomPair.{u} n).snd ≃ₜ
      (classicalDiskCylinderTopPair.{u} n).snd where
  toFun b := ⟨classicalDiskCylinderReflection n b.1, by
    rcases Set.mem_unionProd.mp b.2 with hx | ht
    · exact Set.mem_unionProd.mpr (Or.inl hx)
    · apply Set.mem_unionProd.mpr
      right
      have ht' : b.1.2 = 0 := ht
      change TopCat.I.symm b.1.2 = 1
      rw [ht', TopCat.I.symm_zero]⟩
  invFun b := ⟨classicalDiskCylinderReflection n b.1, by
    rcases Set.mem_unionProd.mp b.2 with hx | ht
    · exact Set.mem_unionProd.mpr (Or.inl hx)
    · apply Set.mem_unionProd.mpr
      right
      have ht' : b.1.2 = 1 := ht
      change TopCat.I.symm b.1.2 = 0
      rw [ht', TopCat.I.symm_one]⟩
  left_inv b := Subtype.ext (reflection_involutive n b.1)
  right_inv b := Subtype.ext (reflection_involutive n b.1)
  continuous_toFun :=
    ((classicalDiskCylinderReflection n).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((classicalDiskCylinderReflection n).continuous.comp continuous_subtype_val).subtype_mk _

private def bottomRetraction (n : ℕ) :
    C((classicalDiskCylinderBottomPair.{u} n).fst,
      (classicalDiskCylinderBottomPair.{u} n).snd) :=
  ((classicalCellDiskPairNDRData.{u} n).toStandard.cylinderRetraction).hom

private theorem bottomRetraction_boundary (n : ℕ)
    (b : (classicalDiskCylinderBottomPair.{u} n).snd) :
    bottomRetraction n ((classicalDiskCylinderBottomPair n).map b) = b :=
  (classicalCellDiskPairNDRData.{u} n).toStandard.hurewiczCofibrationData
    |>.cylinderRetraction_boundary b

private def bottomIncludedRetraction (n : ℕ) : C(Cylinder.{u} n, Cylinder.{u} n) :=
  (classicalDiskCylinderBottomPair n).map.hom.comp (bottomRetraction n)

private theorem bottomIncludedRetraction_fixed (n : ℕ)
    (b : (classicalDiskCylinderBottomPair.{u} n).snd) :
    bottomIncludedRetraction n ((classicalDiskCylinderBottomPair n).map b) =
      (classicalDiskCylinderBottomPair n).map b := by
  exact congrArg (classicalDiskCylinderBottomPair n).map (bottomRetraction_boundary n b)

private def vectorProjection (n : ℕ) : C(Cylinder.{u} n, Fin n → ℝ) where
  toFun z := z.1.down.val
  continuous_toFun :=
    continuous_subtype_val.comp (continuous_uliftDown.comp continuous_fst)

private def bottomVectorHomotopy (n : ℕ) :
    (vectorProjection.{u} n).Homotopy
      ((vectorProjection n).comp (bottomIncludedRetraction n)) :=
  ContinuousMap.Homotopy.affine _ _

private theorem bottomVectorHomotopy_mem (n : ℕ)
    (s : unitInterval) (z : Cylinder.{u} n) :
    bottomVectorHomotopy n (s, z) ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := by
  change AffineMap.lineMap z.1.down.val
    (bottomIncludedRetraction n z).1.down.val (s : ℝ) ∈ _
  exact (convex_closedBall (0 : Fin n → ℝ) 1).lineMap_mem
    z.1.down.property (bottomIncludedRetraction n z).1.down.property s.property

private theorem bottomVectorHomotopy_apply (n : ℕ)
    (s : unitInterval) (z : Cylinder.{u} n) :
    bottomVectorHomotopy n (s, z) =
      (1 - (s : ℝ)) • z.1.down.val +
        (s : ℝ) • (bottomIncludedRetraction n z).1.down.val := by
  exact AffineMap.lineMap_apply_module _ _ _

private def bottomHomotopyMap (n : ℕ) :
    C(unitInterval × Cylinder.{u} n, Cylinder.{u} n) where
  toFun p :=
    (ULift.up ⟨bottomVectorHomotopy n p, bottomVectorHomotopy_mem n p.1 p.2⟩,
      TopCat.I.homeomorph.symm
        (Set.Icc.convexComb (TopCat.I.homeomorph p.2.2)
          (TopCat.I.homeomorph (bottomIncludedRetraction n p.2).2) p.1))
  continuous_toFun := by
    have hvector : Continuous (fun p : unitInterval × Cylinder.{u} n =>
        bottomVectorHomotopy n p) := (bottomVectorHomotopy n).continuous
    have hheight : Continuous (fun p : unitInterval × Cylinder.{u} n =>
        Set.Icc.convexComb (TopCat.I.homeomorph p.2.2)
          (TopCat.I.homeomorph (bottomIncludedRetraction n p.2).2) p.1) := by
      exact Set.Icc.continuous_convexComb_prod.comp
        ((TopCat.I.homeomorph.continuous.comp
          (continuous_snd.comp continuous_snd)).prodMk
          ((TopCat.I.homeomorph.continuous.comp
            (continuous_snd.comp ((bottomIncludedRetraction n).continuous.comp
              continuous_snd))).prodMk continuous_fst))
    exact (continuous_uliftUp.comp (hvector.subtype_mk _)).prodMk
      (TopCat.I.homeomorph.symm.continuous.comp hheight)

private def bottomHomotopy (n : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (Cylinder.{u} n))
      (bottomIncludedRetraction n)
      (Set.range (classicalDiskCylinderBottomPair n).map) where
  toFun := bottomHomotopyMap n
  continuous_toFun := (bottomHomotopyMap n).continuous
  map_zero_left z := by
    apply Prod.ext
    · apply ULift.ext
      apply Subtype.ext
      exact (bottomVectorHomotopy n).apply_zero z
    · change TopCat.I.homeomorph.symm (Set.Icc.convexComb _ _ 0) = z.2
      simp
  map_one_left z := by
    apply Prod.ext
    · apply ULift.ext
      apply Subtype.ext
      exact (bottomVectorHomotopy n).apply_one z
    · change TopCat.I.homeomorph.symm (Set.Icc.convexComb _ _ 1) =
        (bottomIncludedRetraction n z).2
      simp
  prop' s z hz := by
    rcases hz with ⟨b, rfl⟩
    have hr := bottomIncludedRetraction_fixed n b
    apply Prod.ext
    · apply ULift.ext
      apply Subtype.ext
      change bottomVectorHomotopy n (s, (classicalDiskCylinderBottomPair n).map b) =
        ((classicalDiskCylinderBottomPair n).map b).1.down.val
      rw [bottomVectorHomotopy_apply, hr]
      rw [← add_smul, sub_add_cancel, one_smul]
    · change TopCat.I.homeomorph.symm
        (Set.Icc.convexComb _ (TopCat.I.homeomorph
          (bottomIncludedRetraction n ((classicalDiskCylinderBottomPair n).map b)).2) s) =
        ((classicalDiskCylinderBottomPair n).map b).2
      rw [hr]
      simp

private def topRetraction (n : ℕ) :
    C((classicalDiskCylinderTopPair.{u} n).fst,
      (classicalDiskCylinderTopPair.{u} n).snd) :=
  (⟨rimReflection n, (rimReflection n).continuous⟩ :
    C((classicalDiskCylinderBottomPair.{u} n).snd,
      (classicalDiskCylinderTopPair.{u} n).snd)).comp
    ((bottomRetraction n).comp
      ⟨classicalDiskCylinderReflection n, (classicalDiskCylinderReflection n).continuous⟩)

private theorem topRetraction_boundary (n : ℕ)
    (b : (classicalDiskCylinderTopPair.{u} n).snd) :
    topRetraction n ((classicalDiskCylinderTopPair n).map b) = b := by
  change rimReflection n
      (bottomRetraction n ((classicalDiskCylinderBottomPair n).map
        ((rimReflection n).symm b))) = b
  rw [bottomRetraction_boundary, Homeomorph.apply_symm_apply]

private def topIncludedRetraction (n : ℕ) : C(Cylinder.{u} n, Cylinder.{u} n) :=
  (classicalDiskCylinderTopPair n).map.hom.comp (topRetraction n)

private theorem topIncludedRetraction_reflection (n : ℕ) (z : Cylinder.{u} n) :
    topIncludedRetraction n z =
      classicalDiskCylinderReflection n
        (bottomIncludedRetraction n (classicalDiskCylinderReflection n z)) := rfl

private def topHomotopy (n : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (Cylinder.{u} n))
      (topIncludedRetraction n)
      (Set.range (classicalDiskCylinderTopPair n).map) where
  toFun p := classicalDiskCylinderReflection n
    (bottomHomotopy n (p.1, classicalDiskCylinderReflection n p.2))
  continuous_toFun :=
    (classicalDiskCylinderReflection n).continuous.comp
      ((bottomHomotopy n).continuous.comp
        (continuous_fst.prodMk
          ((classicalDiskCylinderReflection n).continuous.comp continuous_snd)))
  map_zero_left z := by
    rw [(bottomHomotopy n).apply_zero]
    exact reflection_involutive n z
  map_one_left z := by
    rw [(bottomHomotopy n).apply_one]
    exact (topIncludedRetraction_reflection n z).symm
  prop' s z hz := by
    rcases hz with ⟨b, rfl⟩
    have hfixed := (bottomHomotopy n).eq_fst s
      (Set.mem_range_self ((rimReflection n).symm b))
    change bottomHomotopy n (s, classicalDiskCylinderReflection n b.1) =
      classicalDiskCylinderReflection n b.1 at hfixed
    change classicalDiskCylinderReflection n
      (bottomHomotopy n (s, classicalDiskCylinderReflection n b.1)) = b.1
    rw [hfixed]
    exact reflection_involutive n b.1

/-- Both actual rim retractions and their ordinary stationary deformations. -/
structure ClassicalDiskCylinderCollapseData (n : ℕ) where
  /-- Retraction of the original cylinder onto the actual bottom-plus-side rim. -/
  bottomRetraction : C((classicalDiskCylinderBottomPair.{u} n).fst,
    (classicalDiskCylinderBottomPair.{u} n).snd)
  /-- The original bottom-rim inclusion followed by its retraction is the identity. -/
  bottom_inclusion_retraction (b : (classicalDiskCylinderBottomPair.{u} n).snd) :
    bottomRetraction ((classicalDiskCylinderBottomPair n).map b) = b
  /-- Ordinary deformation to the included bottom retraction, stationary on the whole rim. -/
  bottomHomotopy : ContinuousMap.HomotopyRel
    (ContinuousMap.id (classicalDiskCylinderBottomPair.{u} n).fst)
    ((classicalDiskCylinderBottomPair n).map.hom.comp bottomRetraction)
    (Set.range (classicalDiskCylinderBottomPair n).map)
  /-- Retraction of the original cylinder onto the actual top-plus-side rim. -/
  topRetraction : C((classicalDiskCylinderTopPair.{u} n).fst,
    (classicalDiskCylinderTopPair.{u} n).snd)
  /-- The original top-rim inclusion followed by its retraction is the identity. -/
  top_inclusion_retraction (b : (classicalDiskCylinderTopPair.{u} n).snd) :
    topRetraction ((classicalDiskCylinderTopPair n).map b) = b
  /-- Ordinary deformation to the included top retraction, stationary on the whole rim. -/
  topHomotopy : ContinuousMap.HomotopyRel
    (ContinuousMap.id (classicalDiskCylinderTopPair.{u} n).fst)
    ((classicalDiskCylinderTopPair n).map.hom.comp topRetraction)
    (Set.range (classicalDiskCylinderTopPair n).map)

/-- Construct both collapses from the actual disk-boundary NDR and spatial reflection. -/
def classicalDiskCylinderCollapseData (n : ℕ) : ClassicalDiskCylinderCollapseData.{u} n where
  bottomRetraction := bottomRetraction n
  bottom_inclusion_retraction := bottomRetraction_boundary n
  bottomHomotopy := bottomHomotopy n
  topRetraction := topRetraction n
  top_inclusion_retraction := topRetraction_boundary n
  topHomotopy := topHomotopy n

private theorem collapseData_bottomRetraction_impl (n : ℕ) :
    (classicalDiskCylinderCollapseData.{u} n).bottomRetraction =
      ((classicalCellDiskPairNDRData.{u} n).toStandard.cylinderRetraction).hom := rfl

/-- The bottom retraction is the existing constructed disk-boundary NDR retraction. -/
theorem classicalDiskCylinderCollapseData_bottomRetraction (n : ℕ) :
    (classicalDiskCylinderCollapseData.{u} n).bottomRetraction =
      ((classicalCellDiskPairNDRData.{u} n).toStandard.cylinderRetraction).hom :=
  collapseData_bottomRetraction_impl n

/-- Both coordinates of the ordinary bottom deformation are the original affine combinations. -/
theorem classicalDiskCylinderCollapseData_bottomHomotopy_coordinates (n : ℕ)
    (s : unitInterval) (z : (classicalDiskCylinderBottomPair.{u} n).fst) :
    let r := ((classicalDiskCylinderCollapseData.{u} n).bottomRetraction z).1
    ((classicalDiskCylinderCollapseData n).bottomHomotopy (s, z)).1.down.val =
        (1 - (s : ℝ)) • z.1.down.val + (s : ℝ) • r.1.down.val ∧
      TopCat.I.homeomorph
          ((classicalDiskCylinderCollapseData n).bottomHomotopy (s, z)).2 =
        Set.Icc.convexComb (TopCat.I.homeomorph z.2) (TopCat.I.homeomorph r.2) s := by
  refine ⟨bottomVectorHomotopy_apply n s z, ?_⟩
  exact TopCat.I.homeomorph.apply_symm_apply _

private theorem collapseData_topRetraction_impl (n : ℕ)
    (z : (classicalDiskCylinderTopPair.{u} n).fst) :
    ((classicalDiskCylinderCollapseData n).topRetraction z).1 =
      classicalDiskCylinderReflection n
        (((classicalDiskCylinderCollapseData n).bottomRetraction
          (classicalDiskCylinderReflection n z)).1) := rfl

/-- The top retraction is the spatial conjugate of the actual bottom retraction. -/
theorem classicalDiskCylinderCollapseData_topRetraction_reflection (n : ℕ)
    (z : (classicalDiskCylinderTopPair.{u} n).fst) :
    ((classicalDiskCylinderCollapseData n).topRetraction z).1 =
      classicalDiskCylinderReflection n
        (((classicalDiskCylinderCollapseData n).bottomRetraction
          (classicalDiskCylinderReflection n z)).1) :=
  collapseData_topRetraction_impl n z

private theorem collapseData_topHomotopy_impl (n : ℕ)
    (s : unitInterval) (z : (classicalDiskCylinderTopPair.{u} n).fst) :
    (classicalDiskCylinderCollapseData n).topHomotopy (s, z) =
      classicalDiskCylinderReflection n
        ((classicalDiskCylinderCollapseData n).bottomHomotopy
          (s, classicalDiskCylinderReflection n z)) := rfl

/-- Spatial conjugation constructs the top homotopy at the same deformation time. -/
theorem classicalDiskCylinderCollapseData_topHomotopy_reflection (n : ℕ)
    (s : unitInterval) (z : (classicalDiskCylinderTopPair.{u} n).fst) :
    (classicalDiskCylinderCollapseData n).topHomotopy (s, z) =
      classicalDiskCylinderReflection n
        ((classicalDiskCylinderCollapseData n).bottomHomotopy
          (s, classicalDiskCylinderReflection n z)) :=
  collapseData_topHomotopy_impl n s z

private theorem zero_disk_eq (x y : (classicalCellDiskPair.{u} 0).fst) : x = y := by
  apply ULift.ext
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

private theorem zero_bottomRetraction (x : (classicalCellDiskPair.{u} 0).fst)
    (t : TopCat.I.{u}) :
    ((classicalDiskCylinderCollapseData 0).bottomRetraction (x, t)).1 = (x, 0) := by
  let r := (classicalDiskCylinderCollapseData 0).bottomRetraction (x, t)
  have hr := Set.mem_unionProd.mp r.2
  rcases hr with hs | ht
  · rcases hs with ⟨a, ha⟩
    exact isEmptyElim a
  · exact Prod.ext (zero_disk_eq _ _) ht

private theorem zero_topRetraction (x : (classicalCellDiskPair.{u} 0).fst)
    (t : TopCat.I.{u}) :
    ((classicalDiskCylinderCollapseData 0).topRetraction (x, t)).1 = (x, 1) := by
  rw [classicalDiskCylinderCollapseData_topRetraction_reflection]
  simp only [reflection_apply, zero_bottomRetraction, TopCat.I.symm_zero]

private theorem zero_bottomHeight (s : unitInterval)
    (x : (classicalCellDiskPair.{u} 0).fst) (t : TopCat.I.{u}) :
    (TopCat.I.homeomorph
        ((classicalDiskCylinderCollapseData 0).bottomHomotopy (s, (x, t))).2 : ℝ) =
      (1 - (s : ℝ)) * (TopCat.I.homeomorph t : ℝ) := by
  have hr : bottomIncludedRetraction.{u} 0 (x, t) = (x, 0) :=
    zero_bottomRetraction x t
  change (Set.Icc.convexComb (TopCat.I.homeomorph t)
    (TopCat.I.homeomorph (bottomIncludedRetraction 0 (x, t)).2) s : ℝ) = _
  rw [hr, TopCat.I.homeomorph_zero]
  simp only [Set.Icc.coe_convexComb]
  change (1 - (s : ℝ)) * (TopCat.I.homeomorph t : ℝ) + (s : ℝ) * (0 : ℝ) = _
  rw [mul_zero, add_zero]

private theorem zero_topHeight (s : unitInterval)
    (x : (classicalCellDiskPair.{u} 0).fst) (t : TopCat.I.{u}) :
    (TopCat.I.homeomorph
        ((classicalDiskCylinderCollapseData 0).topHomotopy (s, (x, t))).2 : ℝ) =
      (1 - (s : ℝ)) * (TopCat.I.homeomorph t : ℝ) + (s : ℝ) := by
  rw [classicalDiskCylinderCollapseData_topHomotopy_reflection, reflection_apply]
  rw [TopCat.I.homeomorph_symm]
  change 1 - (TopCat.I.homeomorph
    ((classicalDiskCylinderCollapseData 0).bottomHomotopy
      (s, (x, TopCat.I.symm t))).2 : ℝ) = _
  rw [zero_bottomHeight, TopCat.I.homeomorph_symm]
  change 1 - (1 - (s : ℝ)) * (1 - (TopCat.I.homeomorph t : ℝ)) = _
  ring

/-- The zero sphere is empty, its disk remains a point, and both collapses have literal heights. -/
theorem classicalDiskCylinder_zero_geometry :
    IsEmpty (classicalCellDiskPair.{u} 0).snd ∧
      Nonempty (classicalCellDiskPair.{u} 0).fst ∧
      ∀ (x : (classicalCellDiskPair.{u} 0).fst) (t : TopCat.I.{u}) (s : unitInterval),
        ((classicalDiskCylinderCollapseData 0).bottomRetraction (x, t)).1 = (x, 0) ∧
        ((classicalDiskCylinderCollapseData 0).topRetraction (x, t)).1 = (x, 1) ∧
        ((classicalDiskCylinderCollapseData 0).bottomHomotopy (s, (x, t))).1 = x ∧
        ((classicalDiskCylinderCollapseData 0).topHomotopy (s, (x, t))).1 = x ∧
        (TopCat.I.homeomorph
            ((classicalDiskCylinderCollapseData 0).bottomHomotopy (s, (x, t))).2 : ℝ) =
          (1 - (s : ℝ)) * (TopCat.I.homeomorph t : ℝ) ∧
        (TopCat.I.homeomorph
            ((classicalDiskCylinderCollapseData 0).topHomotopy (s, (x, t))).2 : ℝ) =
          (1 - (s : ℝ)) * (TopCat.I.homeomorph t : ℝ) + (s : ℝ) := by
  refine ⟨inferInstance, ⟨ULift.up ⟨0, by simp⟩⟩, ?_⟩
  intro x t s
  exact ⟨zero_bottomRetraction x t, zero_topRetraction x t,
    zero_disk_eq _ _, zero_disk_eq _ _, zero_bottomHeight s x t, zero_topHeight s x t⟩

/-- Public coordinates of the spatial reflection in the original disk cylinder. -/
@[simp]
theorem classicalDiskCylinderReflection_apply (n : ℕ)
    (z : (classicalDiskCylinderBottomPair.{u} n).fst) :
    classicalDiskCylinderReflection n z = (z.1, TopCat.I.symm z.2) :=
  reflection_apply n z

/-- Reflecting the spatial interval twice fixes every original cylinder point. -/
theorem classicalDiskCylinderReflection_apply_apply (n : ℕ)
    (z : (classicalDiskCylinderBottomPair.{u} n).fst) :
    classicalDiskCylinderReflection n (classicalDiskCylinderReflection n z) = z :=
  reflection_involutive n z

end Topology.CWComplex

end
