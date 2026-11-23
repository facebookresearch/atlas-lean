/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CWComplex.DiskCylinder

/-!
# Ordinary clients for both classical disk-cylinder collapses

Whole-rim points stay fixed at arbitrary deformation times. The concrete
side and zero-dimensional clients distinguish deformation time from spatial
height and use only the public canonical data and coordinate laws.
-/

open CategoryTheory Topology Topology.CWComplex
open scoped unitInterval

noncomputable section

universe u

example (n : ℕ) (b : (classicalDiskCylinderBottomPair.{u} n).snd) :
    (classicalDiskCylinderCollapseData n).bottomRetraction
      ((classicalDiskCylinderBottomPair n).map b) = b :=
  (classicalDiskCylinderCollapseData n).bottom_inclusion_retraction b

example (n : ℕ) (b : (classicalDiskCylinderTopPair.{u} n).snd) :
    (classicalDiskCylinderCollapseData n).topRetraction
      ((classicalDiskCylinderTopPair n).map b) = b :=
  (classicalDiskCylinderCollapseData n).top_inclusion_retraction b

example (n : ℕ) (s : unitInterval)
    (b : (classicalDiskCylinderBottomPair.{u} n).snd) :
    (classicalDiskCylinderCollapseData n).bottomHomotopy
      (s, (classicalDiskCylinderBottomPair n).map b) =
        (classicalDiskCylinderBottomPair n).map b :=
  (classicalDiskCylinderCollapseData n).bottomHomotopy.eq_fst s (Set.mem_range_self b)

example (n : ℕ) (s : unitInterval)
    (b : (classicalDiskCylinderTopPair.{u} n).snd) :
    (classicalDiskCylinderCollapseData n).topHomotopy
      (s, (classicalDiskCylinderTopPair n).map b) =
        (classicalDiskCylinderTopPair n).map b :=
  (classicalDiskCylinderCollapseData n).topHomotopy.eq_fst s (Set.mem_range_self b)

example (s : unitInterval) (x : (classicalCellDiskPair.{u} 0).fst) (t : TopCat.I.{u}) :
    (TopCat.I.homeomorph
        ((classicalDiskCylinderCollapseData 0).topHomotopy (s, (x, t))).2 : ℝ) =
      (1 - (s : ℝ)) * (TopCat.I.homeomorph t : ℝ) + (s : ℝ) :=
  (classicalDiskCylinder_zero_geometry.2.2 x t s).2.2.2.2.2

example (n : ℕ) (a : (classicalCellDiskPair.{u} n).snd) :
    (classicalDiskCylinderCollapseData n).bottomHomotopy
      (⟨(1 : ℝ) / 2, by norm_num⟩,
        ((classicalCellDiskPair n).map a,
          TopCat.I.homeomorph.symm ⟨(1 : ℝ) / 3, by norm_num⟩)) =
      ((classicalCellDiskPair n).map a,
        TopCat.I.homeomorph.symm ⟨(1 : ℝ) / 3, by norm_num⟩) := by
  let b := TopPair.hurewiczCylinderSidePoint (classicalCellDiskPair.{u} n)
    (TopCat.I.homeomorph.symm ⟨(1 : ℝ) / 3, by norm_num⟩) a
  exact (classicalDiskCylinderCollapseData n).bottomHomotopy.eq_fst
    ⟨(1 : ℝ) / 2, by norm_num⟩ (Set.mem_range_self b)

example (n : ℕ) (a : (classicalCellDiskPair.{u} n).snd) :
    (classicalDiskCylinderCollapseData n).topHomotopy
      (⟨(1 : ℝ) / 2, by norm_num⟩,
        ((classicalCellDiskPair n).map a,
          TopCat.I.homeomorph.symm ⟨(1 : ℝ) / 3, by norm_num⟩)) =
      ((classicalCellDiskPair n).map a,
        TopCat.I.homeomorph.symm ⟨(1 : ℝ) / 3, by norm_num⟩) := by
  let b : (classicalDiskCylinderTopPair.{u} n).snd :=
    ⟨((classicalCellDiskPair n).map a,
      TopCat.I.homeomorph.symm ⟨(1 : ℝ) / 3, by norm_num⟩),
      Set.mem_unionProd.mpr (Or.inl ⟨a, rfl⟩)⟩
  exact (classicalDiskCylinderCollapseData n).topHomotopy.eq_fst
    ⟨(1 : ℝ) / 2, by norm_num⟩ (Set.mem_range_self b)

example : IsEmpty (classicalCellDiskPair.{u} 0).snd :=
  classicalDiskCylinder_zero_geometry.1

example : Nonempty (classicalCellDiskPair.{u} 0).fst :=
  classicalDiskCylinder_zero_geometry.2.1

example (x : (classicalCellDiskPair.{u} 0).fst) :
    (TopCat.I.homeomorph
      ((classicalDiskCylinderCollapseData 0).bottomHomotopy
        (⟨(1 : ℝ) / 4, by norm_num⟩,
          (x, TopCat.I.homeomorph.symm ⟨(1 : ℝ) / 3, by norm_num⟩))).2 : ℝ) =
        (1 : ℝ) / 4 := by
  have h := (classicalDiskCylinder_zero_geometry.2.2 x
    (TopCat.I.homeomorph.symm ⟨(1 : ℝ) / 3, by norm_num⟩)
    ⟨(1 : ℝ) / 4, by norm_num⟩).2.2.2.2.1
  norm_num at h ⊢
  exact h

example (x : (classicalCellDiskPair.{u} 0).fst) :
    (TopCat.I.homeomorph
      ((classicalDiskCylinderCollapseData 0).topHomotopy
        (⟨(1 : ℝ) / 4, by norm_num⟩,
          (x, TopCat.I.homeomorph.symm ⟨(1 : ℝ) / 3, by norm_num⟩))).2 : ℝ) =
        (1 : ℝ) / 2 := by
  have h := (classicalDiskCylinder_zero_geometry.2.2 x
    (TopCat.I.homeomorph.symm ⟨(1 : ℝ) / 3, by norm_num⟩)
    ⟨(1 : ℝ) / 4, by norm_num⟩).2.2.2.2.2
  norm_num at h ⊢
  exact h

example (n : ℕ) (s : unitInterval)
    (z : (classicalDiskCylinderTopPair.{u} n).fst) :
    (classicalDiskCylinderCollapseData n).topHomotopy (s, z) =
      classicalDiskCylinderReflection n
        ((classicalDiskCylinderCollapseData n).bottomHomotopy
          (s, classicalDiskCylinderReflection n z)) :=
  classicalDiskCylinderCollapseData_topHomotopy_reflection n s z

example (n : ℕ) (x : (classicalCellDiskPair.{u} n).fst) (t : TopCat.I.{u}) :
    classicalDiskCylinderReflection n (x, t) = (x, TopCat.I.symm t) := by
  rw [classicalDiskCylinderReflection_apply n (x, t)]

example (n : ℕ) (z : (classicalDiskCylinderBottomPair.{u} n).fst) :
    classicalDiskCylinderReflection n (classicalDiskCylinderReflection n z) = z :=
  classicalDiskCylinderReflection_apply_apply n z

example (n : ℕ) (z : (classicalDiskCylinderBottomPair.{u} n).fst) :
    (TopCat.I.homeomorph (classicalDiskCylinderReflection n z).2 : ℝ) =
      1 - (TopCat.I.homeomorph z.2 : ℝ) := by
  rw [classicalDiskCylinderReflection_apply n z, TopCat.I.homeomorph_symm]
  rfl

end
