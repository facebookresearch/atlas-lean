/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CWComplex.DiskCone

/-!
# Ordinary classical disk/cone clients

The actual lifted boundary and zero point are preserved. The half-time
radial coordinate recovers a boundary vector after multiplication by two,
and an empty zero-dimensional sphere still has its cone point.
-/

open CategoryTheory Limits MonoidalCategory Topology Topology.CWComplex

noncomputable section

universe u

example (n : ℕ) :
    (classicalCellDiskPair.{u} n).fst ≃ₜ TopCat.cone (classicalCellDiskPair.{u} n).snd :=
  classicalDiskConeHomeomorph n

example (n : ℕ) (x : (classicalCellDiskPair.{u} n).snd) :
    (classicalDiskConeHomeomorph.{u} n).symm
      (TopCat.coneBase (classicalCellDiskPair.{u} n).snd x) =
        (classicalCellDiskPair.{u} n).map x := by
  rw [← classicalDiskConeHomeomorph_boundary]
  exact (classicalDiskConeHomeomorph n).symm_apply_apply _

example (n : ℕ) :
    (classicalDiskConeHomeomorph.{u} n).symm
      (TopCat.conePoint (classicalCellDiskPair.{u} n).snd PUnit.unit) =
        (ULift.up ⟨(0 : Fin n → ℝ), by simp⟩ : (classicalCellDiskPair.{u} n).fst) := by
  rw [← classicalDiskConeHomeomorph_zero]
  exact (classicalDiskConeHomeomorph n).symm_apply_apply _

example (n : ℕ) (x : (classicalCellDiskPair.{u} n).snd) :
    (2 : ℝ) • ((classicalDiskConeHomeomorph.{u} n).symm
      (TopCat.coneCylinder (classicalCellDiskPair.{u} n).snd
        (x, TopCat.I.homeomorph.symm ⟨(1 : ℝ) / 2, by norm_num⟩))).down.val =
      x.down.val := by
  rw [classicalDiskConeHomeomorph_symm_coneCylinder]
  norm_num [smul_smul]

example : IsEmpty (classicalCellDiskPair.{u} 0).snd :=
  classicalDiskCone_zero_geometry.1

example (z : TopCat.cone (classicalCellDiskPair.{u} 0).snd) :
    z = TopCat.conePoint (classicalCellDiskPair.{u} 0).snd PUnit.unit :=
  classicalDiskCone_zero_geometry.2 z

example (x : (classicalCellDiskPair.{u} 0).fst) :
    classicalDiskConeHomeomorph.{u} 0 x =
      TopCat.conePoint (classicalCellDiskPair.{u} 0).snd PUnit.unit :=
  classicalDiskCone_zero_geometry.2 _

end
