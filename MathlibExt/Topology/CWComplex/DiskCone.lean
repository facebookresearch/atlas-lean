/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.ConeSphere
public import MathlibExt.Topology.Category.TopPair.ClosedBall.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The actual lifted classical disk as its boundary sphere cone

The standard radial sphere-cone homeomorphism is applied to the canonically
normed lift of the classical coordinate space. The subtype/lift conversions
retain the actual disk pair, its boundary inclusion, and the zero point.
-/

public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits MonoidalCategory Topology

universe u

namespace Topology.CWComplex

private theorem liftedCoordinateSpace_proper (n : ℕ) :
    ProperSpace (ULift.{u} (Fin n → ℝ)) := by
  have hi : Isometry (ULift.up : (Fin n → ℝ) → ULift.{u} (Fin n → ℝ)) :=
    fun x y => rfl
  exact hi.antilipschitzWith.properSpace continuous_uliftUp
    (fun x => ⟨x.down, by cases x; rfl⟩)

private def sphereLiftHomeomorph (n : ℕ) :
    (classicalCellDiskPair.{u} n).snd ≃ₜ
      Metric.sphere (0 : ULift.{u} (Fin n → ℝ)) 1 where
  toFun x := ⟨ULift.up x.down.val, by exact x.down.property⟩
  invFun x := ULift.up ⟨x.val.down, by exact x.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  continuous_toFun :=
    (continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _
  continuous_invFun := continuous_uliftUp.comp
    ((continuous_uliftDown.comp continuous_subtype_val).subtype_mk _)

private def ballLiftHomeomorph (n : ℕ) :
    Metric.closedBall (0 : ULift.{u} (Fin n → ℝ)) 1 ≃ₜ
      (classicalCellDiskPair.{u} n).fst where
  toFun x := ULift.up ⟨x.val.down, by
    change dist x.val.down (0 : Fin n → ℝ) ≤ 1
    exact x.property⟩
  invFun x := ⟨ULift.up x.down.val, by
    change dist (ULift.up x.down.val : ULift.{u} (Fin n → ℝ)) 0 ≤ 1
    exact x.down.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  continuous_toFun := continuous_uliftUp.comp
    ((continuous_uliftDown.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    (continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _

private def sphereLiftIso (n : ℕ) :
    (classicalCellDiskPair.{u} n).snd ≅
      TopCat.of (Metric.sphere (0 : ULift.{u} (Fin n → ℝ)) 1) :=
  TopCat.isoOfHomeo (sphereLiftHomeomorph n)

private def ballLiftIso (n : ℕ) :
    TopCat.of (Metric.closedBall (0 : ULift.{u} (Fin n → ℝ)) 1) ≅
      (classicalCellDiskPair.{u} n).fst :=
  TopCat.isoOfHomeo (ballLiftHomeomorph n)

private def radialIso (n : ℕ) :
    TopCat.cone (TopCat.of (Metric.sphere (0 : ULift.{u} (Fin n → ℝ)) 1)) ≅
      TopCat.of (Metric.closedBall (0 : ULift.{u} (Fin n → ℝ)) 1) := by
  letI := liftedCoordinateSpace_proper.{u} n
  exact TopCat.isoOfHomeo (TopCat.unitSphereConeHomeomorph (ULift.{u} (Fin n → ℝ)))

private theorem radialIso_hom (n : ℕ) :
    (radialIso.{u} n).hom = TopCat.unitSphereConeMap (ULift.{u} (Fin n → ℝ)) := by
  let := liftedCoordinateSpace_proper.{u} n
  exact TopCat.isoOfHomeo_unitSphereConeHomeomorph_hom _


private def coneLiftIso (n : ℕ) :
    TopCat.cone (classicalCellDiskPair.{u} n).snd ≅
      TopCat.cone (TopCat.of (Metric.sphere (0 : ULift.{u} (Fin n → ℝ)) 1)) :=
  TopCat.coneFunctor.mapIso (sphereLiftIso.{u} n)

private theorem coneLiftIso_hom (n : ℕ) :
    (coneLiftIso.{u} n).hom = TopCat.coneMap (sphereLiftIso.{u} n).hom := rfl

private def coneToDiskIso (n : ℕ) :
    TopCat.cone (classicalCellDiskPair.{u} n).snd ≅ (classicalCellDiskPair.{u} n).fst :=
  (coneLiftIso.{u} n).trans
    ((radialIso.{u} n).trans (ballLiftIso.{u} n))

private theorem coneToDisk_base (n : ℕ) :
    TopCat.coneBase (classicalCellDiskPair.{u} n).snd ≫ (coneToDiskIso.{u} n).hom =
      (classicalCellDiskPair.{u} n).map := by
  simp only [coneToDiskIso, Iso.trans_hom, coneLiftIso_hom, radialIso_hom]
  rw [← Category.assoc, TopCat.coneBase_naturality]
  simp only [Category.assoc, TopCat.coneBase_unitSphereConeMap_assoc]
  apply ConcreteCategory.hom_ext
  intro x
  rfl

private theorem coneToDisk_point (n : ℕ) :
    TopCat.conePoint (classicalCellDiskPair.{u} n).snd ≫ (coneToDiskIso.{u} n).hom =
      TopCat.ofHom (ContinuousMap.const _
        (ULift.up ⟨(0 : Fin n → ℝ), by simp⟩ : (classicalCellDiskPair.{u} n).fst)) := by
  simp only [coneToDiskIso, Iso.trans_hom, coneLiftIso_hom, radialIso_hom]
  rw [← Category.assoc, TopCat.conePoint_naturality,
    TopCat.conePoint_unitSphereConeMap_assoc]
  apply ConcreteCategory.hom_ext
  intro x
  cases x
  rfl

private theorem coneToDisk_cylinder (n : ℕ) :
    TopCat.coneCylinder (classicalCellDiskPair.{u} n).snd ≫ (coneToDiskIso.{u} n).hom =
      ((sphereLiftIso.{u} n).hom ▷ TopCat.I) ≫
        TopCat.unitSphereConeCylinderMap (ULift.{u} (Fin n → ℝ)) ≫
          (ballLiftIso.{u} n).hom := by
  simp only [coneToDiskIso, Iso.trans_hom, coneLiftIso_hom, radialIso_hom]
  rw [← Category.assoc, TopCat.coneCylinder_naturality]
  simp only [Category.assoc, TopCat.coneCylinder_unitSphereConeMap_assoc]

/-- The actual lifted classical disk is the ordinary cone on its exact boundary sphere. -/
def classicalDiskConeHomeomorph (n : ℕ) :
    (classicalCellDiskPair.{u} n).fst ≃ₜ TopCat.cone (classicalCellDiskPair.{u} n).snd :=
  (TopCat.homeoOfIso (coneToDiskIso.{u} n)).symm

private theorem boundary_impl (n : ℕ) (x : (classicalCellDiskPair.{u} n).snd) :
    classicalDiskConeHomeomorph.{u} n ((classicalCellDiskPair.{u} n).map x) =
      TopCat.coneBase (classicalCellDiskPair.{u} n).snd x := by
  apply (TopCat.homeoOfIso (coneToDiskIso.{u} n)).injective
  change (TopCat.homeoOfIso (coneToDiskIso.{u} n))
      ((TopCat.homeoOfIso (coneToDiskIso.{u} n)).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  exact (ConcreteCategory.congr_hom (coneToDisk_base.{u} n) x).symm

/-- The cone base is the actual classical boundary inclusion under the dictionary. -/
theorem classicalDiskConeHomeomorph_boundary (n : ℕ)
    (x : (classicalCellDiskPair.{u} n).snd) :
    classicalDiskConeHomeomorph.{u} n ((classicalCellDiskPair.{u} n).map x) =
      TopCat.coneBase (classicalCellDiskPair.{u} n).snd x :=
  boundary_impl n x

private theorem zero_impl (n : ℕ) :
    classicalDiskConeHomeomorph.{u} n
      (ULift.up ⟨(0 : Fin n → ℝ), by simp⟩ : (classicalCellDiskPair.{u} n).fst) =
        TopCat.conePoint (classicalCellDiskPair.{u} n).snd PUnit.unit := by
  apply (TopCat.homeoOfIso (coneToDiskIso.{u} n)).injective
  change (TopCat.homeoOfIso (coneToDiskIso.{u} n))
      ((TopCat.homeoOfIso (coneToDiskIso.{u} n)).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  exact (ConcreteCategory.congr_hom (coneToDisk_point.{u} n) PUnit.unit).symm

/-- The actual zero of the lifted disk is the retained cone apex in every dimension. -/
theorem classicalDiskConeHomeomorph_zero (n : ℕ) :
    classicalDiskConeHomeomorph.{u} n
      (ULift.up ⟨(0 : Fin n → ℝ), by simp⟩ : (classicalCellDiskPair.{u} n).fst) =
        TopCat.conePoint (classicalCellDiskPair.{u} n).snd PUnit.unit :=
  zero_impl n

private theorem radial_impl (n : ℕ) (x : (classicalCellDiskPair.{u} n).snd)
    (t : TopCat.I.{u}) :
    ((classicalDiskConeHomeomorph.{u} n).symm
      (TopCat.coneCylinder (classicalCellDiskPair.{u} n).snd (x, t))).down.val =
        (1 - (TopCat.I.homeomorph t).val) • x.down.val := by
  have h := ConcreteCategory.congr_hom (coneToDisk_cylinder.{u} n) (x, t)
  exact congrArg (fun z : (classicalCellDiskPair.{u} n).fst => z.down.val) h

/-- The inverse dictionary retains the original radial coordinate formula on the cylinder. -/
theorem classicalDiskConeHomeomorph_symm_coneCylinder (n : ℕ)
    (x : (classicalCellDiskPair.{u} n).snd) (t : TopCat.I.{u}) :
    ((classicalDiskConeHomeomorph.{u} n).symm
      (TopCat.coneCylinder (classicalCellDiskPair.{u} n).snd (x, t))).down.val =
        (1 - (TopCat.I.homeomorph t).val) • x.down.val :=
  radial_impl n x t

/-- The zero-dimensional sphere is empty and every point of its cone is its retained apex. -/
theorem classicalDiskCone_zero_geometry :
    IsEmpty (classicalCellDiskPair.{u} 0).snd ∧
      ∀ z : TopCat.cone (classicalCellDiskPair.{u} 0).snd,
        z = TopCat.conePoint (classicalCellDiskPair.{u} 0).snd PUnit.unit :=
  ⟨inferInstance, TopCat.cone_eq_conePoint_of_isEmpty _⟩

end Topology.CWComplex

end
