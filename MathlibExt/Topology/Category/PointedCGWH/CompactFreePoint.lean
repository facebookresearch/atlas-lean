/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.OnePoint

/-!
# Naturality of the original compact free-point comparison

The complete inherited functions and topology are retained.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Filter
open TopologicalSpace Topology

namespace PointedCGWH

/-- The original compact free-point comparison is natural for every actual proper continuous map. -/
theorem compactFreePointIso_naturality {X Y : CGWH.{u, v}}
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    (f : X ⟶ Y) (hf : Tendsto f (coclosedCompact X) (coclosedCompact Y)) :
    (Under.costar CGWH.point.{u, v}).map f ≫
        (PointedCGWH.addBasepointIsoOnePointOfCompact Y).hom =
      (PointedCGWH.addBasepointIsoOnePointOfCompact X).hom ≫
        PointedCGWH.onePointMapOfProper.{u, v}
          (ConcreteCategory.hom (C := CGWH.{u, v}) f) hf := by
  let A := (Under.costar CGWH.point.{u, v}).obj X
  let B := PointedCGWH.onePointOf.{u, v} (Y : Type v)
  let L : A ⟶ B := (Under.costar CGWH.point.{u, v}).map f ≫
    (PointedCGWH.addBasepointIsoOnePointOfCompact Y).hom
  let R : A ⟶ B := (PointedCGWH.addBasepointIsoOnePointOfCompact X).hom ≫
    PointedCGWH.onePointMapOfProper.{u, v}
      (ConcreteCategory.hom (C := CGWH.{u, v}) f) hf
  have hp : A.hom = (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ X) :=
    (Under.costar_obj_hom CGWH.point X).trans (coprod.inl_desc _ _)
  change L = R
  apply Under.UnderMorphism.ext
  apply coprod.hom_ext
  · have hL := Under.w L
    have hR := Under.w R
    rw [hp] at hL hR
    exact hL.trans hR.symm
  · apply ConcreteCategory.hom_ext
    intro x
    change L.right ((coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) x) =
      R.right ((coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) x)
    have hmap0 := ConcreteCategory.congr_hom (coprod.inr_map (𝟙 CGWH.point.{u, v}) f) x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hmap0
    have hmap : ((Under.costar CGWH.point.{u, v}).map f).right
        ((coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) x) =
      (coprod.inr : Y ⟶ CGWH.point.{u, v} ⨿ Y) (f x) := by
      change (coprod.map (𝟙 CGWH.point.{u, v}) f)
        ((coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) x) = _
      exact hmap0
    have hL : L.right ((coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) x) =
        (f x : OnePoint (Y : Type v)) :=
      (congrArg (fun y : ((Under.costar CGWH.point.{u, v}).obj Y).right =>
        (PointedCGWH.addBasepointIsoOnePointOfCompact Y).hom.right y) hmap).trans
          (compactFreePointIso_coe Y (f x))
    have hR : R.right ((coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) x) =
        (f x : OnePoint (Y : Type v)) :=
      (congrArg (fun z : OnePoint (X : Type v) =>
        (PointedCGWH.onePointMapOfProper.{u, v}
          (ConcreteCategory.hom (C := CGWH.{u, v}) f) hf).right z)
        (compactFreePointIso_coe X x)).trans
          (PointedCGWH.onePointMapOfProper_coe.{u, v}
            (ConcreteCategory.hom (C := CGWH.{u, v}) f) hf x)
    exact hL.trans hR.symm

/-- The complete original free-point arrow agrees with the proper compactification arrow. -/
def compactFreePointMapArrowIso {X Y : CGWH.{u, v}}
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    (f : X ⟶ Y) (hf : Tendsto f (coclosedCompact X) (coclosedCompact Y)) :
    Arrow.mk ((Under.costar CGWH.point.{u, v}).map f) ≅
      Arrow.mk (PointedCGWH.onePointMapOfProper.{u, v}
        (ConcreteCategory.hom (C := CGWH.{u, v}) f) hf) :=
  Arrow.isoMk (PointedCGWH.addBasepointIsoOnePointOfCompact X)
    (PointedCGWH.addBasepointIsoOnePointOfCompact Y)
    (compactFreePointIso_naturality f hf).symm

end PointedCGWH
