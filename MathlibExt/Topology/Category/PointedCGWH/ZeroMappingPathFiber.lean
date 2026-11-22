/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.CGWH.PathHomotopyFiber
import MathlibExt.Topology.Category.CGWH.PathLanding
import MathlibExt.Topology.Homotopy.StrictLoopMap

/-!
# The zero mapping-path fiber of a pointed CGWH space

A pointed CGWH space determines the based arrow from the point object to its
underlying space.  This file packages the corresponding mapping-path fiber as
a pointed functor and lands its native path coordinate in the ordinary
compact-open loop space.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology

namespace PointedCGWH

/-- Regard a pointed CGWH space as the based arrow whose total object is the
point and whose map and selected basepoint are its structure map. -/
noncomputable abbrev zeroBasedArrow :
    PointedCGWH.{u, v} ⥤ CGWH.BasedArrow.{u, v} where
  obj X := CGWH.BasedArrow.mk X.hom X.hom
  map {X Y} f := CGWH.BasedArrow.homMk
    (𝟙 CGWH.point.{u, v}) f.right
    (by
      change 𝟙 CGWH.point.{u, v} ≫ Y.hom = X.hom ≫ f.right
      rw [Category.id_comp]
      exact (Under.w f).symm)
    (by
      change X.hom ≫ f.right = Y.hom
      exact Under.w f)
  map_id X := by
    apply StructuredArrow.hom_ext
    apply Arrow.hom_ext
    · rfl
    · rfl
  map_comp {X Y Z} f g := by
    apply StructuredArrow.hom_ext
    apply Arrow.hom_ext
    · rfl
    · rfl

/-- The underlying CGWH-valued zero mapping-path-fiber functor. -/
noncomputable abbrev zeroMappingPathFiberRight :
    PointedCGWH.{u, v} ⥤ CGWH.{u, v} :=
  zeroBasedArrow.{u, v} ⋙ CGWH.mappingPathFiber.{u, v}

private noncomputable abbrev zeroStrictFiberPoint :
    (Functor.const PointedCGWH.{u, v}).obj CGWH.point.{u, v} ⟶
      zeroBasedArrow.{u, v} ⋙ CGWH.strictFiberFunctor.{u, v} where
  app X :=
    CGWH.strictFiberPoint X.hom X.hom (𝟙 CGWH.point.{u, v}) (by simp)
  naturality X Y f := by
    change
      (𝟙 CGWH.point.{u, v}) ≫
          CGWH.strictFiberPoint Y.hom Y.hom
            (𝟙 CGWH.point.{u, v}) _ =
        CGWH.strictFiberPoint X.hom X.hom
            (𝟙 CGWH.point.{u, v}) _ ≫
          CGWH.strictFiberMap (𝟙 CGWH.point.{u, v}) f.right
            (by
              rw [Category.id_comp]
              exact (Under.w f).symm)
            (Under.w f)
    rw [Category.id_comp]
    exact (CGWH.strictFiberPoint_naturality
      (𝟙 CGWH.point.{u, v}) f.right
      (by
        rw [Category.id_comp]
        exact (Under.w f).symm)
      (Under.w f)
      (𝟙 CGWH.point.{u, v}) (by simp)
      (𝟙 CGWH.point.{u, v}) (by simp) (by simp)).symm

/-- The identity lift of the selected point, followed by constant-path
inclusion, gives the canonical point of the zero mapping-path fiber. -/
noncomputable abbrev zeroMappingPathFiberPoint :
    (Functor.const PointedCGWH.{u, v}).obj CGWH.point.{u, v} ⟶
      zeroMappingPathFiberRight.{u, v} :=
  zeroStrictFiberPoint.{u, v} ≫
    Functor.whiskerLeft zeroBasedArrow.{u, v}
      CGWH.strictFiberToMappingPathFiber.{u, v}

/-- The pointed zero mapping-path-fiber functor. -/
noncomputable abbrev zeroMappingPathFiber :
    PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} where
  obj X := Under.mk (zeroMappingPathFiberPoint.app X)
  map {X Y} f := Under.homMk (zeroMappingPathFiberRight.map f) (by
    change zeroMappingPathFiberPoint.app X ≫
        zeroMappingPathFiberRight.map f = zeroMappingPathFiberPoint.app Y
    simpa using (zeroMappingPathFiberPoint.naturality f).symm)
  map_id X := by
    apply Under.UnderMorphism.ext
    exact zeroMappingPathFiberRight.map_id X
  map_comp {X Y Z} f g := by
    apply Under.UnderMorphism.ext
    exact zeroMappingPathFiberRight.map_comp f g

/-- The right object of the pointed functor is the native mapping-path fiber
of the zero based arrow. -/
theorem zeroMappingPathFiber_right_obj (X : PointedCGWH.{u, v}) :
    (zeroMappingPathFiber.obj X).right =
      CGWH.mappingPathFiber.obj (zeroBasedArrow.obj X) :=
  rfl

/-- The total coordinate of the canonical point is the identity of the point
object. -/
theorem zeroMappingPathFiber_point_toTotal (X : PointedCGWH.{u, v}) :
    zeroMappingPathFiberPoint.app X ≫
        CGWH.mappingPathFiberToTotal.app (zeroBasedArrow.obj X) =
      𝟙 CGWH.point.{u, v} := by
  rw [show zeroMappingPathFiberPoint.app X =
      zeroStrictFiberPoint.app X ≫
        (Functor.whiskerLeft zeroBasedArrow
          CGWH.strictFiberToMappingPathFiber).app X from rfl]
  change zeroStrictFiberPoint.app X ≫
      (CGWH.strictFiberToMappingPathFiber.app (zeroBasedArrow.obj X) ≫
        CGWH.mappingPathFiberToTotal.app (zeroBasedArrow.obj X)) = _
  rw [CGWH.strictFiberToMappingPathFiber_toTotal]
  rw [CGWH.strictFiberToTotalNatTrans_app]
  change CGWH.strictFiberPoint X.hom X.hom
      (𝟙 CGWH.point.{u, v}) (by simp) ≫
        CGWH.strictFiberToTotal X.hom X.hom =
        𝟙 CGWH.point.{u, v}
  exact CGWH.strictFiberPoint_toTotal _ _ _ _

/-- The path coordinate of the canonical point is the native constant path at
the selected point. -/
theorem zeroMappingPathFiber_point_path (X : PointedCGWH.{u, v}) :
    zeroMappingPathFiberPoint.app X ≫
        CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj X) =
      X.hom ≫ CGWH.pathConstant.app X.right := by
  rw [show zeroMappingPathFiberPoint.app X =
      zeroStrictFiberPoint.app X ≫
        (Functor.whiskerLeft zeroBasedArrow
          CGWH.strictFiberToMappingPathFiber).app X from rfl]
  change zeroStrictFiberPoint.app X ≫
      (CGWH.strictFiberToMappingPathFiber.app (zeroBasedArrow.obj X) ≫
        CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj X)) = _
  rw [CGWH.strictFiberToMappingPathFiber_path]
  rw [← Category.assoc, CGWH.strictFiberToPointNatTrans_app]
  change (CGWH.strictFiberPoint X.hom X.hom
        (𝟙 CGWH.point.{u, v}) (by simp) ≫
          CGWH.strictFiberToPoint X.hom X.hom) ≫
      X.hom ≫ CGWH.pathConstant.app X.right = _
  rw [CGWH.strictFiberPoint_toPoint, Category.id_comp]

private noncomputable abbrev zeroMappingPathFiberPath
    (X : PointedCGWH.{u, v}) :
    zeroMappingPathFiberRight.obj X ⟶ CGWH.path.obj X.right :=
  CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj X)

private noncomputable def zeroMappingPathFiberLandingPath
    (X : PointedCGWH.{u, v}) :
  CGWH.cgwhToTop.obj (zeroMappingPathFiberRight.obj X) ⟶
      TopCat.pathObject (CGWH.cgwhToTop.obj X.right) :=
  CGWH.cgwhToTop.map (zeroMappingPathFiberPath X) ≫
    CGWH.pathLanding X.right

private theorem zeroMappingPathFiberLandingPath_evalZero
    (X : PointedCGWH.{u, v}) :
    zeroMappingPathFiberLandingPath X ≫ TopCat.pathEvalZero _ =
      CGWH.cgwhToTop.map
        (CGWH.point_isTerminal.from (zeroMappingPathFiberRight.obj X) ≫
          X.hom) := by
  unfold zeroMappingPathFiberLandingPath
  rw [Category.assoc, CGWH.pathLanding_evalZero]
  rw [← CGWH.cgwhToTop.map_comp]
  change CGWH.cgwhToTop.map
      (CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj X) ≫
        CGWH.pathEvalZero.app (zeroBasedArrow.obj X).base) = _
  rw [CGWH.mappingPathFiberPath_evalZero]
  congr 1

private theorem zeroMappingPathFiberLandingPath_evalOne
    (X : PointedCGWH.{u, v}) :
    zeroMappingPathFiberLandingPath X ≫ TopCat.pathEvalOne _ =
      CGWH.cgwhToTop.map
        (CGWH.point_isTerminal.from (zeroMappingPathFiberRight.obj X) ≫
          X.hom) := by
  unfold zeroMappingPathFiberLandingPath
  rw [Category.assoc, CGWH.pathLanding_evalOne]
  rw [← CGWH.cgwhToTop.map_comp]
  change CGWH.cgwhToTop.map
      (CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj X) ≫
        CGWH.pathEvalOne.app (zeroBasedArrow.obj X).base) = _
  rw [CGWH.mappingPathFiberPath_evalOne]
  congr 1

/-- Land the native path coordinate of the zero mapping-path fiber in the
ordinary loop space at the selected point. -/
noncomputable def zeroMappingPathFiberLanding (X : PointedCGWH.{u, v}) :
    CGWH.cgwhToTop.obj (zeroMappingPathFiber.obj X).right ⟶
      TopCat.of (LoopSpace X.right (X.hom PUnit.unit)) :=
  TopCat.ofHom
    { toFun := fun z =>
        { toFun := fun t => zeroMappingPathFiberLandingPath X z
            (TopCat.I.homeomorph.symm t)
          continuous_toFun :=
            (zeroMappingPathFiberLandingPath X z).continuous.comp
              TopCat.I.homeomorph.symm.continuous
          source' := by
            have h := ConcreteCategory.congr_hom
              (zeroMappingPathFiberLandingPath_evalZero X) z
            have hI : TopCat.I.homeomorph.symm (0 : unitInterval) =
                (0 : TopCat.I.{v}) := rfl
            rw [hI]
            change zeroMappingPathFiberLandingPath X z (0 : TopCat.I.{v}) =
              X.hom (CGWH.point_isTerminal.from
                (zeroMappingPathFiberRight.obj X) z) at h
            have hp : CGWH.point_isTerminal.from
                (zeroMappingPathFiberRight.obj X) z = PUnit.unit := rfl
            rw [hp] at h
            exact h
          target' := by
            have h := ConcreteCategory.congr_hom
              (zeroMappingPathFiberLandingPath_evalOne X) z
            have hI : TopCat.I.homeomorph.symm (1 : unitInterval) =
                (1 : TopCat.I.{v}) := rfl
            rw [hI]
            change zeroMappingPathFiberLandingPath X z (1 : TopCat.I.{v}) =
              X.hom (CGWH.point_isTerminal.from
                (zeroMappingPathFiberRight.obj X) z) at h
            have hp : CGWH.point_isTerminal.from
                (zeroMappingPathFiberRight.obj X) z = PUnit.unit := rfl
            rw [hp] at h
            exact h }
      continuous_toFun := by
        apply Path.continuous_uncurry_iff.mp
        exact continuous_eval.comp
          (((ConcreteCategory.hom
              (zeroMappingPathFiberLandingPath X)).continuous.comp
                continuous_fst).prodMk
            (TopCat.I.homeomorph.symm.continuous.comp continuous_snd)) }

/-- The landing is evaluation of the native path coordinate after the
standard interval homeomorphism. -/
theorem zeroMappingPathFiberLanding_apply (X : PointedCGWH.{u, v})
    (z : (zeroMappingPathFiber.obj X).right) (t : unitInterval) :
    zeroMappingPathFiberLanding X z t =
      CGWH.pathLanding X.right
        (CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj X) z)
        (TopCat.I.homeomorph.symm t) :=
  rfl

/-- The canonical point lands at the reflexive loop. -/
theorem zeroMappingPathFiberLanding_basepoint (X : PointedCGWH.{u, v}) :
    zeroMappingPathFiberLanding X
        ((zeroMappingPathFiber.obj X).hom PUnit.unit) =
      Path.refl (X.hom PUnit.unit) := by
  apply Path.ext
  funext t
  rw [zeroMappingPathFiberLanding_apply]
  have h := ConcreteCategory.congr_hom
    (zeroMappingPathFiber_point_path X) PUnit.unit
  change CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj X)
      ((zeroMappingPathFiber.obj X).hom PUnit.unit) =
    CGWH.pathConstant.app X.right (X.hom PUnit.unit) at h
  rw [h]
  exact CGWH.pathLanding_constant_apply X.right _ _

/-- Zero mapping-path-fiber landing is natural for strict postcomposition of
loops. -/
theorem zeroMappingPathFiberLanding_naturality
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (z : (zeroMappingPathFiber.obj X).right) (t : unitInterval) :
    zeroMappingPathFiberLanding Y ((zeroMappingPathFiber.map f).right z) t =
      ContinuousMap.strictLoopMap
          (CGWH.cgwhToTop.map f.right).hom
          (X.hom PUnit.unit)
        (zeroMappingPathFiberLanding X z) t := by
  change CGWH.pathLanding Y.right
      (CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj Y)
        ((zeroMappingPathFiber.map f).right z))
      (TopCat.I.homeomorph.symm t) =
    (CGWH.cgwhToTop.map f.right).hom
      (CGWH.pathLanding X.right
        (CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj X) z)
        (TopCat.I.homeomorph.symm t))
  have hpath := ConcreteCategory.congr_hom
    (CGWH.mappingPathFiberPath.naturality (zeroBasedArrow.map f)) z
  change CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj Y)
      ((zeroMappingPathFiber.map f).right z) =
    CGWH.path.map f.right
      (CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj X) z) at hpath
  rw [hpath]
  have hlanding := ConcreteCategory.congr_hom
    (CGWH.pathLanding_naturality f.right)
    (CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj X) z)
  exact congrArg (fun q => q (TopCat.I.homeomorph.symm t)) hlanding

end PointedCGWH
