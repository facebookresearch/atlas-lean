/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.FramingCylinderCone

/-!
# The remaining framing-cone cofiber is the full cylinder quotient

The first-endpoint cone and its remaining cofiber paste to the quotient
of the original whole two-end cylinder boundary. Every quotient and map
uses the same chosen pushout. The comparison is natural and retains both
the full original cylinder leg and the actual zero leg.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.FramingCylinderCofiber

open OrdinaryHoChosenPuppe

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (d : GeneratedFunctorialReplacements.Data (C := C)) (Z : C) (hZ : IsZero Z)

/-- Pointwise chosen pushouts of a full natural input map and its actual zero contraction. -/
private def quotientFunctor (A B : C ⥤ C) (ι : A ⟶ B) : C ⥤ C where
  obj X := pushout (ι.app X) (toZero Z hZ (A.obj X))
  map {X Y} f := pushout.map (ι.app X) (toZero Z hZ (A.obj X))
    (ι.app Y) (toZero Z hZ (A.obj Y)) (B.map f) (𝟙 Z) (A.map f)
    (ι.naturality f).symm (hZ.isTerminal.hom_ext _ _)
  map_id X := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc]
      exact (congrArg (fun a => a ≫ pushout.inl (ι.app X) (toZero Z hZ (A.obj X)))
        (B.map_id X)).trans ((Category.id_comp _).trans (Category.comp_id _).symm)
    · rw [pushout.inr_desc]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  map_comp f g := by
    simp only [Functor.map_comp]
    rw [pushout.map_comp]
    simp only [Category.comp_id]

/-- The whole remaining cofiber uses the actual second insertion and original zero. -/
def cofiber : C ⥤ C :=
  quotientFunctor Z hZ d.Q (FramingCylinderCone.cone d Z hZ) (FramingCylinderCone.inclusion d Z hZ)

/-- The two original Q source copies form their full functor on all maps. -/
def sourcePair : C ⥤ C where
  obj X := d.Q.obj X ⨿ d.Q.obj X
  map f := coprod.map (d.Q.map f) (d.Q.map f)
  map_id X := by apply coprod.hom_ext <;> simp
  map_comp f g := by apply coprod.hom_ext <;> simp

/-- The entire original cylinder boundary is natural on both Q source copies. -/
def boundaryNatTrans : sourcePair d ⟶ FramingCylinderCone.cylinderFunctor d where
  app X := FramingCylinderCone.boundary d X
  naturality X Y f := by
    change coprod.map (d.Q.map f) (d.Q.map f) ≫ FramingCylinderCone.boundary d Y =
      FramingCylinderCone.boundary d X ≫ (FramingCylinderCone.cylinderFunctor d).map f
    apply coprod.hom_ext
    · simp only [FramingCylinderCone.boundary, coprod.inl_map_assoc, coprod.inl_desc_assoc,
        coprod.inl_desc]
      exact (FramingCylinderCone.first d).naturality f
    · simp only [FramingCylinderCone.boundary, coprod.inr_map_assoc, coprod.inr_desc_assoc,
        coprod.inr_desc]
      exact (FramingCylinderCone.second d).naturality f

/-- Collapse the whole original two-end cylinder boundary to the actual zero. -/
def fullQuotient : C ⥤ C :=
  quotientFunctor Z hZ (sourcePair d) (FramingCylinderCone.cylinderFunctor d) (boundaryNatTrans d)

/-- The actual cone injects into its remaining cofiber by the original quotient leg. -/
def cofiberLeg (X : C) : (FramingCylinderCone.cone d Z hZ).obj X ⟶ (cofiber d Z hZ).obj X :=
  pushout.inl _ _

/-- The actual zero injects by the other original cofiber leg. -/
def cofiberZero (X : C) : Z ⟶ (cofiber d Z hZ).obj X := pushout.inr _ _

/-- The full cylinder quotient retains the entire original cylinder leg. -/
def fullCylinder (X : C) : (FramingCylinderCone.cylinderFunctor d).obj X ⟶
    (fullQuotient d Z hZ).obj X := pushout.inl _ _

/-- The full cylinder quotient retains the same original zero leg. -/
def fullZero (X : C) : Z ⟶ (fullQuotient d Z hZ).obj X := pushout.inr _ _

/-- Every cofiber map retains the original whole cone map. -/
theorem cofiberLeg_naturality {X Y : C} (f : X ⟶ Y) :
    cofiberLeg d Z hZ X ≫ (cofiber d Z hZ).map f =
      (FramingCylinderCone.cone d Z hZ).map f ≫ cofiberLeg d Z hZ Y := pushout.inl_desc _ _ _

/-- Every full cylinder quotient map retains the original degree-one frame map. -/
theorem fullCylinder_naturality {X Y : C} (f : X ⟶ Y) :
    fullCylinder d Z hZ X ≫ (fullQuotient d Z hZ).map f =
      (FramingCylinderCone.cylinderFunctor d).map f ≫ fullCylinder d Z hZ Y := pushout.inl_desc _ _ _

/-- The two original pushouts paste to the quotient of the entire cylinder boundary. -/
theorem fullQuotientIsPushout (X : C) :
    IsPushout (FramingCylinderCone.boundary d X) (toZero Z hZ ((sourcePair d).obj X))
      (FramingCylinderCone.cylinderLeg d Z hZ X ≫ cofiberLeg d Z hZ X) (cofiberZero d Z hZ X) := by
  have h := (IsPushout.of_isColimit (FramingCylinderCone.boundaryIsColimit d Z hZ X)).paste_vert
    (IsPushout.of_hasPushout ((FramingCylinderCone.inclusion d Z hZ).app X)
      (toZero Z hZ (d.Q.obj X)))
  have hZero : FramingCylinderCone.collapseBoundary d Z hZ X ≫ toZero Z hZ (d.Q.obj X) =
      toZero Z hZ ((sourcePair d).obj X) := hZ.isTerminal.hom_ext _ _
  exact hZero ▸ h

/-- The full cylinder quotient and remaining cone cofiber have the same actual universal property. -/
def fullQuotientIso (X : C) : (fullQuotient d Z hZ).obj X ≅ (cofiber d Z hZ).obj X :=
  (pushout.isColimit (FramingCylinderCone.boundary d X)
    (toZero Z hZ ((sourcePair d).obj X))).coconePointUniqueUpToIso
      (fullQuotientIsPushout d Z hZ X).isColimit

/-- The full comparison keeps the entire original cylinder quotient map. -/
theorem fullQuotientIso_cylinder (X : C) :
    fullCylinder d Z hZ X ≫ (fullQuotientIso d Z hZ X).hom =
      FramingCylinderCone.cylinderLeg d Z hZ X ≫ cofiberLeg d Z hZ X :=
  (pushout.isColimit (FramingCylinderCone.boundary d X) (toZero Z hZ ((sourcePair d).obj X))).fac
    (fullQuotientIsPushout d Z hZ X).cocone WalkingSpan.left

/-- The full comparison keeps the unchanged original zero quotient map. -/
theorem fullQuotientIso_zero (X : C) :
    fullZero d Z hZ X ≫ (fullQuotientIso d Z hZ X).hom = cofiberZero d Z hZ X :=
  (pushout.isColimit (FramingCylinderCone.boundary d X) (toZero Z hZ ((sourcePair d).obj X))).fac
    (fullQuotientIsPushout d Z hZ X).cocone WalkingSpan.right

/-- Both whole original quotient legs give the entire natural cylinder/cofiber comparison. -/
def comparison : fullQuotient d Z hZ ≅ cofiber d Z hZ :=
  NatIso.ofComponents (fullQuotientIso d Z hZ) (fun {X Y} f => by
    apply pushout.hom_ext
    · change fullCylinder d Z hZ X ≫
          ((fullQuotient d Z hZ).map f ≫ (fullQuotientIso d Z hZ Y).hom) =
        fullCylinder d Z hZ X ≫ ((fullQuotientIso d Z hZ X).hom ≫ (cofiber d Z hZ).map f)
      calc
        fullCylinder d Z hZ X ≫ ((fullQuotient d Z hZ).map f ≫ (fullQuotientIso d Z hZ Y).hom) =
            (fullCylinder d Z hZ X ≫ (fullQuotient d Z hZ).map f) ≫
              (fullQuotientIso d Z hZ Y).hom := (Category.assoc _ _ _).symm
        _ = ((FramingCylinderCone.cylinderFunctor d).map f ≫ fullCylinder d Z hZ Y) ≫
              (fullQuotientIso d Z hZ Y).hom :=
          congrArg (fun a => a ≫ (fullQuotientIso d Z hZ Y).hom) (fullCylinder_naturality d Z hZ f)
        _ = (FramingCylinderCone.cylinderFunctor d).map f ≫
              (fullCylinder d Z hZ Y ≫ (fullQuotientIso d Z hZ Y).hom) := Category.assoc _ _ _
        _ = (FramingCylinderCone.cylinderFunctor d).map f ≫
              (FramingCylinderCone.cylinderLeg d Z hZ Y ≫ cofiberLeg d Z hZ Y) :=
          congrArg (fun a => (FramingCylinderCone.cylinderFunctor d).map f ≫ a)
            (fullQuotientIso_cylinder d Z hZ Y)
        _ = ((FramingCylinderCone.cylinderFunctor d).map f ≫
              FramingCylinderCone.cylinderLeg d Z hZ Y) ≫ cofiberLeg d Z hZ Y :=
          (Category.assoc _ _ _).symm
        _ = (FramingCylinderCone.cylinderLeg d Z hZ X ≫
              (FramingCylinderCone.cone d Z hZ).map f) ≫ cofiberLeg d Z hZ Y :=
          congrArg (fun a => a ≫ cofiberLeg d Z hZ Y) (FramingCylinderCone.coneMap_cylinder d Z hZ f).symm
        _ = FramingCylinderCone.cylinderLeg d Z hZ X ≫
              ((FramingCylinderCone.cone d Z hZ).map f ≫ cofiberLeg d Z hZ Y) := Category.assoc _ _ _
        _ = FramingCylinderCone.cylinderLeg d Z hZ X ≫
              (cofiberLeg d Z hZ X ≫ (cofiber d Z hZ).map f) :=
          congrArg (fun a => FramingCylinderCone.cylinderLeg d Z hZ X ≫ a)
            (cofiberLeg_naturality d Z hZ f).symm
        _ = (FramingCylinderCone.cylinderLeg d Z hZ X ≫ cofiberLeg d Z hZ X) ≫
              (cofiber d Z hZ).map f := (Category.assoc _ _ _).symm
        _ = (fullCylinder d Z hZ X ≫ (fullQuotientIso d Z hZ X).hom) ≫ (cofiber d Z hZ).map f :=
          congrArg (fun a => a ≫ (cofiber d Z hZ).map f) (fullQuotientIso_cylinder d Z hZ X).symm
        _ = fullCylinder d Z hZ X ≫ ((fullQuotientIso d Z hZ X).hom ≫ (cofiber d Z hZ).map f) :=
          Category.assoc _ _ _
    · exact hZ.isInitial.hom_ext _ _)

end HomotopicalAlgebra.FramingCylinderCofiber
