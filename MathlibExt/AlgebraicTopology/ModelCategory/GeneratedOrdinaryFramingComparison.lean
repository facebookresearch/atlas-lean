/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinarySuspension
import MathlibExt.AlgebraicTopology.ModelCategory.FramingCylinderHomotopyCofiber
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedSuspensionLoopAdjunction

/-!
# Original generated cone suspension and actual ordinary framing suspension

The generated I cone and actual framing cone are compared through the same
canonical zero-arrow homotopy cofiber. The full framing cylinder quotient
retains both original Q endpoints and its genuine circle-tensor comparison.
These maps give natural comparisons with the ordinary suspension functor
defined by the original pointed framing on the same canonical Ho(C).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace HomotopicalAlgebra.GeneratedOrdinaryFramingComparison

open OrdinaryHoChosenPuppe PointedFramingAction DerivedSuspensionLoopAdjunction

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- The original generated cone suspension and actual framing cofiber have the same canonical computation. -/
def coneToFraming (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z) :
    GeneratedFunctorialReplacements.Q g ⋙ GeneratedOrdinaryPuppe.suspension g Z hZ ⋙
        toHomotopyCategory C ≅
      FramingCylinderCofiber.cofiber (GeneratedFunctorialReplacements.fromGeneration g) Z hZ ⋙
        toHomotopyCategory C := by
  letI := g.hasFunctorialFactorizationCofibrationsTrivialFibrations
  exact GeneratedOrdinarySuspension.cofiberComparison g Z hZ ≪≫
    (FramingCylinderHomotopyCofiber.comparison (GeneratedFunctorialReplacements.fromGeneration g) Z hZ).symm

section Pointed

variable [HasZeroObject C] (d : GeneratedFunctorialReplacements.Data (C := C))

attribute [local implicit_reducible] PointedFramingAction.leftCylinder
/-- The zero morphisms of the original coefficient category. -/
local instance coefficientZeroMorphisms : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
open scoped ZeroObject

/-- The actual full Q-cylinder quotient maps to the full degree-zero frame-cylinder quotient. -/
def fullToCylinderMap (X : C) :
    (FramingCylinderCofiber.fullQuotient d (0 : C) (isZero_zero C)).obj X ⟶
      cylinderCofiber ((leftFrame d).obj X) :=
  pushout.map (FramingCylinderCone.boundary d X)
    (toZero (0 : C) (isZero_zero C) (d.Q.obj X ⨿ d.Q.obj X))
    (cylinderBoundary ((leftFrame d).obj X))
    (0 : ((leftFrame d).obj X).obj ⦋0⦌ ⨿ ((leftFrame d).obj X).obj ⦋0⦌ ⟶ (0 : C))
    (𝟙 ((FramingCylinderCone.cylinderFunctor d).obj X)) (𝟙 (0 : C))
    (coprod.map ((leftZeroIso d).inv.app X) ((leftZeroIso d).inv.app X))
    (by
      change FramingCylinderCone.boundary d X ≫ 𝟙 _ =
        coprod.map ((leftZeroIso d).inv.app X) ((leftZeroIso d).inv.app X) ≫
          cylinderBoundary ((leftFrame d).obj X)
      exact (Category.comp_id _).trans (originalCylinderBoundary_frame d X))
    (HasZeroObject.zeroIsTerminal.hom_ext _ _)

/-- Both genuine Q/degree-zero endpoint isomorphisms make the whole quotient comparison invertible. -/
def fullToCylinderIso (X : C) :
    (FramingCylinderCofiber.fullQuotient d (0 : C) (isZero_zero C)).obj X ≅
      cylinderCofiber ((leftFrame d).obj X) := by
  let _ : IsIso (coprod.map ((leftZeroIso d).inv.app X) ((leftZeroIso d).inv.app X)) := by
    change IsIso (coprod.mapIso ((leftZeroIso d).app X).symm ((leftZeroIso d).app X).symm).hom
    infer_instance
  let _ : IsIso (fullToCylinderMap d X) := by
    dsimp only [fullToCylinderMap]
    exact pushout.map_isIso _ _ _ _ _ _ _ _ _
  exact asIso (fullToCylinderMap d X)

/-- The full comparison retains the entire original cylinder quotient leg. -/
theorem fullToCylinderIso_quotient (X : C) :
    FramingCylinderCofiber.fullCylinder d (0 : C) (isZero_zero C) X ≫
        (fullToCylinderIso d X).hom = cylinderQuotient ((leftFrame d).obj X) :=
  (pushout.inl_desc _ _ _).trans (Category.id_comp _)

/-- Every original source map commutes with both entire cylinder quotient calculations. -/
theorem fullToCylinderIso_naturality {X Y : C} (f : X ⟶ Y) :
    (FramingCylinderCofiber.fullQuotient d (0 : C) (isZero_zero C)).map f ≫
        (fullToCylinderIso d Y).hom =
      (fullToCylinderIso d X).hom ≫ cylinderMap ((leftFrame d).map f) := by
  apply pushout.hom_ext
  · change FramingCylinderCofiber.fullCylinder d (0 : C) (isZero_zero C) X ≫
        ((FramingCylinderCofiber.fullQuotient d (0 : C) (isZero_zero C)).map f ≫
          (fullToCylinderIso d Y).hom) =
      FramingCylinderCofiber.fullCylinder d (0 : C) (isZero_zero C) X ≫
        ((fullToCylinderIso d X).hom ≫ cylinderMap ((leftFrame d).map f))
    calc
      FramingCylinderCofiber.fullCylinder d (0 : C) (isZero_zero C) X ≫
          ((FramingCylinderCofiber.fullQuotient d (0 : C) (isZero_zero C)).map f ≫
            (fullToCylinderIso d Y).hom) =
          (FramingCylinderCofiber.fullCylinder d (0 : C) (isZero_zero C) X ≫
            (FramingCylinderCofiber.fullQuotient d (0 : C) (isZero_zero C)).map f) ≫
              (fullToCylinderIso d Y).hom := (Category.assoc _ _ _).symm
      _ = ((FramingCylinderCone.cylinderFunctor d).map f ≫
            FramingCylinderCofiber.fullCylinder d (0 : C) (isZero_zero C) Y) ≫
              (fullToCylinderIso d Y).hom :=
        congrArg (fun a => a ≫ (fullToCylinderIso d Y).hom)
          (FramingCylinderCofiber.fullCylinder_naturality d (0 : C) (isZero_zero C) f)
      _ = (FramingCylinderCone.cylinderFunctor d).map f ≫ cylinderQuotient ((leftFrame d).obj Y) := by
        rw [Category.assoc, fullToCylinderIso_quotient]
      _ = cylinderQuotient ((leftFrame d).obj X) ≫ cylinderMap ((leftFrame d).map f) :=
        (cylinderMap_quotient ((leftFrame d).map f)).symm
      _ = (FramingCylinderCofiber.fullCylinder d (0 : C) (isZero_zero C) X ≫
            (fullToCylinderIso d X).hom) ≫ cylinderMap ((leftFrame d).map f) :=
        congrArg (fun a => a ≫ cylinderMap ((leftFrame d).map f)) (fullToCylinderIso_quotient d X).symm
      _ = FramingCylinderCofiber.fullCylinder d (0 : C) (isZero_zero C) X ≫
            ((fullToCylinderIso d X).hom ≫ cylinderMap ((leftFrame d).map f)) := Category.assoc _ _ _
  · exact HasZeroObject.zeroIsInitial.hom_ext _ _

variable [HasColimitsOfSize.{0, v} C] [HasLimitsOfSize.{0, v} C]

/-- The full original Q cylinder quotient is naturally the actual framing tensor by the circle. -/
def fullQuotientTensorIso :
    FramingCylinderCofiber.fullQuotient d (0 : C) (isZero_zero C) ≅ framedTensor d circle :=
  NatIso.ofComponents
    (fun X => fullToCylinderIso d X ≪≫ (cylinderTensorIso ((leftFrame d).obj X)).symm)
    (fun {X Y} f => by
      have hInv : cylinderMap ((leftFrame d).map f) ≫ (cylinderTensorIso ((leftFrame d).obj Y)).inv =
          (cylinderTensorIso ((leftFrame d).obj X)).inv ≫ (framedTensor d circle).map f := by
        apply (cancel_epi (cylinderTensorIso ((leftFrame d).obj X)).hom).mp
        calc
          (cylinderTensorIso ((leftFrame d).obj X)).hom ≫
              (cylinderMap ((leftFrame d).map f) ≫ (cylinderTensorIso ((leftFrame d).obj Y)).inv) =
              ((cylinderTensorIso ((leftFrame d).obj X)).hom ≫ cylinderMap ((leftFrame d).map f)) ≫
                (cylinderTensorIso ((leftFrame d).obj Y)).inv := (Category.assoc _ _ _).symm
          _ = ((framedTensor d circle).map f ≫ (cylinderTensorIso ((leftFrame d).obj Y)).hom) ≫
                (cylinderTensorIso ((leftFrame d).obj Y)).inv :=
            congrArg (fun a => a ≫ (cylinderTensorIso ((leftFrame d).obj Y)).inv)
              (cylinderTensorIso_naturality ((leftFrame d).map f)).symm
          _ = (framedTensor d circle).map f := by
            rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
          _ = (cylinderTensorIso ((leftFrame d).obj X)).hom ≫
                ((cylinderTensorIso ((leftFrame d).obj X)).inv ≫ (framedTensor d circle).map f) := by
            simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      change (FramingCylinderCofiber.fullQuotient d (0 : C) (isZero_zero C)).map f ≫
          ((fullToCylinderIso d Y).hom ≫ (cylinderTensorIso ((leftFrame d).obj Y)).inv) =
        ((fullToCylinderIso d X).hom ≫ (cylinderTensorIso ((leftFrame d).obj X)).inv) ≫
          (framedTensor d circle).map f
      calc
        (FramingCylinderCofiber.fullQuotient d (0 : C) (isZero_zero C)).map f ≫
            ((fullToCylinderIso d Y).hom ≫ (cylinderTensorIso ((leftFrame d).obj Y)).inv) =
            ((FramingCylinderCofiber.fullQuotient d (0 : C) (isZero_zero C)).map f ≫
              (fullToCylinderIso d Y).hom) ≫ (cylinderTensorIso ((leftFrame d).obj Y)).inv :=
          (Category.assoc _ _ _).symm
        _ = ((fullToCylinderIso d X).hom ≫ cylinderMap ((leftFrame d).map f)) ≫
              (cylinderTensorIso ((leftFrame d).obj Y)).inv :=
          congrArg (fun a => a ≫ (cylinderTensorIso ((leftFrame d).obj Y)).inv)
            (fullToCylinderIso_naturality d f)
        _ = (fullToCylinderIso d X).hom ≫
              (cylinderMap ((leftFrame d).map f) ≫ (cylinderTensorIso ((leftFrame d).obj Y)).inv) :=
          Category.assoc _ _ _
        _ = (fullToCylinderIso d X).hom ≫
              ((cylinderTensorIso ((leftFrame d).obj X)).inv ≫ (framedTensor d circle).map f) :=
          congrArg (fun a => (fullToCylinderIso d X).hom ≫ a) hInv
        _ = ((fullToCylinderIso d X).hom ≫ (cylinderTensorIso ((leftFrame d).obj X)).inv) ≫
              (framedTensor d circle).map f := (Category.assoc _ _ _).symm)


/-- The actual circle tensor calculation agrees with the original ordinary suspension on every source map. -/
def tensorOrdinaryIso : framedTensor d circle ⋙ toHomotopyCategory C ≅
    toHomotopyCategory C ⋙ DerivedSuspensionLoopAdjunction.suspension d :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {X Y} f => by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact (DerivedSuspensionLoopAdjunction.suspension_map d f).symm)

/-- The actual remaining framing cofiber is naturally ordinary framing suspension. -/
def framingOrdinaryIso :
    FramingCylinderCofiber.cofiber d (0 : C) (isZero_zero C) ⋙ toHomotopyCategory C ≅
      toHomotopyCategory C ⋙ DerivedSuspensionLoopAdjunction.suspension d :=
  Functor.isoWhiskerRight (FramingCylinderCofiber.comparison d (0 : C) (isZero_zero C)).symm
      (toHomotopyCategory C) ≪≫
    Functor.isoWhiskerRight (fullQuotientTensorIso d) (toHomotopyCategory C) ≪≫ tensorOrdinaryIso d

/-- Original I-cone suspension after original Q agrees with actual ordinary suspension from the same framing data. -/
def comparisonOfGeneration (g : CofibrantGenerationData C κ) :
    GeneratedFunctorialReplacements.Q g ⋙
        GeneratedOrdinaryPuppe.suspension g (0 : C) (isZero_zero C) ⋙ toHomotopyCategory C ≅
      toHomotopyCategory C ⋙ DerivedSuspensionLoopAdjunction.suspension
        (GeneratedFunctorialReplacements.fromGeneration g) :=
  coneToFraming g (0 : C) (isZero_zero C) ≪≫
    framingOrdinaryIso (GeneratedFunctorialReplacements.fromGeneration g)

/-- Both actual zero choices give a full natural Arrow isomorphism with unchanged sources. -/
def zeroChoiceIso (Z : C) (hZ : IsZero Z) :
    zeroArrowFunctor Z hZ ≅ zeroArrowFunctor (0 : C) (isZero_zero C) :=
  NatIso.ofComponents
    (fun X => Arrow.isoMk (Iso.refl X)
      (hZ.isInitial.uniqueUpToIso HasZeroObject.zeroIsInitial)
      (HasZeroObject.zeroIsTerminal.hom_ext _ _))
    (fun {X Y} f => by
      apply Arrow.hom_ext
      · change f ≫ 𝟙 Y = 𝟙 X ≫ f
        simp
      · change 𝟙 Z ≫ (hZ.isInitial.uniqueUpToIso HasZeroObject.zeroIsInitial).hom =
          (hZ.isInitial.uniqueUpToIso HasZeroObject.zeroIsInitial).hom ≫ 𝟙 (0 : C)
        exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- Every caller zero and original I-cone computes the actual ordinary framing suspension naturally. -/
def comparison (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z) :
    GeneratedFunctorialReplacements.Q g ⋙ GeneratedOrdinaryPuppe.suspension g Z hZ ⋙
        toHomotopyCategory C ≅
      toHomotopyCategory C ⋙ DerivedSuspensionLoopAdjunction.suspension
        (GeneratedFunctorialReplacements.fromGeneration g) := by
  letI := g.hasFunctorialFactorizationCofibrationsTrivialFibrations
  exact GeneratedOrdinarySuspension.cofiberComparison g Z hZ ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (zeroChoiceIso Z hZ)
        (GeneratedOrdinaryCofiberComparison.canonicalCofiberOfGeneration g)) (toHomotopyCategory C) ≪≫
    (FramingCylinderHomotopyCofiber.comparison
      (GeneratedFunctorialReplacements.fromGeneration g) (0 : C) (isZero_zero C)).symm ≪≫
    framingOrdinaryIso (GeneratedFunctorialReplacements.fromGeneration g)

end Pointed

end HomotopicalAlgebra.GeneratedOrdinaryFramingComparison
