/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedCarrierHomComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.LeftRightDerivedCarrierComparison

/-!
# Complete original sphere-carrier Hom transport

The two actual canonical derived adjunctions keep their original source
models and cardinal choices. Their complete Hom equivalences and inverse
functions equal the transported original carrier functions on all localized
objects and morphisms, with naturality, unit, counit and both triangles.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

namespace PointedCGWH.Spectra.Symmetric.LeftRightNativeModel

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

@[instance_reducible]
private def sourceLeftModel : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
  HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

@[instance_reducible]
private def sourceRightModel : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
  HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}

attribute [local instance] sourceLeftModel sourceRightModel
  Native.modelCategory toRight_isQuillenAdjunction toLeft_isQuillenAdjunction

/-- Instantiate the entire original Right carrier Hom equivalence before its functions. -/
def toRightCarrierHomEquiv (X : originalLeftHo.{u, v}) (Y :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) :
    (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X ⟶ Y) ≃ (X ⟶
        toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y) :=
  QuillenCarrierLocalization.transportedHomEquiv
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps X Y

/-- The actual canonical Right derived Hom equivalence keeps both original carrier functions. -/
theorem toRightDerived_carrierHomEquiv (X : originalLeftHo.{u, v}) (Y :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) :
    toRightDerivedAdjunctionData.{u, v}.adjunction.homEquiv X Y = toRightCarrierHomEquiv X Y :=
  QuillenCarrierLocalization.derivedHomEquiv_eq
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps X Y

/-- The complete original Right forward Hom function is retained. -/
theorem toRightDerived_carrierHomFunction (X : originalLeftHo.{u, v}) (Y :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) :
    (toRightDerivedAdjunctionData.{u, v}.adjunction.homEquiv X Y).toFun =
        (toRightCarrierHomEquiv X Y).toFun :=
  QuillenCarrierLocalization.derivedHomFunction_eq
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps X Y

/-- The entire original Right inverse Hom function is retained. -/
theorem toRightDerived_carrierHomInverseFunction (X : originalLeftHo.{u, v}) (Y :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) :
    (toRightDerivedAdjunctionData.{u, v}.adjunction.homEquiv X Y).invFun =
        (toRightCarrierHomEquiv X Y).invFun :=
  QuillenCarrierLocalization.derivedHomInverseFunction_eq
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps X Y

/-- The full original Right transported Hom function is natural in every source arrow. -/
theorem toRightCarrierHom_leftNaturality {X X' : originalLeftHo.{u, v}} {Y :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})}
    (f : X' ⟶ X) (g : toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X ⟶ Y) :
    toRightCarrierHomEquiv X' Y (toRightDerivedAdjunctionData.{u, v}.leftDerived.map f ≫ g) =
        f ≫ toRightCarrierHomEquiv X Y g :=
  QuillenCarrierLocalization.transportedHomLeftNaturality
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps f g

/-- The whole original Right transported Hom function is natural in every target arrow. -/
theorem toRightCarrierHom_rightNaturality {X : originalLeftHo.{u, v}} {Y Y' :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})}
    (f : toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X ⟶ Y) (g : Y ⟶ Y') :
    toRightCarrierHomEquiv X Y' (f ≫ g) = toRightCarrierHomEquiv X Y f ≫
        toRightDerivedAdjunctionData.{u, v}.rightDerived.map g :=
  QuillenCarrierLocalization.transportedHomRightNaturality
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps f g

/-- The entire original Right inverse Hom function is natural in every source arrow. -/
theorem toRightCarrierHom_inverseLeftNaturality {X X' : originalLeftHo.{u, v}} {Y :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})}
    (f : X' ⟶ X) (g : X ⟶ toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y) :
    (toRightCarrierHomEquiv X' Y).symm (f ≫ g) = toRightDerivedAdjunctionData.{u,
        v}.leftDerived.map f ≫ (toRightCarrierHomEquiv X Y).symm g :=
  QuillenCarrierLocalization.transportedHomInverseLeftNaturality
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps f g

/-- The full original Right inverse Hom function is natural in every target arrow. -/
theorem toRightCarrierHom_inverseRightNaturality {X : originalLeftHo.{u, v}} {Y Y' :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})}
    (f : X ⟶ toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y) (g : Y ⟶ Y') :
    (toRightCarrierHomEquiv X Y').symm (f ≫ toRightDerivedAdjunctionData.{u,
        v}.rightDerived.map g) = (toRightCarrierHomEquiv X Y).symm f ≫ g :=
  QuillenCarrierLocalization.transportedHomInverseRightNaturality
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps f g

/-- The entire Right transported Hom function recovers its actual original derived unit. -/
theorem toRightCarrierHom_unit (X : originalLeftHo.{u, v}) :
    toRightCarrierHomEquiv X (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X) (𝟙 _) =
        toRightDerivedAdjunctionData.{u, v}.adjunction.unit.app X :=
  QuillenCarrierLocalization.transportedHomUnit
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps X

/-- The entire Right inverse Hom function recovers its actual original derived counit. -/
theorem toRightCarrierHom_counit (Y : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) :
    (toRightCarrierHomEquiv (toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y) Y).symm
        (𝟙 _) = toRightDerivedAdjunctionData.{u, v}.adjunction.counit.app Y :=
  QuillenCarrierLocalization.transportedHomCounit
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps Y

/-- The actual Right transported unit and counit satisfy the full left triangle. -/
theorem toRightCarrierHom_leftTriangle (X : originalLeftHo.{u, v}) :
    toRightDerivedAdjunctionData.{u, v}.leftDerived.map (toRightCarrierHomEquiv X
        (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X) (𝟙 _)) ≫
      (toRightCarrierHomEquiv (toRightDerivedAdjunctionData.{u, v}.rightDerived.obj
          (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X))
        (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X)).symm (𝟙 _) = 𝟙
            (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X) :=
  QuillenCarrierLocalization.transportedHomLeftTriangle
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps X

/-- The actual Right transported unit and counit satisfy the full right triangle. -/
theorem toRightCarrierHom_rightTriangle (Y :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) :
    toRightCarrierHomEquiv (toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y)
        (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj
            (toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y)) (𝟙 _) ≫
      toRightDerivedAdjunctionData.{u, v}.rightDerived.map ((toRightCarrierHomEquiv
          (toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y) Y).symm (𝟙 _)) =
        𝟙 (toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y) :=
  QuillenCarrierLocalization.transportedHomRightTriangle
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps Y

/-- Instantiate the entire original Left carrier Hom equivalence before its functions. -/
def toLeftCarrierHomEquiv (X : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) (Y :
    originalLeftHo.{u, v}) :
    (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X ⟶ Y) ≃ (X ⟶
        toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y) :=
  QuillenCarrierLocalization.transportedHomEquiv
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps X Y

/-- The actual canonical Left derived Hom equivalence keeps both original carrier functions. -/
theorem toLeftDerived_carrierHomEquiv (X :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) (Y : originalLeftHo.{u, v}) :
    toLeftDerivedAdjunctionData.{u, v}.adjunction.homEquiv X Y = toLeftCarrierHomEquiv X Y :=
  QuillenCarrierLocalization.derivedHomEquiv_eq
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps X Y

/-- The complete original Left forward Hom function is retained. -/
theorem toLeftDerived_carrierHomFunction (X :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) (Y : originalLeftHo.{u, v}) :
    (toLeftDerivedAdjunctionData.{u, v}.adjunction.homEquiv X Y).toFun =
        (toLeftCarrierHomEquiv X Y).toFun :=
  QuillenCarrierLocalization.derivedHomFunction_eq
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps X Y

/-- The entire original Left inverse Hom function is retained. -/
theorem toLeftDerived_carrierHomInverseFunction (X :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) (Y : originalLeftHo.{u, v}) :
    (toLeftDerivedAdjunctionData.{u, v}.adjunction.homEquiv X Y).invFun =
        (toLeftCarrierHomEquiv X Y).invFun :=
  QuillenCarrierLocalization.derivedHomInverseFunction_eq
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps X Y

/-- The full original Left transported Hom function is natural in every source arrow. -/
theorem toLeftCarrierHom_leftNaturality {X X' :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} {Y : originalLeftHo.{u, v}}
    (f : X' ⟶ X) (g : toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X ⟶ Y) :
    toLeftCarrierHomEquiv X' Y (toLeftDerivedAdjunctionData.{u, v}.leftDerived.map f ≫ g) = f
        ≫ toLeftCarrierHomEquiv X Y g :=
  QuillenCarrierLocalization.transportedHomLeftNaturality
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps f g

/-- The whole original Left transported Hom function is natural in every target arrow. -/
theorem toLeftCarrierHom_rightNaturality {X :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} {Y Y' : originalLeftHo.{u,
      v}}
    (f : toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X ⟶ Y) (g : Y ⟶ Y') :
    toLeftCarrierHomEquiv X Y' (f ≫ g) = toLeftCarrierHomEquiv X Y f ≫
        toLeftDerivedAdjunctionData.{u, v}.rightDerived.map g :=
  QuillenCarrierLocalization.transportedHomRightNaturality
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps f g

/-- The entire original Left inverse Hom function is natural in every source arrow. -/
theorem toLeftCarrierHom_inverseLeftNaturality {X X' :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} {Y : originalLeftHo.{u, v}}
    (f : X' ⟶ X) (g : X ⟶ toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y) :
    (toLeftCarrierHomEquiv X' Y).symm (f ≫ g) = toLeftDerivedAdjunctionData.{u,
        v}.leftDerived.map f ≫ (toLeftCarrierHomEquiv X Y).symm g :=
  QuillenCarrierLocalization.transportedHomInverseLeftNaturality
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps f g

/-- The full original Left inverse Hom function is natural in every target arrow. -/
theorem toLeftCarrierHom_inverseRightNaturality {X :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} {Y Y' : originalLeftHo.{u,
      v}}
    (f : X ⟶ toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y) (g : Y ⟶ Y') :
    (toLeftCarrierHomEquiv X Y').symm (f ≫ toLeftDerivedAdjunctionData.{u,
        v}.rightDerived.map g) = (toLeftCarrierHomEquiv X Y).symm f ≫ g :=
  QuillenCarrierLocalization.transportedHomInverseRightNaturality
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps f g

/-- The entire Left transported Hom function recovers its actual original derived unit. -/
theorem toLeftCarrierHom_unit (X : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) :
    toLeftCarrierHomEquiv X (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X) (𝟙 _) =
        toLeftDerivedAdjunctionData.{u, v}.adjunction.unit.app X :=
  QuillenCarrierLocalization.transportedHomUnit
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps X

/-- The entire Left inverse Hom function recovers its actual original derived counit. -/
theorem toLeftCarrierHom_counit (Y : originalLeftHo.{u, v}) :
    (toLeftCarrierHomEquiv (toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y) Y).symm (𝟙
        _) = toLeftDerivedAdjunctionData.{u, v}.adjunction.counit.app Y :=
  QuillenCarrierLocalization.transportedHomCounit
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps Y

/-- The actual Left transported unit and counit satisfy the full left triangle. -/
theorem toLeftCarrierHom_leftTriangle (X : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) :
    toLeftDerivedAdjunctionData.{u, v}.leftDerived.map (toLeftCarrierHomEquiv X
        (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X) (𝟙 _)) ≫
      (toLeftCarrierHomEquiv (toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj
          (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X))
        (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X)).symm (𝟙 _) = 𝟙
            (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X) :=
  QuillenCarrierLocalization.transportedHomLeftTriangle
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps X

/-- The actual Left transported unit and counit satisfy the full right triangle. -/
theorem toLeftCarrierHom_rightTriangle (Y : originalLeftHo.{u, v}) :
    toLeftCarrierHomEquiv (toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y)
        (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj (toLeftDerivedAdjunctionData.{u,
            v}.rightDerived.obj Y)) (𝟙 _) ≫
      toLeftDerivedAdjunctionData.{u, v}.rightDerived.map ((toLeftCarrierHomEquiv
          (toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y) Y).symm (𝟙 _)) =
        𝟙 (toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y) :=
  QuillenCarrierLocalization.transportedHomRightTriangle
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps Y

end PointedCGWH.Spectra.Symmetric.LeftRightNativeModel

namespace PointedCGWH.Spectra.Symmetric.LeftRightNativeModel.Canonical

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction


attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel toRight_isQuillenAdjunction
  toLeft_isQuillenAdjunction

/-- Instantiate the entire original Right carrier Hom equivalence before its functions. -/
def toRightCarrierHomEquiv (X : originalLeftHo.{u, v}) (Y :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) :
    (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X ⟶ Y) ≃ (X ⟶
        toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y) :=
  QuillenCarrierLocalization.transportedHomEquiv
      carrierEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps X Y

/-- The actual canonical Right derived Hom equivalence keeps both original carrier functions. -/
theorem toRightDerived_carrierHomEquiv (X : originalLeftHo.{u, v}) (Y :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) :
    toRightDerivedAdjunctionData.{u, v}.adjunction.homEquiv X Y = toRightCarrierHomEquiv X Y :=
  QuillenCarrierLocalization.derivedHomEquiv_eq
      carrierEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps X Y

/-- The complete original Right forward Hom function is retained. -/
theorem toRightDerived_carrierHomFunction (X : originalLeftHo.{u, v}) (Y :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) :
    (toRightDerivedAdjunctionData.{u, v}.adjunction.homEquiv X Y).toFun =
        (toRightCarrierHomEquiv X Y).toFun :=
  QuillenCarrierLocalization.derivedHomFunction_eq
      carrierEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps X Y

/-- The entire original Right inverse Hom function is retained. -/
theorem toRightDerived_carrierHomInverseFunction (X : originalLeftHo.{u, v}) (Y :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) :
    (toRightDerivedAdjunctionData.{u, v}.adjunction.homEquiv X Y).invFun =
        (toRightCarrierHomEquiv X Y).invFun :=
  QuillenCarrierLocalization.derivedHomInverseFunction_eq
      carrierEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps X Y

/-- The full original Right transported Hom function is natural in every source arrow. -/
theorem toRightCarrierHom_leftNaturality {X X' : originalLeftHo.{u, v}} {Y :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}}
    (f : X' ⟶ X) (g : toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X ⟶ Y) :
    toRightCarrierHomEquiv X' Y (toRightDerivedAdjunctionData.{u, v}.leftDerived.map f ≫ g) =
        f ≫ toRightCarrierHomEquiv X Y g :=
  QuillenCarrierLocalization.transportedHomLeftNaturality
      carrierEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps f g

/-- The whole original Right transported Hom function is natural in every target arrow. -/
theorem toRightCarrierHom_rightNaturality {X : originalLeftHo.{u, v}} {Y Y' :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}}
    (f : toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X ⟶ Y) (g : Y ⟶ Y') :
    toRightCarrierHomEquiv X Y' (f ≫ g) = toRightCarrierHomEquiv X Y f ≫
        toRightDerivedAdjunctionData.{u, v}.rightDerived.map g :=
  QuillenCarrierLocalization.transportedHomRightNaturality
      carrierEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps f g

/-- The entire original Right inverse Hom function is natural in every source arrow. -/
theorem toRightCarrierHom_inverseLeftNaturality {X X' : originalLeftHo.{u, v}} {Y :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}}
    (f : X' ⟶ X) (g : X ⟶ toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y) :
    (toRightCarrierHomEquiv X' Y).symm (f ≫ g) = toRightDerivedAdjunctionData.{u,
        v}.leftDerived.map f ≫ (toRightCarrierHomEquiv X Y).symm g :=
  QuillenCarrierLocalization.transportedHomInverseLeftNaturality
      carrierEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps f g

/-- The full original Right inverse Hom function is natural in every target arrow. -/
theorem toRightCarrierHom_inverseRightNaturality {X : originalLeftHo.{u, v}} {Y Y' :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}}
    (f : X ⟶ toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y) (g : Y ⟶ Y') :
    (toRightCarrierHomEquiv X Y').symm (f ≫ toRightDerivedAdjunctionData.{u,
        v}.rightDerived.map g) = (toRightCarrierHomEquiv X Y).symm f ≫ g :=
  QuillenCarrierLocalization.transportedHomInverseRightNaturality
      carrierEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps f g

/-- The entire Right transported Hom function recovers its actual original derived unit. -/
theorem toRightCarrierHom_unit (X : originalLeftHo.{u, v}) :
    toRightCarrierHomEquiv X (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X) (𝟙 _) =
        toRightDerivedAdjunctionData.{u, v}.adjunction.unit.app X :=
  QuillenCarrierLocalization.transportedHomUnit
      carrierEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps X

/-- The entire Right inverse Hom function recovers its actual original derived counit. -/
theorem toRightCarrierHom_counit (Y : PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) :
    (toRightCarrierHomEquiv (toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y) Y).symm
        (𝟙 _) = toRightDerivedAdjunctionData.{u, v}.adjunction.counit.app Y :=
  QuillenCarrierLocalization.transportedHomCounit
      carrierEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps Y

/-- The actual Right transported unit and counit satisfy the full left triangle. -/
theorem toRightCarrierHom_leftTriangle (X : originalLeftHo.{u, v}) :
    toRightDerivedAdjunctionData.{u, v}.leftDerived.map (toRightCarrierHomEquiv X
        (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X) (𝟙 _)) ≫
      (toRightCarrierHomEquiv (toRightDerivedAdjunctionData.{u, v}.rightDerived.obj
          (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X))
        (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X)).symm (𝟙 _) = 𝟙
            (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj X) :=
  QuillenCarrierLocalization.transportedHomLeftTriangle
      carrierEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps X

/-- The actual Right transported unit and counit satisfy the full right triangle. -/
theorem toRightCarrierHom_rightTriangle (Y :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) :
    toRightCarrierHomEquiv (toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y)
        (toRightDerivedAdjunctionData.{u, v}.leftDerived.obj
            (toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y)) (𝟙 _) ≫
      toRightDerivedAdjunctionData.{u, v}.rightDerived.map ((toRightCarrierHomEquiv
          (toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y) Y).symm (𝟙 _)) =
        𝟙 (toRightDerivedAdjunctionData.{u, v}.rightDerived.obj Y) :=
  QuillenCarrierLocalization.transportedHomRightTriangle
      carrierEquivalence.{u, v} toRight_allWeakMaps
      toLeft_allWeakMaps Y

/-- Instantiate the entire original Left carrier Hom equivalence before its functions. -/
def toLeftCarrierHomEquiv (X : PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) (Y :
    originalLeftHo.{u, v}) :
    (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X ⟶ Y) ≃ (X ⟶
        toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y) :=
  QuillenCarrierLocalization.transportedHomEquiv
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps X Y

/-- The actual canonical Left derived Hom equivalence keeps both original carrier functions. -/
theorem toLeftDerived_carrierHomEquiv (X :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) (Y : originalLeftHo.{u, v}) :
    toLeftDerivedAdjunctionData.{u, v}.adjunction.homEquiv X Y = toLeftCarrierHomEquiv X Y :=
  QuillenCarrierLocalization.derivedHomEquiv_eq
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps X Y

/-- The complete original Left forward Hom function is retained. -/
theorem toLeftDerived_carrierHomFunction (X :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) (Y : originalLeftHo.{u, v}) :
    (toLeftDerivedAdjunctionData.{u, v}.adjunction.homEquiv X Y).toFun =
        (toLeftCarrierHomEquiv X Y).toFun :=
  QuillenCarrierLocalization.derivedHomFunction_eq
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps X Y

/-- The entire original Left inverse Hom function is retained. -/
theorem toLeftDerived_carrierHomInverseFunction (X :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) (Y : originalLeftHo.{u, v}) :
    (toLeftDerivedAdjunctionData.{u, v}.adjunction.homEquiv X Y).invFun =
        (toLeftCarrierHomEquiv X Y).invFun :=
  QuillenCarrierLocalization.derivedHomInverseFunction_eq
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps X Y

/-- The full original Left transported Hom function is natural in every source arrow. -/
theorem toLeftCarrierHom_leftNaturality {X X' :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}} {Y : originalLeftHo.{u, v}}
    (f : X' ⟶ X) (g : toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X ⟶ Y) :
    toLeftCarrierHomEquiv X' Y (toLeftDerivedAdjunctionData.{u, v}.leftDerived.map f ≫ g) = f
        ≫ toLeftCarrierHomEquiv X Y g :=
  QuillenCarrierLocalization.transportedHomLeftNaturality
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps f g

/-- The whole original Left transported Hom function is natural in every target arrow. -/
theorem toLeftCarrierHom_rightNaturality {X :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}} {Y Y' : originalLeftHo.{u, v}}
    (f : toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X ⟶ Y) (g : Y ⟶ Y') :
    toLeftCarrierHomEquiv X Y' (f ≫ g) = toLeftCarrierHomEquiv X Y f ≫
        toLeftDerivedAdjunctionData.{u, v}.rightDerived.map g :=
  QuillenCarrierLocalization.transportedHomRightNaturality
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps f g

/-- The entire original Left inverse Hom function is natural in every source arrow. -/
theorem toLeftCarrierHom_inverseLeftNaturality {X X' :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}} {Y : originalLeftHo.{u, v}}
    (f : X' ⟶ X) (g : X ⟶ toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y) :
    (toLeftCarrierHomEquiv X' Y).symm (f ≫ g) = toLeftDerivedAdjunctionData.{u,
        v}.leftDerived.map f ≫ (toLeftCarrierHomEquiv X Y).symm g :=
  QuillenCarrierLocalization.transportedHomInverseLeftNaturality
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps f g

/-- The full original Left inverse Hom function is natural in every target arrow. -/
theorem toLeftCarrierHom_inverseRightNaturality {X :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}} {Y Y' : originalLeftHo.{u, v}}
    (f : X ⟶ toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y) (g : Y ⟶ Y') :
    (toLeftCarrierHomEquiv X Y').symm (f ≫ toLeftDerivedAdjunctionData.{u,
        v}.rightDerived.map g) = (toLeftCarrierHomEquiv X Y).symm f ≫ g :=
  QuillenCarrierLocalization.transportedHomInverseRightNaturality
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps f g

/-- The entire Left transported Hom function recovers its actual original derived unit. -/
theorem toLeftCarrierHom_unit (X : PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) :
    toLeftCarrierHomEquiv X (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X) (𝟙 _) =
        toLeftDerivedAdjunctionData.{u, v}.adjunction.unit.app X :=
  QuillenCarrierLocalization.transportedHomUnit
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps X

/-- The entire Left inverse Hom function recovers its actual original derived counit. -/
theorem toLeftCarrierHom_counit (Y : originalLeftHo.{u, v}) :
    (toLeftCarrierHomEquiv (toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y) Y).symm (𝟙
        _) = toLeftDerivedAdjunctionData.{u, v}.adjunction.counit.app Y :=
  QuillenCarrierLocalization.transportedHomCounit
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps Y

/-- The actual Left transported unit and counit satisfy the full left triangle. -/
theorem toLeftCarrierHom_leftTriangle (X : PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) :
    toLeftDerivedAdjunctionData.{u, v}.leftDerived.map (toLeftCarrierHomEquiv X
        (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X) (𝟙 _)) ≫
      (toLeftCarrierHomEquiv (toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj
          (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X))
        (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X)).symm (𝟙 _) = 𝟙
            (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj X) :=
  QuillenCarrierLocalization.transportedHomLeftTriangle
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps X

/-- The actual Left transported unit and counit satisfy the full right triangle. -/
theorem toLeftCarrierHom_rightTriangle (Y : originalLeftHo.{u, v}) :
    toLeftCarrierHomEquiv (toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y)
        (toLeftDerivedAdjunctionData.{u, v}.leftDerived.obj (toLeftDerivedAdjunctionData.{u,
            v}.rightDerived.obj Y)) (𝟙 _) ≫
      toLeftDerivedAdjunctionData.{u, v}.rightDerived.map ((toLeftCarrierHomEquiv
          (toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y) Y).symm (𝟙 _)) =
        𝟙 (toLeftDerivedAdjunctionData.{u, v}.rightDerived.obj Y) :=
  QuillenCarrierLocalization.transportedHomRightTriangle
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
      toRight_allWeakMaps Y

end PointedCGWH.Spectra.Symmetric.LeftRightNativeModel.Canonical
