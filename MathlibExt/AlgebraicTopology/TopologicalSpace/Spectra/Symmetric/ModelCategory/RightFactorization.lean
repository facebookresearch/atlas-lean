/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.RightModuleMigration
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.ClosedData

/-!
# Whole original-cardinal data in the actual RIGHT sphere-module presentation

The actual native I/J data, genuine module/operator inverse and its unit and
counit determine all fields. The original right Day action is preserved by
the computed first map, second map and every middle map of an Arrow square.
Closed-constructor comparisons use the same explicit original κ algorithm.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty MonoidalOpposite
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.RightPresentationModel

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

open SymmetricRightModulePresentation

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The whole actual κ/I first map uses the original right-carrier unit and inverse. -/
theorem cofibrantFactorizationData_i (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f =
      rightModuleOperatorEquivalence.unitIso.hom.app f.left ≫
        operatorToRightModule.map
          ((EnrichedProjective.Native.cofibrantFactorizationData
            (A := SymmetricOperatorIndex.{u, v})).i.app (rightModuleToOperator.mapArrow.obj f)) :=
  rfl

/-- The whole actual κ/I second map uses the original right inverse and unit inverse. -/
theorem cofibrantFactorizationData_p (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f =
      operatorToRightModule.map
        ((EnrichedProjective.Native.cofibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).p.app (rightModuleToOperator.mapArrow.obj f)) ≫
            rightModuleOperatorEquivalence.unitIso.inv.app f.right := rfl

/-- The whole actual κ/J first map uses the original right-carrier unit and inverse. -/
theorem fibrantFactorizationData_i (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f =
      rightModuleOperatorEquivalence.unitIso.hom.app f.left ≫
        operatorToRightModule.map
          ((EnrichedProjective.Native.fibrantFactorizationData
            (A := SymmetricOperatorIndex.{u, v})).i.app (rightModuleToOperator.mapArrow.obj f)) :=
  rfl

/-- The whole actual κ/J second map uses the original right inverse and unit inverse. -/
theorem fibrantFactorizationData_p (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f =
      operatorToRightModule.map
        ((EnrichedProjective.Native.fibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).p.app (rightModuleToOperator.mapArrow.obj f)) ≫
            rightModuleOperatorEquivalence.unitIso.inv.app f.right := rfl

/-- The actual original right equivalence counit compares the entire κ/I middle functor. -/
def cofibrantFactorizationZComparisonIso :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z ⋙ rightModuleToOperator ≅
      rightModuleToOperator.mapArrow ⋙
        (EnrichedProjective.Native.cofibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).Z :=
  EnrichedProjective.NativePresentation.cofibrantFactorizationDataZComparisonIso
    rightModuleOperatorEquivalence

/-- The actual original right equivalence counit compares the entire κ/J middle functor. -/
def fibrantFactorizationZComparisonIso :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z ⋙ rightModuleToOperator ≅
      rightModuleToOperator.mapArrow ⋙
        (EnrichedProjective.Native.fibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).Z :=
  EnrichedProjective.NativePresentation.fibrantFactorizationDataZComparisonIso
    rightModuleOperatorEquivalence

/-- The whole original κ/I first map recovers the same native map through the actual counit. -/
theorem cofibrantFactorizationData_mapped_i (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    rightModuleToOperator.map (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f) ≫
      cofibrantFactorizationZComparisonIso.hom.app f =
        (EnrichedProjective.Native.cofibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).i.app (rightModuleToOperator.mapArrow.obj f) :=
  EnrichedProjective.NativePresentation.cofibrantFactorizationData_mapped_i
    rightModuleOperatorEquivalence f

/-- The whole original κ/I second map recovers the same native map through the actual counit. -/
theorem cofibrantFactorizationData_mapped_p (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    cofibrantFactorizationZComparisonIso.hom.app f ≫
      (EnrichedProjective.Native.cofibrantFactorizationData
        (A := SymmetricOperatorIndex.{u, v})).p.app (rightModuleToOperator.mapArrow.obj f) =
          rightModuleToOperator.map
            (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f) :=
  EnrichedProjective.NativePresentation.cofibrantFactorizationData_mapped_p
    rightModuleOperatorEquivalence f

/-- The whole original κ/J first map recovers the same native map through the actual counit. -/
theorem fibrantFactorizationData_mapped_i (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    rightModuleToOperator.map (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f) ≫
      fibrantFactorizationZComparisonIso.hom.app f =
        (EnrichedProjective.Native.fibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).i.app (rightModuleToOperator.mapArrow.obj f) :=
  EnrichedProjective.NativePresentation.fibrantFactorizationData_mapped_i
    rightModuleOperatorEquivalence f

/-- The whole original κ/J second map recovers the same native map through the actual counit. -/
theorem fibrantFactorizationData_mapped_p (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    fibrantFactorizationZComparisonIso.hom.app f ≫
      (EnrichedProjective.Native.fibrantFactorizationData
        (A := SymmetricOperatorIndex.{u, v})).p.app (rightModuleToOperator.mapArrow.obj f) =
          rightModuleToOperator.map (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f) :=
  EnrichedProjective.NativePresentation.fibrantFactorizationData_mapped_p
    rightModuleOperatorEquivalence f

/-- The full original right κ/I middle functor is the same explicit closed-constructor algorithm. -/
theorem cofibrantFactorizationData_Z_closed :
  ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z =
    rightModuleToOperator.mapArrow ⋙
      (EnrichedProjective.Native.Construction.cofibrantFactorizationData
        (A := SymmetricOperatorIndex.{u, v})).Z ⋙ operatorToRightModule :=
  EnrichedProjective.NativePresentation.ClosedData.cofibrant_middle_functor_closed
    rightModuleOperatorEquivalence

/-- The full original right κ/J middle functor is the same explicit closed-constructor algorithm. -/
theorem fibrantFactorizationData_Z_closed :
  ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z =
    rightModuleToOperator.mapArrow ⋙
      (EnrichedProjective.Native.Construction.fibrantFactorizationData
        (A := SymmetricOperatorIndex.{u, v})).Z ⋙ operatorToRightModule :=
  HomotopicalAlgebra.EnrichedProjective.NativePresentation.ClosedData.fibrant_middle_functor_closed
    rightModuleOperatorEquivalence

omit B in
private theorem smul_comm {M N : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : M ⟶ N) :
    M.mod.smul ≫ f.hom = (f.hom ▷ sphereSequence.{u, v}) ≫ N.mod.smul :=
  f.isModHom.smul_hom

/-- The actual κ/I first map preserves the entire original RIGHT Day action. -/
theorem cofibrantFactorizationData_i_smul (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    f.left.mod.smul ≫ (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f).hom =
      ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f).hom ▷
        sphereSequence.{u, v}) ≫
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.obj f).mod.smul :=
  smul_comm _

/-- The actual κ/I second map preserves the entire original RIGHT Day action. -/
theorem cofibrantFactorizationData_p_smul (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.obj f).mod.smul ≫
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f).hom =
        ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f).hom ▷
          sphereSequence.{u, v}) ≫
          f.right.mod.smul := smul_comm _

/-- The actual κ/J first map preserves the entire original RIGHT Day action. -/
theorem fibrantFactorizationData_i_smul (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    f.left.mod.smul ≫ (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f).hom =
      ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f).hom ▷
        sphereSequence.{u, v}) ≫
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.obj f).mod.smul :=
  smul_comm _

/-- The actual κ/J second map preserves the entire original RIGHT Day action. -/
theorem fibrantFactorizationData_p_smul (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.obj f).mod.smul ≫
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f).hom =
        ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f).hom ▷
          sphereSequence.{u, v}) ≫
          f.right.mod.smul := smul_comm _

/-- Every entire κ/I middle map of an original square preserves the original right action. -/
theorem cofibrantFactorizationData_Z_map_smul
    {f g : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (φ : f ⟶ g) :
    (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.obj f).mod.smul ≫
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ).hom =
        ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ).hom ▷
          sphereSequence.{u, v}) ≫
          (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.obj g).mod.smul :=
            smul_comm _

/-- Every entire κ/J middle map of an original square preserves the original right action. -/
theorem fibrantFactorizationData_Z_map_smul
    {f g : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (φ : f ⟶ g) :
    (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.obj f).mod.smul ≫
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ).hom =
        ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ).hom ▷
          sphereSequence.{u, v}) ≫
          (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.obj g).mod.smul :=
            smul_comm _

end PointedCGWH.Spectra.Symmetric.RightPresentationModel
