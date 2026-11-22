/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.LeftRightConversion
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.StandardDerivedFreeComparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Factorization
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.EquivalenceComposition

/-!
# Original κ/I/J factorization data through the actual sphere-module conversion

Both original models use the same native cardinal data. The actual right-module/operator
equivalence is the original inverse conversion followed by the actual left-module/operator
equivalence. The existing composition theorem preserves every Z/i/p/fac and full Arrow map.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open CategoryTheory.MorphismProperty.FunctorialFactorizationData
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

namespace PointedCGWH.Spectra.Symmetric.LeftRightNativeModel

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

/-- The actual right operator equivalence is the complete original two-stage composition. -/
theorem rightOperatorEquivalence_eq :
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v} =
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm.trans
        SymmetricModulePresentation.moduleOperatorEquivalence.{u, v} := rfl

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

/-- The original κ/I right middle functor is exactly the full iterated left-to-right route. -/
theorem rightCofibrantData_iterated_Z :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z =
      (((EnrichedProjective.Native.cofibrantFactorizationData
        (A := SymmetricOperatorIndex.{u, v})).ofEquivalence
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).ofEquivalence
            SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).Z := by
  exact (ofEquivalence_trans_Z
    (EnrichedProjective.Native.cofibrantFactorizationData (A := SymmetricOperatorIndex.{u, v}))
    SymmetricRightModulePresentation.sphereModuleEquivalence.symm
    SymmetricModulePresentation.moduleOperatorEquivalence).symm

/-- The original κ/J right middle functor retains the whole original left-to-right route. -/
theorem rightFibrantData_iterated_Z :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z =
      (((EnrichedProjective.Native.fibrantFactorizationData
        (A := SymmetricOperatorIndex.{u, v})).ofEquivalence
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).ofEquivalence
            SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).Z := by
  exact (ofEquivalence_trans_Z
    (EnrichedProjective.Native.fibrantFactorizationData (A := SymmetricOperatorIndex.{u, v}))
    SymmetricRightModulePresentation.sphereModuleEquivalence.symm
    SymmetricModulePresentation.moduleOperatorEquivalence).symm

/-- Every original right κ/I left component is the same entire iterated component. -/
theorem rightCofibrantData_iterated_i
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f =
      (((EnrichedProjective.Native.cofibrantFactorizationData
        (A := SymmetricOperatorIndex.{u, v})).ofEquivalence
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).ofEquivalence
            SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).i.app f := by
  exact (ofEquivalence_trans_i
    (EnrichedProjective.Native.cofibrantFactorizationData (A := SymmetricOperatorIndex.{u, v}))
    SymmetricRightModulePresentation.sphereModuleEquivalence.symm
    SymmetricModulePresentation.moduleOperatorEquivalence f).symm

/-- Every entire κ/I middle map retains both original inverses and the complete Arrow square. -/
theorem rightCofibrantData_iterated_Z_map
    {f g : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (φ : f ⟶ g) :
    let c := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    let e := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ =
      c.functor.map (e.inverse.map
        ((EnrichedProjective.Native.cofibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).Z.map
            (e.functor.mapArrow.map (c.inverse.mapArrow.map φ)))) := rfl

/-- The whole original κ/J middle square keeps both exact original inverse conversion stages. -/
theorem rightFibrantData_iterated_Z_map
    {f g : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (φ : f ⟶ g) :
    let c := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    let e := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ =
      c.functor.map (e.inverse.map
        ((EnrichedProjective.Native.fibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).Z.map
            (e.functor.mapArrow.map (c.inverse.mapArrow.map φ)))) := rfl

/-- The actual κ/I first component retains both original units and the whole native component. -/
theorem rightCofibrantData_original_i
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    let c := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    let e := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f =
      c.counitIso.inv.app f.left ≫ c.functor.map
        (e.unitIso.hom.app (c.inverse.obj f.left) ≫ e.inverse.map
          ((EnrichedProjective.Native.cofibrantFactorizationData
            (A := SymmetricOperatorIndex.{u, v})).i.app
              (e.functor.mapArrow.obj (c.inverse.mapArrow.obj f)))) := by
  dsimp only
  rw [rightCofibrantData_iterated_i]
  exact ofEquivalence_trans_i_explicit _ _ _ f

/-- The unchanged actual κ/I factors retain the entire original caller arrow. -/
theorem rightCofibrantData_original_fac
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f = f.hom :=
  RightPresentationModel.cofibrantFactorizationData_fac f

/-- The unchanged actual κ/J factors recover every entire original caller arrow. -/
theorem rightFibrantData_original_fac
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f = f.hom :=
  RightPresentationModel.fibrantFactorizationData_fac f

/-- The full original κ/I right component is retained through both actual inverse units. -/
theorem rightCofibrantData_iterated_p
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f =
      (((EnrichedProjective.Native.cofibrantFactorizationData
        (A := SymmetricOperatorIndex.{u, v})).ofEquivalence
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).ofEquivalence
            SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).p.app f := by
  exact (ofEquivalence_trans_p
    (EnrichedProjective.Native.cofibrantFactorizationData (A := SymmetricOperatorIndex.{u, v}))
    SymmetricRightModulePresentation.sphereModuleEquivalence.symm
    SymmetricModulePresentation.moduleOperatorEquivalence f).symm

/-- Every original right κ/J left component keeps the exact complete original source component. -/
theorem rightFibrantData_iterated_i
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f =
      (((EnrichedProjective.Native.fibrantFactorizationData
        (A := SymmetricOperatorIndex.{u, v})).ofEquivalence
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).ofEquivalence
            SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).i.app f := by
  exact (ofEquivalence_trans_i
    (EnrichedProjective.Native.fibrantFactorizationData (A := SymmetricOperatorIndex.{u, v}))
    SymmetricRightModulePresentation.sphereModuleEquivalence.symm
    SymmetricModulePresentation.moduleOperatorEquivalence f).symm

/-- The actual κ/J right component preserves both full original inverse-unit stages. -/
theorem rightFibrantData_iterated_p
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f =
      (((EnrichedProjective.Native.fibrantFactorizationData
        (A := SymmetricOperatorIndex.{u, v})).ofEquivalence
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).ofEquivalence
            SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).p.app f := by
  exact (ofEquivalence_trans_p
    (EnrichedProjective.Native.fibrantFactorizationData (A := SymmetricOperatorIndex.{u, v}))
    SymmetricRightModulePresentation.sphereModuleEquivalence.symm
    SymmetricModulePresentation.moduleOperatorEquivalence f).symm

/-- The entire original κ/I projection retains the full original inverse-unit stages. -/
theorem rightCofibrantData_original_p
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    let c := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    let e := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f =
      c.functor.map (e.inverse.map
        ((EnrichedProjective.Native.cofibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).p.app
            (e.functor.mapArrow.obj (c.inverse.mapArrow.obj f))) ≫
          e.unitIso.inv.app (c.inverse.obj f.right)) ≫ c.counitIso.hom.app f.right := by
  dsimp only
  rw [rightCofibrantData_iterated_p]
  exact ofEquivalence_trans_p_explicit _ _ _ f

/-- The full original κ/I middle comparison uses both actual original equivalence counits. -/
def rightCofibrantDataNativeMiddleIso :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z ⋙
      SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor ≅
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor.mapArrow ⋙
          (EnrichedProjective.Native.cofibrantFactorizationData
            (A := SymmetricOperatorIndex.{u, v})).Z :=
  (EnrichedProjective.Native.cofibrantFactorizationData
    (A := SymmetricOperatorIndex.{u, v})).ofEquivalenceTransComparisonIso
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

/-- The actual whole κ/J middle comparison retains both supplied original counits. -/
def rightFibrantDataNativeMiddleIso :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z ⋙
      SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor ≅
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor.mapArrow ⋙
          (EnrichedProjective.Native.fibrantFactorizationData
            (A := SymmetricOperatorIndex.{u, v})).Z :=
  (EnrichedProjective.Native.fibrantFactorizationData
    (A := SymmetricOperatorIndex.{u, v})).ofEquivalenceTransComparisonIso
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

/-- The full κ/I comparison keeps the original conversion unit and original operator counit. -/
theorem rightCofibrantData_nativeMiddle_hom
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    let c := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    let e := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    let z := (EnrichedProjective.Native.cofibrantFactorizationData
      (A := SymmetricOperatorIndex.{u, v})).Z.obj
        (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.obj f)
    rightCofibrantDataNativeMiddleIso.{u, v}.hom.app f =
      e.functor.map (c.unitIso.inv.app (e.inverse.obj z)) ≫ e.counitIso.hom.app z :=
  ofEquivalenceTransComparisonIso_hom_app _ _ _ f

/-- Both complete original inverse counits are retained by the κ/I inverse middle map. -/
theorem rightCofibrantData_nativeMiddle_inv
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    let c := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    let e := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    let z := (EnrichedProjective.Native.cofibrantFactorizationData
      (A := SymmetricOperatorIndex.{u, v})).Z.obj
        (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.obj f)
    rightCofibrantDataNativeMiddleIso.{u, v}.inv.app f =
      e.counitIso.inv.app z ≫ e.functor.map (c.unitIso.hom.app (e.inverse.obj z)) :=
  ofEquivalenceTransComparisonIso_inv_app _ _ _ f

/-- The actual κ/J comparison preserves the full original conversion and operator components. -/
theorem rightFibrantData_nativeMiddle_hom
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    let c := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    let e := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    let z := (EnrichedProjective.Native.fibrantFactorizationData
      (A := SymmetricOperatorIndex.{u, v})).Z.obj
        (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.obj f)
    rightFibrantDataNativeMiddleIso.{u, v}.hom.app f =
      e.functor.map (c.unitIso.inv.app (e.inverse.obj z)) ≫ e.counitIso.hom.app z :=
  ofEquivalenceTransComparisonIso_hom_app _ _ _ f

/-- The whole κ/J inverse middle component keeps both original inverse components. -/
theorem rightFibrantData_nativeMiddle_inv
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    let c := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    let e := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    let z := (EnrichedProjective.Native.fibrantFactorizationData
      (A := SymmetricOperatorIndex.{u, v})).Z.obj
        (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.obj f)
    rightFibrantDataNativeMiddleIso.{u, v}.inv.app f =
      e.counitIso.inv.app z ≫ e.functor.map (c.unitIso.hom.app (e.inverse.obj z)) :=
  ofEquivalenceTransComparisonIso_inv_app _ _ _ f

/-- Every entire original Arrow square is preserved by the complete κ/I middle comparison. -/
theorem rightCofibrantData_nativeMiddle_naturality
    {f g : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (φ : f ⟶ g) :
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.map
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ) ≫
      rightCofibrantDataNativeMiddleIso.hom.app g =
        rightCofibrantDataNativeMiddleIso.hom.app f ≫
          (EnrichedProjective.Native.cofibrantFactorizationData
            (A := SymmetricOperatorIndex.{u, v})).Z.map
              (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.map
                φ) :=
  rightCofibrantDataNativeMiddleIso.hom.naturality φ

/-- The κ/J whole middle map retains naturality on every original complete Arrow square. -/
theorem rightFibrantData_nativeMiddle_naturality
    {f g : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (φ : f ⟶ g) :
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.map
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ) ≫
      rightFibrantDataNativeMiddleIso.hom.app g =
        rightFibrantDataNativeMiddleIso.hom.app f ≫
          (EnrichedProjective.Native.fibrantFactorizationData
            (A := SymmetricOperatorIndex.{u, v})).Z.map
              (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.map
                φ) :=
  rightFibrantDataNativeMiddleIso.hom.naturality φ

/-- The actual original left κ/I data, followed by conversion, gives the entire right middle. -/
theorem rightCofibrantData_actualLeft_Z :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z =
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).ofEquivalence
        SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).Z :=
  rightCofibrantData_iterated_Z

/-- The chosen original left κ/J data retains the whole right middle through actual conversion. -/
theorem rightFibrantData_actualLeft_Z :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z =
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).ofEquivalence
        SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).Z :=
  rightFibrantData_iterated_Z

/-- The whole κ/I first component comes from the SAME chosen original left factorization data. -/
theorem rightCofibrantData_actualLeft_i
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f =
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).ofEquivalence
        SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).i.app f :=
  rightCofibrantData_iterated_i f

/-- The whole κ/I projection uses the unchanged chosen original left factorization data. -/
theorem rightCofibrantData_actualLeft_p
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f =
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).ofEquivalence
        SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).p.app f :=
  rightCofibrantData_iterated_p f

/-- The entire κ/J first component is given by the actual original left factorization data. -/
theorem rightFibrantData_actualLeft_i
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f =
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).ofEquivalence
        SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).i.app f :=
  rightFibrantData_iterated_i f

/-- The entire κ/J projection retains the SAME chosen original left factorization data. -/
theorem rightFibrantData_actualLeft_p
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f =
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).ofEquivalence
        SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).p.app f :=
  rightFibrantData_iterated_p f

/-- The complete κ/J inclusion retains both original units and the whole native inclusion. -/
theorem rightFibrantData_original_i
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    let c := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    let e := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f =
      c.counitIso.inv.app f.left ≫ c.functor.map
        (e.unitIso.hom.app (c.inverse.obj f.left) ≫ e.inverse.map
          ((EnrichedProjective.Native.fibrantFactorizationData
            (A := SymmetricOperatorIndex.{u, v})).i.app
              (e.functor.mapArrow.obj (c.inverse.mapArrow.obj f)))) := by
  dsimp only
  rw [rightFibrantData_iterated_i]
  exact ofEquivalence_trans_i_explicit _ _ _ f

/-- The entire κ/J projection retains both original inverse units and the native projection. -/
theorem rightFibrantData_original_p
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    let c := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    let e := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f =
      c.functor.map (e.inverse.map
        ((EnrichedProjective.Native.fibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).p.app
            (e.functor.mapArrow.obj (c.inverse.mapArrow.obj f))) ≫
          e.unitIso.inv.app (c.inverse.obj f.right)) ≫ c.counitIso.hom.app f.right := by
  dsimp only
  rw [rightFibrantData_iterated_p]
  exact ofEquivalence_trans_p_explicit _ _ _ f

/-- The complete original κ/I inclusion is recovered by the actual native middle comparison. -/
theorem rightCofibrantData_nativeMiddle_mapped_i
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.map
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f) ≫
      rightCofibrantDataNativeMiddleIso.hom.app f =
        (EnrichedProjective.Native.cofibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).i.app
            (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.obj
              f) := by
  rw [rightCofibrantData_iterated_i]
  exact ofEquivalence_trans_mapped_i
    (EnrichedProjective.Native.cofibrantFactorizationData (A := SymmetricOperatorIndex.{u, v}))
    SymmetricRightModulePresentation.sphereModuleEquivalence.symm
    SymmetricModulePresentation.moduleOperatorEquivalence f

/-- The whole original κ/I projection is recovered by the SAME actual native middle comparison. -/
theorem rightCofibrantData_nativeMiddle_mapped_p
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    rightCofibrantDataNativeMiddleIso.hom.app f ≫
        (EnrichedProjective.Native.cofibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).p.app
            (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.obj
              f) =
      SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.map
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f) := by
  rw [rightCofibrantData_iterated_p]
  exact ofEquivalence_trans_mapped_p
    (EnrichedProjective.Native.cofibrantFactorizationData (A := SymmetricOperatorIndex.{u, v}))
    SymmetricRightModulePresentation.sphereModuleEquivalence.symm
    SymmetricModulePresentation.moduleOperatorEquivalence f

/-- Every whole κ/J inclusion is recovered by the unchanged actual native middle comparison. -/
theorem rightFibrantData_nativeMiddle_mapped_i
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.map
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f) ≫
      rightFibrantDataNativeMiddleIso.hom.app f =
        (EnrichedProjective.Native.fibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).i.app
            (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.obj
              f) := by
  rw [rightFibrantData_iterated_i]
  exact ofEquivalence_trans_mapped_i
    (EnrichedProjective.Native.fibrantFactorizationData (A := SymmetricOperatorIndex.{u, v}))
    SymmetricRightModulePresentation.sphereModuleEquivalence.symm
    SymmetricModulePresentation.moduleOperatorEquivalence f

/-- The complete κ/J projection retains the actual native comparison on the SAME original data. -/
theorem rightFibrantData_nativeMiddle_mapped_p
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    rightFibrantDataNativeMiddleIso.hom.app f ≫
        (EnrichedProjective.Native.fibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).p.app
            (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.obj
              f) =
      SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.map
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f) := by
  rw [rightFibrantData_iterated_p]
  exact ofEquivalence_trans_mapped_p
    (EnrichedProjective.Native.fibrantFactorizationData (A := SymmetricOperatorIndex.{u, v}))
    SymmetricRightModulePresentation.sphereModuleEquivalence.symm
    SymmetricModulePresentation.moduleOperatorEquivalence f

/-- Every original Arrow square retains inverse naturality for the full κ/I comparison. -/
theorem rightCofibrantData_nativeMiddle_inverse_naturality
    {f g : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (φ : f ⟶ g) :
    (EnrichedProjective.Native.cofibrantFactorizationData
        (A := SymmetricOperatorIndex.{u, v})).Z.map
          (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.map
            φ) ≫ rightCofibrantDataNativeMiddleIso.inv.app g =
      rightCofibrantDataNativeMiddleIso.inv.app f ≫
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.map
          (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ) :=
  rightCofibrantDataNativeMiddleIso.inv.naturality φ

/-- The complete κ/J inverse middle comparison is natural on every original Arrow square. -/
theorem rightFibrantData_nativeMiddle_inverse_naturality
    {f g : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (φ : f ⟶ g) :
    (EnrichedProjective.Native.fibrantFactorizationData
        (A := SymmetricOperatorIndex.{u, v})).Z.map
          (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.map
            φ) ≫ rightFibrantDataNativeMiddleIso.inv.app g =
      rightFibrantDataNativeMiddleIso.inv.app f ≫
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.map
          (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ) :=
  rightFibrantDataNativeMiddleIso.inv.naturality φ

/-- The whole original κ/I inclusion Arrow is compared using the SAME full native middle Iso. -/
def rightCofibrantDataNativeFirstArrowIso
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    CategoryTheory.Arrow.mk
        (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.map
          (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f)) ≅
      CategoryTheory.Arrow.mk
        ((EnrichedProjective.Native.cofibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).i.app
            (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.obj
              f)) :=
  CategoryTheory.Arrow.isoMk' _ _ (Iso.refl _) (rightCofibrantDataNativeMiddleIso.app f)
    (by simpa only [Iso.refl_hom, Category.id_comp, Iso.app_hom, Functor.comp_obj] using
      (rightCofibrantData_nativeMiddle_mapped_i f).symm)

/-- The entire original κ/I projection Arrow retains its actual native middle component. -/
def rightCofibrantDataNativeSecondArrowIso
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    CategoryTheory.Arrow.mk
        (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.map
          (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f)) ≅
      CategoryTheory.Arrow.mk
        ((EnrichedProjective.Native.cofibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).p.app
            (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.obj
              f)) :=
  CategoryTheory.Arrow.isoMk' _ _ (rightCofibrantDataNativeMiddleIso.app f) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.comp_id, Iso.app_hom, Functor.comp_obj] using
      rightCofibrantData_nativeMiddle_mapped_p f)

/-- The whole original κ/J inclusion Arrow uses the actual unchanged native middle comparison. -/
def rightFibrantDataNativeFirstArrowIso
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    CategoryTheory.Arrow.mk
        (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.map
          (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f)) ≅
      CategoryTheory.Arrow.mk
        ((EnrichedProjective.Native.fibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).i.app
            (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.obj
              f)) :=
  CategoryTheory.Arrow.isoMk' _ _ (Iso.refl _) (rightFibrantDataNativeMiddleIso.app f)
    (by simpa only [Iso.refl_hom, Category.id_comp, Iso.app_hom, Functor.comp_obj] using
      (rightFibrantData_nativeMiddle_mapped_i f).symm)

/-- The complete original κ/J projection Arrow keeps the SAME actual native middle Iso. -/
def rightFibrantDataNativeSecondArrowIso
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    CategoryTheory.Arrow.mk
        (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.map
          (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f)) ≅
      CategoryTheory.Arrow.mk
        ((EnrichedProjective.Native.fibrantFactorizationData
          (A := SymmetricOperatorIndex.{u, v})).p.app
            (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor.mapArrow.obj
              f)) :=
  CategoryTheory.Arrow.isoMk' _ _ (rightFibrantDataNativeMiddleIso.app f) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.comp_id, Iso.app_hom, Functor.comp_obj] using
      rightFibrantData_nativeMiddle_mapped_p f)

/-- The SAME original κ/I source factors keep the literal standard RIGHT I lifting class. -/
theorem rightCofibrantData_standard_original_classes
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    RightPresentationModel.standardBoundaryGenerators.{u, v}.rlp.llp
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f) ∧
      ∀ n : CategoryTheory.Operad.SmallFinBijGroupoid, trivialFibrations PointedCGWH.{u, v}
        ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f).hom.natTrans.app
          n) :=
  ⟨Eq.mp (congrArg (fun P : MorphismProperty PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} =>
      P (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f))
        RightPresentationModel.convertedStandardBoundaryGenerators_rlp_llp_eq)
      (RightPresentationModel.cofibrantFactorizationData_original_classes f).1,
    (RightPresentationModel.cofibrantFactorizationData_original_classes f).2⟩

/-- The SAME chosen κ/J factors preserve every standard RIGHT J label and full right level map. -/
theorem rightFibrantData_standard_original_classes
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    RightPresentationModel.standardHornGenerators.{u, v}.rlp.llp
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f) ∧
      ∀ n : CategoryTheory.Operad.SmallFinBijGroupoid, fibrations PointedCGWH.{u, v}
        ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f).hom.natTrans.app
          n) :=
  ⟨Eq.mp (congrArg (fun P : MorphismProperty PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} =>
      P (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f))
        RightPresentationModel.convertedStandardHornGenerators_rlp_llp_eq)
      (RightPresentationModel.fibrantFactorizationData_original_classes f).1,
    (RightPresentationModel.fibrantFactorizationData_original_classes f).2⟩

end PointedCGWH.Spectra.Symmetric.LeftRightNativeModel
