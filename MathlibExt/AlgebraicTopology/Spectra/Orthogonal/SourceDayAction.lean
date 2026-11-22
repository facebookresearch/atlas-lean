/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceSphereTransformation
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.TransformationDescent
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Tensor

/-!
# The original continuous native Day action

The genuine original sphere transformation contracts the entire native Day
coend. Its output is the actual restricted continuous I-space. The tensor
object is the original selected Day bifunctor value, and its full enriched
output action is retained. Each contraction generator uses the original
sphere action and the full continuous restricted Hom action.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.OrthogonalSourceRightModule

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory
attribute [local instance] OrthogonalIndex.symmetricCategory
attribute [local instance] Enriched.prodCategory

/-- The original enriched representation sphere, wrapped as the genuine continuous I-space. -/
def sphereISpace : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex :=
  ⟨orthogonalSphereFunctor.{u, v}⟩

/-- The whole original selected right Day tensor of the restricted diagram and sphere. -/
def dayTensor
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :
    EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex :=
  (EnrichedDayKernel.Input.bifunctor
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor).obj
      (((restrictionFunctor.{u, v}).obj F), sphereISpace.{u, v})

/-- Its entire enriched output functor is the original selected Day kernel functor. -/
theorem dayTensor_functor
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :
    (dayTensor.{u, v} F).toEnrichedFunctor =
      EnrichedDayKernel.Output.functor
        OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
        ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor orthogonalSphereFunctor.{u, v} :=
  rfl

/-- The actual full continuous contraction family from the original sphere transformation. -/
def contractedDayGenerator
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (k : OrthogonalIndex) (a : OrthogonalIndex × OrthogonalIndex) :
    EnrichedDayKernel.objects
      OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
      ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor orthogonalSphereFunctor.{u, v} k a ⟶
        ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.obj k :=
  EnrichedDayKernel.ActionFromTransformation.generator
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor orthogonalSphereFunctor.{u, v}
    ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor (sphereTransformation.{u, v} F) k a

/-- Every entire contraction generator retains the literal original sphere and Hom actions. -/
theorem contractedDayGenerator_value
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (k : OrthogonalIndex) (a : OrthogonalIndex × OrthogonalIndex) :
    contractedDayGenerator.{u, v} F k a =
      (𝟙 (OrthogonalIndex.hom.{u, v} (a.1 + a.2) k) ⊗ₘ sphereAction.{u, v} F a.1 a.2) ≫
        (β_ (OrthogonalIndex.hom.{u, v} (a.1 + a.2) k)
          (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.obj (a.1 + a.2))).hom ≫
        MonoidalClosed.uncurry
          (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.map (a.1 + a.2) k) := by
  exact congrArg (fun z =>
    (𝟙 (OrthogonalIndex.hom.{u, v} (a.1 + a.2) k) ⊗ₘ z) ≫
      (β_ (OrthogonalIndex.hom.{u, v} (a.1 + a.2) k)
        (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.obj (a.1 + a.2))).hom ≫
      MonoidalClosed.uncurry
        (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.map (a.1 + a.2) k))
      (sphereTransformation_component.{u, v} F a)

/-- The complete descended right Day action is a genuine native enriched transformation. -/
def dayAction
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :
    dayTensor.{u, v} F ⟶ (restrictionFunctor.{u, v}).obj F :=
  EnrichedDayKernel.ActionFromTransformation.transformation
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor orthogonalSphereFunctor.{u, v}
    ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor (sphereTransformation.{u, v} F)

/-- The ordinary action component is the original whole continuous Day coend descent. -/
theorem dayAction_component
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (k : OrthogonalIndex) :
    EnrichedFunctorCat.component (dayAction.{u, v} F) k =
      EnrichedDayKernel.ActionFromTransformation.desc
        OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
        ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor orthogonalSphereFunctor.{u, v}
        ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor (sphereTransformation.{u, v} F) k :=
  EnrichedDayKernel.ActionFromTransformation.transformation_component
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor orthogonalSphereFunctor.{u, v}
    ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor (sphereTransformation.{u, v} F) k

/-- The original Day generators determine the entire native action component. -/
theorem gen_dayAction_component
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (k : OrthogonalIndex) (a : OrthogonalIndex × OrthogonalIndex) :
    EnrichedDayKernel.gen
        OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
        ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor orthogonalSphereFunctor.{u, v} k a ≫
      EnrichedFunctorCat.component (dayAction.{u, v} F) k =
        contractedDayGenerator.{u, v} F k a := by
  rw [dayAction_component]
  exact EnrichedDayKernel.ActionFromTransformation.gen_desc
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor orthogonalSphereFunctor.{u, v}
    ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor (sphereTransformation.{u, v} F) k a

/-- The full native output Hom acts naturally on the entire descended right action. -/
theorem dayAction_full_naturality
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (k l : OrthogonalIndex) :
    MonoidalClosed.uncurry ((dayTensor.{u, v} F).toEnrichedFunctor.map k l) ≫
        EnrichedFunctorCat.component (dayAction.{u, v} F) l =
      (EnrichedFunctorCat.component (dayAction.{u, v} F) k ⊗ₘ
        𝟙 (k ⟶[PointedCGWH.{u, v}] l)) ≫ MonoidalClosed.uncurry
          (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.map k l) :=
  GradedNatTrans.uncurriedNaturality (dayAction.{u, v} F) k l

end CategoryTheory.Spectra.OrthogonalSourceRightModule
