/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceDayAction
public import MathlibExt.CategoryTheory.Enriched.SphereMonoidalDayTransformations

/-!
# Actual original sphere Day unit and multiplication arrows

The unit source is the same whole graded representable used by the original
Day constructor. Its map is the literal Yoneda extension of the original
sphere epsilon. Multiplication descends the actual original mu transformation
through the full continuous Day coend. These arrows retain all entire Hom
actions; the remaining native Day monoid laws are separate obligations.
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

/-- The exact original graded representable supplying the native Day tensor unit. -/
def dayUnitISpace : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex :=
  letI := OrthogonalIndex.category.{u, v}
  letI := OrthogonalIndex.monoidalCategory.{u, v}
  ⟨GradedYoneda.representable (V := PointedCGWH.{u, v}) (𝟙_ OrthogonalIndex)⟩

/-- Extend the literal original sphere epsilon through the actual graded Yoneda supplier. -/
def sphereDayUnit : dayUnitISpace.{u, v} ⟶ sphereISpace.{u, v} :=
  Enriched.SphereOperator.sphereUnitTransformation
    OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    orthogonalSphereMonoidalData.{u, v}

/-- The entire unit value is the original literal Yoneda extension call. -/
theorem sphereDayUnit_eq_original_extend :
    sphereDayUnit.{u, v} = GradedYoneda.extend (𝟙_ OrthogonalIndex)
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}.epsilon := rfl

/-- Each entire unit component is the original epsilon acting through the native sphere Hom. -/
theorem sphereDayUnit_component (k : OrthogonalIndex) :
    EnrichedFunctorCat.component sphereDayUnit.{u, v} k =
      GradedYoneda.component (𝟙_ OrthogonalIndex) orthogonalSphereFunctor.{u, v}
        orthogonalSphereMonoidalData.{u, v}.epsilon k :=
  Enriched.SphereOperator.sphereUnitTransformation_component
    OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    orthogonalSphereMonoidalData.{u, v} k

/-- The enriched identity computes precisely the selected original sphere epsilon. -/
theorem sphereDayUnit_original_epsilon :
    GradedYoneda.evaluate (𝟙_ OrthogonalIndex) orthogonalSphereFunctor.{u, v}
      sphereDayUnit.{u, v} = orthogonalSphereMonoidalData.{u, v}.epsilon :=
  Enriched.SphereOperator.sphereUnitTransformation_evaluate
    OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    orthogonalSphereMonoidalData.{u, v}

/-- The multiplication source is the original selected Day tensor of the entire sphere. -/
def sphereDayTensor : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex :=
  (EnrichedDayKernel.Input.bifunctor
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor).obj
      (sphereISpace.{u, v}, sphereISpace.{u, v})

/-- Descend the genuine original sphere tensorator through the entire native Day coend. -/
def sphereDayMultiply : sphereDayTensor.{u, v} ⟶ sphereISpace.{u, v} :=
  EnrichedDayKernel.ActionFromTransformation.transformation
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    orthogonalSphereFunctor.{u, v} orthogonalSphereFunctor.{u, v} orthogonalSphereFunctor.{u, v}
    (Enriched.SphereOperator.tensoratorTransformation
      OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
      orthogonalSphereMonoidalData.{u, v})

/-- Each entire multiplication component is the original selected continuous coend descent. -/
theorem sphereDayMultiply_component (k : OrthogonalIndex) :
    EnrichedFunctorCat.component sphereDayMultiply.{u, v} k =
      EnrichedDayKernel.ActionFromTransformation.desc
        OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
        orthogonalSphereFunctor.{u, v} orthogonalSphereFunctor.{u, v} orthogonalSphereFunctor.{u, v}
        (Enriched.SphereOperator.tensoratorTransformation
          OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
          orthogonalSphereMonoidalData.{u, v}) k :=
  EnrichedDayKernel.ActionFromTransformation.transformation_component
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    orthogonalSphereFunctor.{u, v} orthogonalSphereFunctor.{u, v} orthogonalSphereFunctor.{u, v}
    (Enriched.SphereOperator.tensoratorTransformation
      OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
      orthogonalSphereMonoidalData.{u, v}) k

/-- Every complete multiplication generator is the literal original mu and full sphere action. -/
theorem gen_sphereDayMultiply (k : OrthogonalIndex) (a : OrthogonalIndex × OrthogonalIndex) :
    EnrichedDayKernel.gen
        OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
        orthogonalSphereFunctor.{u, v} orthogonalSphereFunctor.{u, v} k a ≫
      EnrichedFunctorCat.component sphereDayMultiply.{u, v} k =
    (𝟙 (OrthogonalIndex.hom.{u, v} (a.1 + a.2) k) ⊗ₘ
      orthogonalSphereMonoidalData.{u, v}.mu a.1 a.2) ≫
        (β_ (OrthogonalIndex.hom.{u, v} (a.1 + a.2) k)
          (orthogonalSphereFunctor.{u, v}.obj (a.1 + a.2))).hom ≫
        MonoidalClosed.uncurry (orthogonalSphereFunctor.{u, v}.map (a.1 + a.2) k) :=
  (EnrichedDayKernel.ActionFromTransformation.gen_transformation
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    orthogonalSphereFunctor.{u, v} orthogonalSphereFunctor.{u, v} orthogonalSphereFunctor.{u, v}
    (Enriched.SphereOperator.tensoratorTransformation
      OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
      orthogonalSphereMonoidalData.{u, v}) k a).trans
    (congrArg (fun z =>
      (𝟙 (OrthogonalIndex.hom.{u, v} (a.1 + a.2) k) ⊗ₘ z) ≫
        (β_ (OrthogonalIndex.hom.{u, v} (a.1 + a.2) k)
          (orthogonalSphereFunctor.{u, v}.obj (a.1 + a.2))).hom ≫
        MonoidalClosed.uncurry (orthogonalSphereFunctor.{u, v}.map (a.1 + a.2) k))
      (Enriched.SphereOperator.tensoratorTransformation_component
        OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
        orthogonalSphereMonoidalData.{u, v} a))

/-- The entire output Hom acts naturally on the original descended multiplication. -/
theorem sphereDayMultiply_full_naturality (k l : OrthogonalIndex) :
    MonoidalClosed.uncurry (sphereDayTensor.{u, v}.toEnrichedFunctor.map k l) ≫
        EnrichedFunctorCat.component sphereDayMultiply.{u, v} l =
      (EnrichedFunctorCat.component sphereDayMultiply.{u, v} k ⊗ₘ
        𝟙 (k ⟶[PointedCGWH.{u, v}] l)) ≫
          MonoidalClosed.uncurry (orthogonalSphereFunctor.{u, v}.map k l) :=
  GradedNatTrans.uncurriedNaturality sphereDayMultiply.{u, v} k l

end CategoryTheory.Spectra.OrthogonalSourceRightModule
