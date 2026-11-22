/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorReconstructionDescent
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceSphereTransformation

/-!
# Original native operator fields from genuine continuous sphere transformations

The actual original orthogonal coend supplies every native Hom action and
every curried field. Restricting an original operator diagram and selecting
its original sphere transformation recovers its entire native map function.
The genuine canonical right-module carrier supplies the remaining source
unit and associativity laws for assembling the reverse enriched functor.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.OrthogonalSourceRightModule

open Enriched Enriched.SphereOperator

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory
attribute [local instance] OrthogonalIndex.symmetricCategory
attribute [local instance] Enriched.prodCategory

variable (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  (t : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
    (X.toEnrichedFunctor.externalTensor orthogonalSphereFunctor.{u, v})
    (OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
      PointedCGWH.{u, v} X.toEnrichedFunctor))

/-- The actual whole native coend action uses every original continuous generator. -/
def reverseOperatorAction (n k : OrthogonalIndex) :
    X.toEnrichedFunctor.obj n ⊗ OrthogonalOperatorIndex.hom.{u, v} n k ⟶
      X.toEnrichedFunctor.obj k :=
  Reconstruction.coendAction OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t PointedCGWH.isSeparator_tensorUnit n k

/-- Every actual native Hom field is the curry of the same original mapped-coend action. -/
def reverseOperatorMapField (n k : OrthogonalIndex) :
    OrthogonalOperatorIndex.hom.{u, v} n k ⟶
      (ihom (X.toEnrichedFunctor.obj n)).obj (X.toEnrichedFunctor.obj k) :=
  Reconstruction.enrichedMapField OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t PointedCGWH.isSeparator_tensorUnit n k

/-- The complete native field function is the original literal all-index supplier application. -/
theorem reverseOperatorMapField_eq_original_function :
    reverseOperatorMapField.{u, v} X t = fun n k => MonoidalClosed.curry
      (weightedCoend.Mapped.desc
        (weight OrthogonalIndex.enrichedMonoidalData.{u, v} n k) orthogonalSphereFunctor.{u, v}
        (tensorLeft (X.toEnrichedFunctor.obj n))
        (Reconstruction.generator OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n k)
        (Reconstruction.generator_balanced OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t
            PointedCGWH.isSeparator_tensorUnit n k)) :=
  Reconstruction.enrichedMapField_eq_original_function OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t PointedCGWH.isSeparator_tensorUnit

/-- Every full original native generator has its genuine reconstructed coefficient value. -/
theorem reverseOperatorAction_generator (n k a : OrthogonalIndex) :
    (X.toEnrichedFunctor.obj n ◁ OrthogonalOperatorIndex.ι.{u, v} n k a) ≫
        reverseOperatorAction.{u, v} X t n k =
      Reconstruction.generator OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n k a :=
  Reconstruction.gen_coendAction OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t PointedCGWH.isSeparator_tensorUnit n k a

/-- The actual genuine sphere coefficient is the same original recovered source coefficient. -/
theorem reverseCoefficient_original
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n a : OrthogonalIndex) :
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
        (sphereTransformation.{u, v} F) n a = coefficientFromRightSphere.{u, v} F n a := by
  have h : Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
      (sphereTransformation.{u, v} F) n a = sphereAction.{u, v} F n a :=
    sphereTransformation_component.{u, v} F (n, a)
  exact (congrArg (fun q => q ≫
    ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.toOrdinaryFunctor.map
      (β_ a n).inv) h).trans (coefficientFromRightSphere_value.{u, v} F n a).symm

/-- Each full original native operator generator is conserved by the genuine reverse builder. -/
theorem reverseGenerator_original
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n k a : OrthogonalIndex) :
    Reconstruction.generator OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
        (sphereTransformation.{u, v} F) n k a = recoveredGenerator.{u, v} F n k a := by
  let M := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)
  let H := OrthogonalIndex.hom.{u, v} (a + n) k
  let C := PointedCGWH.orthogonalSphere.{u, v} a
  let e := MonoidalClosed.uncurry
    (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.map (a + n) k)
  have h := congrArg (fun q => (M ◁ (β_ H C).hom) ≫ (α_ M C H).inv ≫ (q ▷ H) ≫ e)
    (reverseCoefficient_original.{u, v} F n a)
  exact h.trans (recoveredGenerator_value.{u, v} F n k a).symm

/-- The whole original native coend action is recovered from the actual source diagram. -/
theorem reverseOperatorAction_original_desc
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n k : OrthogonalIndex) :
    reverseOperatorAction.{u, v} ((restrictionFunctor.{u, v}).obj F)
        (sphereTransformation.{u, v} F) n k =
      weightedCoend.Mapped.desc
        (weight OrthogonalIndex.enrichedMonoidalData.{u, v} n k) orthogonalSphereFunctor.{u, v}
        (tensorLeft (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)))
        (recoveredGenerator.{u, v} F n k) (recoveredGenerator_balanced.{u, v} F n k) := by
  apply weightedCoend.Mapped.hom_ext
    (weight OrthogonalIndex.enrichedMonoidalData.{u, v} n k) orthogonalSphereFunctor.{u, v}
    (tensorLeft (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)))
  intro a
  exact (reverseOperatorAction_generator.{u, v} ((restrictionFunctor.{u, v}).obj F)
    (sphereTransformation.{u, v} F) n k a).trans
      ((reverseGenerator_original.{u, v} F n k a).trans
        (weightedCoend.Mapped.gen_desc
          (weight OrthogonalIndex.enrichedMonoidalData.{u, v} n k) orthogonalSphereFunctor.{u, v}
          (tensorLeft (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)))
          (recoveredGenerator.{u, v} F n k) (recoveredGenerator_balanced.{u, v} F n k) a).symm)

/-- Every entire original native enriched Hom map is conserved by the reverse builder. -/
theorem reverseOperatorMapField_original
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n k : OrthogonalIndex) :
    reverseOperatorMapField.{u, v} ((restrictionFunctor.{u, v}).obj F)
        (sphereTransformation.{u, v} F) n k =
      F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
        (OrthogonalOperatorIndex.ofIndex.{u, v} k) :=
  (congrArg MonoidalClosed.curry (reverseOperatorAction_original_desc.{u, v} F n k)).trans
    (full_operator_map_recovery.{u, v} F n k)

/-- The complete original native Hom function is conserved for every actual source diagram. -/
theorem reverseOperatorMapField_original_function :
    (fun (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
        n k => reverseOperatorMapField.{u, v} ((restrictionFunctor.{u, v}).obj F)
          (sphereTransformation.{u, v} F) n k) =
      fun (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) n k =>
        F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
          (OrthogonalOperatorIndex.ofIndex.{u, v} k) := by
  funext F n k
  exact reverseOperatorMapField_original.{u, v} F n k

end CategoryTheory.Spectra.OrthogonalSourceRightModule
