/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.OriginalClasses
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.FreeEvaluation

/-!
# Actual original free/evaluation Quillen adjunctions

The source model is constructed from the actual native projective factory.
Complete natural evaluation comparisons then prove that the original source
adjunction is Quillen, retaining its actual functors and unit/counit.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]
  [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The ORIGINAL free/evaluation adjunction is Quillen for the constructed source model. -/
theorem originalFreeEvaluation_isQuillenAdjunction
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R) :
    let _ : ModelCategory C := modelCategory e
    adj.IsQuillenAdjunction := by
  let _ : ModelCategory C := modelCategory e
  apply CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    rw [fibrations_eq e] at hf
    have h := (EvaluationTransfer.evaluationProperty_iff
      (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations PointedCGWH.{u, v})
      (e.functor.map f)).mp hf a
    exact (mappedProperty_iso_iff (fibrations PointedCGWH.{u, v}) hR f).mp h
  · intro X Y f hf
    rw [trivialFibrations_eq e] at hf
    have h := (EvaluationTransfer.evaluationProperty_iff
      (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations PointedCGWH.{u, v})
      (e.functor.map f)).mp hf a
    exact (mappedProperty_iso_iff (trivialFibrations PointedCGWH.{u, v}) hR f).mp h

/-- The actual forward carrier adjunction preserves both left model classes. -/
theorem presentation_isQuillenAdjunction
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    let _ : ModelCategory C := modelCategory e
    e.toAdjunction.IsQuillenAdjunction := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  let _ : ModelCategory C := modelCategory e
  exact { preservesCofibrations := fun _ _ _ h => h
          preservesTrivialCofibrations := fun _ _ _ h => h }

/-- The actual inverse carrier adjunction preserves both right model classes. -/
theorem inversePresentation_isQuillenAdjunction
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    let _ : ModelCategory C := modelCategory e
    e.symm.toAdjunction.IsQuillenAdjunction := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  let _ : ModelCategory C := modelCategory e
  apply CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · exact fun _ _ _ h => h
  · exact fun _ _ _ h => h

end HomotopicalAlgebra.EnrichedProjective.NativePresentation
