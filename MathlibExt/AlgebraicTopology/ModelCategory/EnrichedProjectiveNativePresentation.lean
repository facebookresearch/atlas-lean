/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative
import Mathlib.AlgebraicTopology.ModelCategory.Transport
import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily

/-!
# Native projective models on actual source presentations

The target model is constructed by the native generator-cardinal factory.
The source map classes are defined from that actual model through the supplied
complete carrier equivalence. No source or target model dictionary is a premise.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]
  [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The source weak class is the inverse image of the actual native weak class. -/
def weakProperty (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    MorphismProperty C :=
  (Native.modelCategory (A := A)).categoryWithWeakEquivalences.weakEquivalences.inverseImage
    e.functor

/-- The source cofibrations come from the actual canonical free-I model class. -/
def cofibrationProperty (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    MorphismProperty C :=
  (Native.modelCategory (A := A)).categoryWithCofibrations.cofibrations.inverseImage e.functor

/-- The source fibrations come from the actual native projective model. -/
def fibrationProperty (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    MorphismProperty C :=
  (Native.modelCategory (A := A)).categoryWithFibrations.fibrations.inverseImage e.functor

/-- Construct the complete original-presentation model from the actual native
model and the complete existing carrier equivalence. -/
@[instance_reducible]
def modelCategory (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    ModelCategory C := by
  letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  letI : CategoryWithCofibrations C := ⟨cofibrationProperty e⟩
  letI : CategoryWithFibrations C := ⟨fibrationProperty e⟩
  letI : CategoryWithWeakEquivalences C := ⟨weakProperty e⟩
  exact ModelCategory.transport e rfl rfl rfl

/-- The constructed source weak class retains its literal mapped source arrow. -/
theorem modelCategory_weakProperty (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (modelCategory e).categoryWithWeakEquivalences.weakEquivalences = weakProperty e := rfl

/-- The constructed source cofibration class retains the same literal map. -/
theorem modelCategory_cofibrationProperty (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (modelCategory e).categoryWithCofibrations.cofibrations = cofibrationProperty e := rfl

/-- The constructed source fibration class retains the same literal map. -/
theorem modelCategory_fibrationProperty (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (modelCategory e).categoryWithFibrations.fibrations = fibrationProperty e := rfl

/-- Source weak equivalences are exactly the original mapped native evaluations. -/
theorem weakEquivalences_eq (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    weakEquivalences C =
      (EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a)
        (weakEquivalences PointedCGWH.{u, v})).inverseImage e.functor := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  change (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor = _
  exact congrArg (fun P : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} A) =>
    P.inverseImage e.functor) (Native.weakEquivalences_eq (A := A))

/-- Source cofibrations are the inverse image of the actual free-I left class. -/
theorem cofibrations_eq (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    cofibrations C =
      ((generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp).inverseImage
        e.functor := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  change (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor = _
  exact congrArg (fun P : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} A) =>
    P.inverseImage e.functor) (Native.cofibrations_eq (A := A))

/-- Source fibrations retain all actual original mapped evaluations. -/
theorem fibrations_eq (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    fibrations C =
      (EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a)
        (fibrations PointedCGWH.{u, v})).inverseImage e.functor := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  change (fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor = _
  exact congrArg (fun P : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} A) =>
    P.inverseImage e.functor) (Native.fibrations_eq (A := A))

/-- The two source intersections are literally inverse images of native intersections. -/
theorem trivialFibrations_inverseImage (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    let _ : ModelCategory C := modelCategory e
    trivialFibrations C =
      (trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor := rfl

/-- Source trivial fibrations are the actual original mapped level intersection. -/
theorem trivialFibrations_eq (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    trivialFibrations C =
      (EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a)
        (trivialFibrations PointedCGWH.{u, v})).inverseImage e.functor := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  change (trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor = _
  exact congrArg (fun P : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} A) =>
    P.inverseImage e.functor) (Native.trivialFibrations_eq (A := A))

/-- Source trivial cofibrations retain the same mapped native whole arrow. -/
theorem trivialCofibrations_inverseImage (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    let _ : ModelCategory C := modelCategory e
    trivialCofibrations C =
      (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor := rfl

/-- Source trivial cofibrations come from the original full free-J left class. -/
theorem trivialCofibrations_eq (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    trivialCofibrations C =
      ((generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp).inverseImage
        e.functor := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  change (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor = _
  exact congrArg (fun P : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} A) =>
    P.inverseImage e.functor) (Native.trivialCofibrations_eq (A := A))

end HomotopicalAlgebra.EnrichedProjective.NativePresentation
