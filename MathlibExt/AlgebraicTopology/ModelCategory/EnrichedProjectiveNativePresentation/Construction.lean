/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeDataComparison

/-!
# Original source models with the constructed native generator bottom

Use the existing constructed original bottom and the actual full source
equivalence. All five classes retain the original mapped arrows. The returned
source record agrees with the existing presentation model at every caller bottom.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation.Construction

attribute [local instance] Native.Construction.generatorOrderBot

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]

/-- Construct the source model from the same native original bottom and full equivalence. -/
@[instance_reducible]
def modelCategory (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : ModelCategory C :=
  NativePresentation.modelCategory e

/-- Source weak equivalences retain every original mapped evaluation. -/
theorem weakEquivalences_eq (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    weakEquivalences C =
      (EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a)
        (weakEquivalences PointedCGWH.{u, v})).inverseImage e.functor :=
  NativePresentation.weakEquivalences_eq e

/-- Source cofibrations retain the actual full native free-I class. -/
theorem cofibrations_eq (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    cofibrations C =
      ((generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp).inverseImage
        e.functor :=
  NativePresentation.cofibrations_eq e

/-- Source fibrations retain every original mapped evaluation. -/
theorem fibrations_eq (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    fibrations C =
      (EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a)
        (fibrations PointedCGWH.{u, v})).inverseImage e.functor :=
  NativePresentation.fibrations_eq e

/-- Source trivial fibrations retain all original mapped evaluation intersections. -/
theorem trivialFibrations_eq (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    trivialFibrations C =
      (EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a)
        (trivialFibrations PointedCGWH.{u, v})).inverseImage e.functor :=
  NativePresentation.trivialFibrations_eq e

/-- Source trivial cofibrations retain the actual full native free-J class. -/
theorem trivialCofibrations_eq (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    trivialCofibrations C =
      ((generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp).inverseImage
        e.functor :=
  NativePresentation.trivialCofibrations_eq e

/-- The weak class is the inverse image of the actual constructed native target. -/
theorem weakEquivalences_inverseImage (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.Construction.modelCategory
    let _ : ModelCategory C := modelCategory e
    weakEquivalences C =
      (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor := rfl

/-- The cofibration class is the inverse image of the actual constructed native target. -/
theorem cofibrations_inverseImage (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.Construction.modelCategory
    let _ : ModelCategory C := modelCategory e
    cofibrations C =
      (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor := rfl

/-- The fibration class is the inverse image of the actual constructed native target. -/
theorem fibrations_inverseImage (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.Construction.modelCategory
    let _ : ModelCategory C := modelCategory e
    fibrations C =
      (fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor := rfl

/-- Both intersections retain the complete actual target class. -/
theorem trivialFibrations_inverseImage (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.Construction.modelCategory
    let _ : ModelCategory C := modelCategory e
    trivialFibrations C =
      (trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor := rfl

/-- The complete trivial-cofibration class retains the actual constructed native target. -/
theorem trivialCofibrations_inverseImage (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.Construction.modelCategory
    let _ : ModelCategory C := modelCategory e
    trivialCofibrations C =
      (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor := rfl

/-- The actual constructed source/native carrier adjunction is Quillen. -/
theorem source_isQuillenAdjunction (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.Construction.modelCategory
    let _ : ModelCategory C := modelCategory e
    e.toAdjunction.IsQuillenAdjunction := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
    Native.Construction.modelCategory
  let _ : ModelCategory C := modelCategory e
  exact { preservesCofibrations := fun _ _ _ h => h,
          preservesTrivialCofibrations := fun _ _ _ h => h }

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The whole constructed source record agrees with the original model at every caller bottom. -/
theorem modelCategory_eq_existing (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    modelCategory e = NativePresentation.modelCategory e := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

end HomotopicalAlgebra.EnrichedProjective.NativePresentation.Construction
