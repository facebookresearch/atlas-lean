/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization

/-!
# Original generated coefficient factory clients of the Reedy model

The original category, degree, boundary maps and coefficient factories are retained.
Only the actual latching and matching shape (co)limits used by these constructions
are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC uB vB uS vS uK vK

section ReedyPart1

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ReedyModel

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType] (d : CofibrantGenerationData C κ)

/-- The original selected fixed-cardinal source factories construct the
actual ordinary Reedy model. -/
@[instance_reducible]
def generatedModelCategory : ModelCategory (J ⥤ C) :=
  modelCategory r d.cofibrantFactorizationData d.fibrantFactorizationData

/-- The full generated Reedy cofibration factor retains the original selected
coefficient factory. -/
def generatedCofibrantFactorizationData :
    letI := generatedModelCategory r d
    FunctorialFactorizationData (cofibrations (J ⥤ C)) (trivialFibrations (J ⥤ C)) :=
  cofibrantFactorizationData r d.cofibrantFactorizationData d.fibrantFactorizationData

/-- The full generated Reedy fibration factor retains the original selected coefficient factory. -/
def generatedFibrantFactorizationData :
    letI := generatedModelCategory r d
    FunctorialFactorizationData (trivialCofibrations (J ⥤ C)) (fibrations (J ⥤ C)) :=
  fibrantFactorizationData r d.cofibrantFactorizationData d.fibrantFactorizationData

/-- Original source generation data constructs the same five classes and
both complete functorial factor records. -/
theorem generatedConstructs :
    letI := generatedModelCategory r d
    ∃ (c : FunctorialFactorizationData (cofibrations (J ⥤ C)) (trivialFibrations (J ⥤ C)))
      (f : FunctorialFactorizationData (trivialCofibrations (J ⥤ C)) (fibrations (J ⥤ C))),
      c = generatedCofibrantFactorizationData r d ∧ f = generatedFibrantFactorizationData r d ∧
      weakEquivalences (J ⥤ C) = (weakEquivalences C).functorCategory J ∧
      cofibrations (J ⥤ C) = CategoryTheory.ReedyStructure.latchingClass r (cofibrations C) ∧
      fibrations (J ⥤ C) = CategoryTheory.ReedyStructure.matchingClass r (fibrations C) ∧
      trivialCofibrations (J ⥤ C) =
        CategoryTheory.ReedyStructure.latchingClass r (trivialCofibrations C) ∧
      trivialFibrations (J ⥤ C) =
        CategoryTheory.ReedyStructure.matchingClass r (trivialFibrations C) :=
  constructs r d.cofibrantFactorizationData d.fibrantFactorizationData

end HomotopicalAlgebra.ReedyModel

end ReedyPart1
