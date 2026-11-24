/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedTransfinitePreserves

@[expose] public section

/-!
# Singular closed-transfinite preservation clients

Public clients for all three transfinite singular-preservation declarations
at independent diagram and ambient universes. Preservation remains an
explicit per-diagram theorem: both per-diagram and shape-wide inferred
instances are deliberately rejected.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatSingularClosedTransfinitePreservesTests

variable {J : Type v} [LinearOrder J] [OrderBot J]

/-- Injectivity of each transfinite singular colimit leg. -/
theorem injective_toSSet_leg_app_of_closedT1_transfinite_client
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    (j : J) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((TopCat.toSSet.map (c.ι.app j)).app n) :=
  TopCat.injective_toSSet_leg_app_of_closedT1_transfinite c hc hF j n

/-- Pointwise transfinite preservation into the correctly sized `Type u`. -/
theorem preservesColimit_comp_evaluation_of_closedT1_transfinite_client
    {F : J ⥤ TopCat.{u}}
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    (n : SimplexCategoryᵒᵖ) :
    PreservesColimit F
      (TopCat.toSSet ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n) :=
  TopCat.preservesColimit_comp_evaluation_of_closedT1_transfinite hF n

/-- Per-diagram transfinite `toSSet` preservation. -/
theorem preservesColimit_toSSet_of_closedT1_transfinite_client
    {F : J ⥤ TopCat.{u}}
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f)) :
    PreservesColimit F TopCat.toSSet :=
  TopCat.preservesColimit_toSSet_of_closedT1_transfinite hF

section UniverseOne

variable {J₁ : Type 1} [LinearOrder J₁] [OrderBot J₁]

/-- Concrete universe-one transfinite preservation. -/
theorem preservesColimit_toSSet_of_closedT1_transfinite_universeOne_client
    {F : J₁ ⥤ TopCat.{1}}
    (hF : ∀ ⦃i j : J₁⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f)) :
    PreservesColimit F TopCat.toSSet :=
  TopCat.preservesColimit_toSSet_of_closedT1_transfinite hF

end UniverseOne

/-- Original universe-zero transfinite preservation. -/
theorem preservesColimit_toSSet_of_closedT1_transfinite_universeZero_client
    {F : J ⥤ TopCat.{0}}
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f)) :
    PreservesColimit F TopCat.toSSet :=
  TopCat.preservesColimit_toSSet_of_closedT1_transfinite hF

/-- No per-diagram or shape-wide preservation dictionary is installed. -/
example {_F : J ⥤ TopCat.{u}} : True := by
  fail_if_success
    let _ : PreservesColimit _F TopCat.toSSet := inferInstance
  fail_if_success
    let _ : PreservesColimitsOfShape J TopCat.toSSet := inferInstance
  trivial

#print axioms TopCat.injective_toSSet_leg_app_of_closedT1_transfinite
#print axioms TopCat.preservesColimit_comp_evaluation_of_closedT1_transfinite
#print axioms TopCat.preservesColimit_toSSet_of_closedT1_transfinite
#print axioms injective_toSSet_leg_app_of_closedT1_transfinite_client
#print axioms preservesColimit_comp_evaluation_of_closedT1_transfinite_client
#print axioms preservesColimit_toSSet_of_closedT1_transfinite_client
#print axioms preservesColimit_toSSet_of_closedT1_transfinite_universeOne_client
#print axioms preservesColimit_toSSet_of_closedT1_transfinite_universeZero_client

end TopCatSingularClosedTransfinitePreservesTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
