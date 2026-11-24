/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedSequentialPreserves

@[expose] public section

/-!
# Singular closed-sequential preservation clients

Public clients for all four sequential singular-preservation declarations at
an arbitrary universe. The preservation results remain explicit per-diagram
theorems; this test deliberately rejects a global inferred instance.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatSingularClosedSequentialPreservesTests

/-- Singular maps induced by injective TopCat maps are injective in each degree. -/
theorem injective_toSSet_map_app_of_injective_client
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Function.Injective f.hom)
    (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((TopCat.toSSet.map f).app n) :=
  TopCat.injective_toSSet_map_app_of_injective f hf n

/-- Injectivity of each singular colimit leg. -/
theorem injective_toSSet_leg_app_of_closedT1_client
    {F : ℕ ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    (j : ℕ) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((TopCat.toSSet.map (c.ι.app j)).app n) :=
  TopCat.injective_toSSet_leg_app_of_closedT1 c hc hF j n

/-- Pointwise preservation into the correctly sized `Type u`. -/
theorem preservesColimit_comp_evaluation_of_closedT1_client
    {F : ℕ ⥤ TopCat.{u}}
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    (n : SimplexCategoryᵒᵖ) :
    PreservesColimit F
      (TopCat.toSSet ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n) :=
  TopCat.preservesColimit_comp_evaluation_of_closedT1 hF n

/-- Per-diagram `toSSet` preservation. -/
theorem preservesColimit_toSSet_of_closedT1_client
    {F : ℕ ⥤ TopCat.{u}}
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f)) :
    PreservesColimit F TopCat.toSSet :=
  TopCat.preservesColimit_toSSet_of_closedT1 hF

/-- Concrete universe-one preservation. -/
theorem preservesColimit_toSSet_of_closedT1_universeOne_client
    {F : ℕ ⥤ TopCat.{1}}
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f)) :
    PreservesColimit F TopCat.toSSet :=
  TopCat.preservesColimit_toSSet_of_closedT1 hF

/-- Original universe-zero preservation. -/
theorem preservesColimit_toSSet_of_closedT1_universeZero_client
    {F : ℕ ⥤ TopCat.{0}}
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f)) :
    PreservesColimit F TopCat.toSSet :=
  TopCat.preservesColimit_toSSet_of_closedT1 hF

/-- The explicit hypothesis does not install global per-diagram preservation. -/
example {_F : ℕ ⥤ TopCat.{u}} : True := by
  fail_if_success
    let _ : PreservesColimit _F TopCat.toSSet := inferInstance
  trivial

#print axioms TopCat.injective_toSSet_map_app_of_injective
#print axioms TopCat.injective_toSSet_leg_app_of_closedT1
#print axioms TopCat.preservesColimit_comp_evaluation_of_closedT1
#print axioms TopCat.preservesColimit_toSSet_of_closedT1
#print axioms injective_toSSet_map_app_of_injective_client
#print axioms injective_toSSet_leg_app_of_closedT1_client
#print axioms preservesColimit_comp_evaluation_of_closedT1_client
#print axioms preservesColimit_toSSet_of_closedT1_client
#print axioms preservesColimit_toSSet_of_closedT1_universeOne_client
#print axioms preservesColimit_toSSet_of_closedT1_universeZero_client

end TopCatSingularClosedSequentialPreservesTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
