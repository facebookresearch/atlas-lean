/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedTransfiniteColimit

@[expose] public section

/-!
# Singular closed-transfinite-stage factorization clients

Public clients for compact-separable and singular-simplex factorization with
independent diagram, compact-source, and ambient universes. Concrete clients
pin raw universe-zero sources and simplices into a universe-one chain while
retaining the original universe-zero applications.
-/

set_option autoImplicit false

open CategoryTheory Limits Topology

universe w v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatSingularClosedTransfiniteColimitTests

variable {J : Type v} [LinearOrder J] [OrderBot J]

/-- Compact-separable stage factorization with three independent universes. -/
theorem exists_stage_of_compact_transfinite_client
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    {K : Type w} [TopologicalSpace K] [TopologicalSpace.SeparableSpace K]
    (hK : IsCompact (Set.univ : Set K)) (f : C(K, ↥c.pt)) :
    ∃ (j : J) (g : C(K, ↥(F.obj j))), (c.ι.app j).hom.comp g = f :=
  TopCat.exists_stage_of_compact_transfinite c hc hF hK f

/-- Singular-simplex stage factorization at arbitrary diagram/ambient levels. -/
theorem toSSet_stage_exists_transfinite_client
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    (n : SimplexCategoryᵒᵖ) (x : (TopCat.toSSet.obj c.pt).obj n) :
    ∃ (j : J) (y : (TopCat.toSSet.obj (F.obj j)).obj n),
      (TopCat.toSSet.map (c.ι.app j)).app n y = x :=
  TopCat.toSSet_stage_exists_transfinite c hc hF n x

section TypeZeroIntoUniverseOne

variable {J₁ : Type 1} [LinearOrder J₁] [OrderBot J₁]

/-- A raw universe-zero compact source factors through a universe-one chain. -/
theorem exists_stage_of_compact_transfinite_typeZero_to_universeOne_client
    {F : J₁ ⥤ TopCat.{1}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J₁⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    {K : Type} [TopologicalSpace K] [TopologicalSpace.SeparableSpace K]
    (hK : IsCompact (Set.univ : Set K)) (f : C(K, ↥c.pt)) :
    ∃ (j : J₁) (g : C(K, ↥(F.obj j))), (c.ι.app j).hom.comp g = f :=
  TopCat.exists_stage_of_compact_transfinite c hc hF hK f

/-- A raw standard simplex factors through a universe-one transfinite chain. -/
theorem toSSet_stage_exists_transfinite_universeOne_client
    {F : J₁ ⥤ TopCat.{1}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J₁⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    (n : SimplexCategoryᵒᵖ) (x : (TopCat.toSSet.obj c.pt).obj n) :
    ∃ (j : J₁) (y : (TopCat.toSSet.obj (F.obj j)).obj n),
      (TopCat.toSSet.map (c.ι.app j)).app n y = x :=
  TopCat.toSSet_stage_exists_transfinite c hc hF n x

end TypeZeroIntoUniverseOne

/-- Original universe-zero compact-separable application. -/
theorem exists_stage_of_compact_transfinite_universeZero_client
    {F : J ⥤ TopCat.{0}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    {K : Type} [TopologicalSpace K] [TopologicalSpace.SeparableSpace K]
    (hK : IsCompact (Set.univ : Set K)) (f : C(K, ↥c.pt)) :
    ∃ (j : J) (g : C(K, ↥(F.obj j))), (c.ι.app j).hom.comp g = f :=
  TopCat.exists_stage_of_compact_transfinite c hc hF hK f

/-- Original universe-zero singular-simplex application. -/
theorem toSSet_stage_exists_transfinite_universeZero_client
    {F : J ⥤ TopCat.{0}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    (n : SimplexCategoryᵒᵖ) (x : (TopCat.toSSet.obj c.pt).obj n) :
    ∃ (j : J) (y : (TopCat.toSSet.obj (F.obj j)).obj n),
      (TopCat.toSSet.map (c.ι.app j)).app n y = x :=
  TopCat.toSSet_stage_exists_transfinite c hc hF n x

#print axioms TopCat.exists_stage_of_compact_transfinite
#print axioms TopCat.toSSet_stage_exists_transfinite
#print axioms exists_stage_of_compact_transfinite_client
#print axioms toSSet_stage_exists_transfinite_client
#print axioms exists_stage_of_compact_transfinite_typeZero_to_universeOne_client
#print axioms toSSet_stage_exists_transfinite_universeOne_client
#print axioms exists_stage_of_compact_transfinite_universeZero_client
#print axioms toSSet_stage_exists_transfinite_universeZero_client

end TopCatSingularClosedTransfiniteColimitTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
