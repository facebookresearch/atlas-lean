/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedSequentialColimit

@[expose] public section

/-!
# Singular closed-sequential-stage factorization clients

Public clients for compact-source and singular-simplex stage factorization at
arbitrary universes. The source universe is independent of the ambient
`TopCat` universe; concrete clients pin a raw `Type 0` source into
`TopCat.{1}` and retain the original universe-zero applications.
-/

set_option autoImplicit false

open CategoryTheory Limits Topology

universe w u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatSingularClosedSequentialColimitTests

/-- Compact-source stage factorization with an independent source universe. -/
theorem exists_stage_of_compact_client
    {F : ℕ ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    {K : Type w} [TopologicalSpace K]
    (hK : IsCompact (Set.univ : Set K)) (f : C(K, ↥c.pt)) :
    ∃ (j : ℕ) (g : C(K, ↥(F.obj j))), (c.ι.app j).hom.comp g = f :=
  TopCat.exists_stage_of_compact c hc hF hK f

/-- Singular-simplex stage factorization at an arbitrary ambient universe. -/
theorem toSSet_stage_exists_client
    {F : ℕ ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    (n : SimplexCategoryᵒᵖ) (x : (TopCat.toSSet.obj c.pt).obj n) :
    ∃ (j : ℕ) (y : (TopCat.toSSet.obj (F.obj j)).obj n),
      (TopCat.toSSet.map (c.ι.app j)).app n y = x :=
  TopCat.toSSet_stage_exists c hc hF n x

/-- A raw universe-zero compact source factors through a `TopCat.{1}` chain. -/
theorem exists_stage_of_compact_typeZero_to_universeOne_client
    {F : ℕ ⥤ TopCat.{1}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    {K : Type} [TopologicalSpace K]
    (hK : IsCompact (Set.univ : Set K)) (f : C(K, ↥c.pt)) :
    ∃ (j : ℕ) (g : C(K, ↥(F.obj j))), (c.ι.app j).hom.comp g = f :=
  TopCat.exists_stage_of_compact c hc hF hK f

/-- Singular-simplex stage factorization for a `TopCat.{1}` chain. -/
theorem toSSet_stage_exists_universeOne_client
    {F : ℕ ⥤ TopCat.{1}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    (n : SimplexCategoryᵒᵖ) (x : (TopCat.toSSet.obj c.pt).obj n) :
    ∃ (j : ℕ) (y : (TopCat.toSSet.obj (F.obj j)).obj n),
      (TopCat.toSSet.map (c.ι.app j)).app n y = x :=
  TopCat.toSSet_stage_exists c hc hF n x

/-- Original universe-zero compact-source application. -/
theorem exists_stage_of_compact_universeZero_client
    {F : ℕ ⥤ TopCat.{0}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    {K : Type} [TopologicalSpace K]
    (hK : IsCompact (Set.univ : Set K)) (f : C(K, ↥c.pt)) :
    ∃ (j : ℕ) (g : C(K, ↥(F.obj j))), (c.ι.app j).hom.comp g = f :=
  TopCat.exists_stage_of_compact c hc hF hK f

/-- Original universe-zero singular-simplex application. -/
theorem toSSet_stage_exists_universeZero_client
    {F : ℕ ⥤ TopCat.{0}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f))
    (n : SimplexCategoryᵒᵖ) (x : (TopCat.toSSet.obj c.pt).obj n) :
    ∃ (j : ℕ) (y : (TopCat.toSSet.obj (F.obj j)).obj n),
      (TopCat.toSSet.map (c.ι.app j)).app n y = x :=
  TopCat.toSSet_stage_exists c hc hF n x

#print axioms TopCat.exists_stage_of_compact
#print axioms TopCat.toSSet_stage_exists
#print axioms exists_stage_of_compact_client
#print axioms toSSet_stage_exists_client
#print axioms exists_stage_of_compact_typeZero_to_universeOne_client
#print axioms toSSet_stage_exists_universeOne_client
#print axioms exists_stage_of_compact_universeZero_client
#print axioms toSSet_stage_exists_universeZero_client

end TopCatSingularClosedSequentialColimitTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
