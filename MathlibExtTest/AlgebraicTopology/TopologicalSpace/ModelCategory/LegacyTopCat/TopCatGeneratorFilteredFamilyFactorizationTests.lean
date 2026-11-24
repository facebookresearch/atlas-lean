/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorFilteredFamilyFactorization

/-!
# Uniform generator filtered-factorization client

Thin direct client restating `realizedGenerator_stage_exists`: every `TopCat`
map from a realized boundary/horn generator into the colimit of a filtered
diagram with closed-embedding transitions factors through some stage. No
separate boundary/horn wrapper, presentability, small-object,
factorization-system, cofibration, weak-equivalence, or model-structure claim.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits Topology

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatGeneratorFilteredFamilyFactorizationTests

universe u v w

theorem realizedGenerator_stage_exists_client
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
    [Fact realizedGeneratorCardinal.{u}.IsRegular]
    [IsCardinalFiltered J realizedGeneratorCardinal.{u}]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    {A B : TopCat.{u}} (f : A ⟶ B)
    (hf : (TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions) f)
    (g : A ⟶ c.pt) :
    ∃ (j : J) (g' : A ⟶ F.obj j), g' ≫ c.ι.app j = g :=
  realizedGenerator_stage_exists c hc hF f hf g

#print axioms realizedGenerator_stage_exists
#print axioms realizedGenerator_stage_exists_client

end TopCatGeneratorFilteredFamilyFactorizationTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
