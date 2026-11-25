/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorFilteredFactorization

/-!
# Boundary generator filtered-factorization client

Thin direct client restating `realizedBoundary_stage_exists`: every `TopCat` map
from a realized boundary into the colimit of a filtered diagram with
closed-embedding transitions factors through some stage. No horn wrapper,
presentability, arbitrary filtered-colimit preservation, small-object,
factorization-system, cofibration, weak-equivalence, or model-structure claim.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits Topology

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatGeneratorFilteredFactorizationBoundaryTests

universe u v w

theorem realizedBoundary_stage_exists_client
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
    [Fact realizedGeneratorCardinal.{u}.IsRegular]
    [IsCardinalFiltered J realizedGeneratorCardinal.{u}]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    (n : ℕ) (f : SSet.toTop.{u}.obj (SSet.boundary.{u} n) ⟶ c.pt) :
    ∃ (j : J) (g : SSet.toTop.{u}.obj (SSet.boundary.{u} n) ⟶ F.obj j),
      g ≫ c.ι.app j = f :=
  realizedBoundary_stage_exists c hc hF n f

#check @realizedBoundary_stage_exists
#print axioms realizedBoundary_stage_exists
#print axioms realizedBoundary_stage_exists_client

end TopCatGeneratorFilteredFactorizationBoundaryTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
