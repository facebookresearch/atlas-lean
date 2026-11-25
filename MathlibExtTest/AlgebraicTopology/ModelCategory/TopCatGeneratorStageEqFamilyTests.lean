/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorStageEq

/-!
# Uniform generator stage-equality client

Thin direct client restating `realizedGenerator_stage_eq` over
`TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions`: two
factorizations through stages of a filtered diagram with closed-embedding
transitions that agree in the colimit agree after passage to a common later
stage. Direct term application only; no new proof, and no presentability,
small-object, factorization, cofibration, weak-equivalence, or
model-structure claim.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits Topology

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatGeneratorStageEqFamilyTests

universe u v w

theorem realizedGenerator_stage_eq_client
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
    [Fact realizedGeneratorCardinal.{u}.IsRegular]
    [IsCardinalFiltered J realizedGeneratorCardinal.{u}]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    {A B : TopCat.{u}} (f : A ⟶ B)
    (hf : (TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions) f)
    {j₁ j₂ : J} (g₁ : A ⟶ F.obj j₁) (g₂ : A ⟶ F.obj j₂)
    (h : g₁ ≫ c.ι.app j₁ = g₂ ≫ c.ι.app j₂) :
    ∃ (k : J) (u : j₁ ⟶ k) (v : j₂ ⟶ k),
      g₁ ≫ F.map u = g₂ ≫ F.map v :=
  realizedGenerator_stage_eq c hc hF f hf g₁ g₂ h

theorem realizedGenerator_stage_eq_horn_client
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
    [Fact realizedGeneratorCardinal.{u}.IsRegular]
    [IsCardinalFiltered J realizedGeneratorCardinal.{u}]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    (n : ℕ) [NeZero n] (i : Fin (n + 1))
    {j₁ j₂ : J}
    (g₁ : SSet.toTop.{u}.obj (SSet.horn.{u} n i) ⟶ F.obj j₁)
    (g₂ : SSet.toTop.{u}.obj (SSet.horn.{u} n i) ⟶ F.obj j₂)
    (h : g₁ ≫ c.ι.app j₁ = g₂ ≫ c.ι.app j₂) :
    ∃ (k : J) (u : j₁ ⟶ k) (v : j₂ ⟶ k),
      g₁ ≫ F.map u = g₂ ≫ F.map v :=
  realizedGenerator_stage_eq c hc hF _
    (Or.inr (TopCat.horn_mem_realizedHornInclusions n i)) g₁ g₂ h

#print axioms realizedGenerator_stage_eq
#print axioms realizedGenerator_stage_eq_client
#print axioms realizedGenerator_stage_eq_horn_client

end TopCatGeneratorStageEqFamilyTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
