/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorStageEq

/-!
# Generator stage-equality client

Thin direct client restating `realizedBoundary_stage_eq` and
`realizedHorn_stage_eq`: two factorizations through stages of a filtered
diagram with closed-embedding transitions that agree in the colimit agree
after passage to a common later stage. Direct term application only; no new
proof, and no
presentability, small-object, factorization, cofibration, weak-equivalence,
or model-structure claim.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits Topology

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatGeneratorStageEqTests

universe u v w

theorem realizedBoundary_stage_eq_client
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
    [Fact realizedGeneratorCardinal.{u}.IsRegular]
    [IsCardinalFiltered J realizedGeneratorCardinal.{u}]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    (n : ℕ) {j₁ j₂ : J}
    (g₁ : SSet.toTop.{u}.obj (SSet.boundary.{u} n) ⟶ F.obj j₁)
    (g₂ : SSet.toTop.{u}.obj (SSet.boundary.{u} n) ⟶ F.obj j₂)
    (h : g₁ ≫ c.ι.app j₁ = g₂ ≫ c.ι.app j₂) :
    ∃ (k : J) (u : j₁ ⟶ k) (v : j₂ ⟶ k),
      g₁ ≫ F.map u = g₂ ≫ F.map v :=
  realizedBoundary_stage_eq c hc hF n g₁ g₂ h

theorem realizedHorn_stage_eq_client
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
    [Fact realizedGeneratorCardinal.{u}.IsRegular]
    [IsCardinalFiltered J realizedGeneratorCardinal.{u}]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    (n : ℕ) (i : Fin (n + 1)) {j₁ j₂ : J}
    (g₁ : SSet.toTop.{u}.obj (SSet.horn.{u} n i) ⟶ F.obj j₁)
    (g₂ : SSet.toTop.{u}.obj (SSet.horn.{u} n i) ⟶ F.obj j₂)
    (h : g₁ ≫ c.ι.app j₁ = g₂ ≫ c.ι.app j₂) :
    ∃ (k : J) (u : j₁ ⟶ k) (v : j₂ ⟶ k),
      g₁ ≫ F.map u = g₂ ≫ F.map v :=
  realizedHorn_stage_eq c hc hF n i g₁ g₂ h

#print axioms realizedBoundary_stage_eq
#print axioms realizedHorn_stage_eq
#print axioms realizedBoundary_stage_eq_client
#print axioms realizedHorn_stage_eq_client

end TopCatGeneratorStageEqTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
