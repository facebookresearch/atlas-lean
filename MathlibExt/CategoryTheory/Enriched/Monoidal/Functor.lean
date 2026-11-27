/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic

/-!
# Enriched lax monoidal functors

Explicit lax, strong, and braided monoidal data for enriched functors between
categories carrying selected enriched monoidal structures.  This file installs
no global or scoped instances.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory.MonoidalCategory

universe uV vV uC vC uD vD

namespace CategoryTheory.EnrichedFunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [EnrichedOrdinaryCategory V C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
  [EnrichedOrdinaryCategory V D]

/-- Lax monoidal data on an enriched functor, including genuine hom-object
naturality of the tensorator. -/
structure LaxMonoidalData
    (dC : EnrichedMonoidalCategoryData V C)
    (dD : EnrichedMonoidalCategoryData V D)
    (F : EnrichedFunctor V C D) where
  /-- The lax unit map. -/
  epsilon : 𝟙_ D ⟶ F.obj (𝟙_ C)
  /-- The lax tensorator. -/
  mu : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)
  /-- The tensorator is natural on enriched hom objects. -/
  mu_naturality : ∀ X X' Y Y' : C,
    (F.map X X' ⊗ₘ F.map Y Y') ≫
          dD.tensorMap (F.obj X) (F.obj X') (F.obj Y) (F.obj Y') ≫
        eHomWhiskerLeft V (F.obj X ⊗ F.obj Y) (mu X' Y') =
      dC.tensorMap X X' Y Y' ≫ F.map (X ⊗ Y) (X' ⊗ Y') ≫
        eHomWhiskerRight V (mu X Y) (F.obj (X' ⊗ Y'))
  /-- The left and right unit coherences, in lax-monoidal orientation. -/
  unit : ∀ X : C,
    ((λ_ (F.obj X)).hom =
        epsilon ▷ F.obj X ≫ mu (𝟙_ C) X ≫
          (eHomEquiv V).symm
            (eHomEquiv V (λ_ X).hom ≫ F.map (𝟙_ C ⊗ X) X)) ∧
    ((ρ_ (F.obj X)).hom =
        F.obj X ◁ epsilon ≫ mu X (𝟙_ C) ≫
          (eHomEquiv V).symm
            (eHomEquiv V (ρ_ X).hom ≫ F.map (X ⊗ 𝟙_ C) X))
  /-- Associativity of the tensorator, in lax-monoidal orientation. -/
  assoc : ∀ X Y Z : C,
    mu X Y ▷ F.obj Z ≫ mu (X ⊗ Y) Z ≫
        (eHomEquiv V).symm
          (eHomEquiv V (α_ X Y Z).hom ≫
            F.map ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))) =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        F.obj X ◁ mu Y Z ≫ mu X (Y ⊗ Z)

/-- Strongness witnesses for existing enriched lax monoidal data. -/
structure StrongMonoidalData
    {dC : EnrichedMonoidalCategoryData V C}
    {dD : EnrichedMonoidalCategoryData V D}
    {F : EnrichedFunctor V C D}
    (l : LaxMonoidalData dC dD F) : Prop where
  /-- The lax unit map is an isomorphism. -/
  unitIso : IsIso l.epsilon
  /-- Every lax tensorator is an isomorphism. -/
  tensorIso : ∀ X Y : C, IsIso (l.mu X Y)

variable [BraidedCategory C] [BraidedCategory D]

/-- Braided compatibility for existing enriched lax monoidal data. -/
structure LaxBraidedData
    {dC : EnrichedMonoidalCategoryData V C}
    {dD : EnrichedMonoidalCategoryData V D}
    {F : EnrichedFunctor V C D}
    (l : LaxMonoidalData dC dD F) : Prop where
  /-- The tensorator intertwines the selected source and target braidings. -/
  braided : ∀ X Y : C,
    l.mu X Y ≫
        (eHomEquiv V).symm
          (eHomEquiv V (β_ X Y).hom ≫ F.map (X ⊗ Y) (Y ⊗ X)) =
      (β_ (F.obj X) (F.obj Y)).hom ≫ l.mu Y X

end CategoryTheory.EnrichedFunctor
