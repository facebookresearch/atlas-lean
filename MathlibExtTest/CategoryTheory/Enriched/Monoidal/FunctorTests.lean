/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.Monoidal.Functor

set_option autoImplicit false

noncomputable section

open CategoryTheory.MonoidalCategory

universe uV vV uC vC uD vD

namespace CategoryTheory.EnrichedFunctor.MonoidalFunctorTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [EnrichedOrdinaryCategory V C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
  [EnrichedOrdinaryCategory V D]
variable {dC : EnrichedMonoidalCategoryData V C}
variable {dD : EnrichedMonoidalCategoryData V D}
variable {F : EnrichedFunctor V C D}

#check LaxMonoidalData
#check LaxMonoidalData.epsilon
#check LaxMonoidalData.mu
#check LaxMonoidalData.mu_naturality
#check LaxMonoidalData.unit
#check LaxMonoidalData.assoc
#check StrongMonoidalData
#check StrongMonoidalData.unitIso
#check StrongMonoidalData.tensorIso
#check LaxBraidedData
#check LaxBraidedData.braided

section Lax

variable (l : LaxMonoidalData dC dD F)

example : 𝟙_ D ⟶ F.obj (𝟙_ C) := l.epsilon

example (X Y : C) : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y) :=
  l.mu X Y

example (X X' Y Y' : C) :
    (F.map X X' ⊗ₘ F.map Y Y') ≫
          dD.tensorMap (F.obj X) (F.obj X') (F.obj Y) (F.obj Y') ≫
        eHomWhiskerLeft V (F.obj X ⊗ F.obj Y) (l.mu X' Y') =
      dC.tensorMap X X' Y Y' ≫ F.map (X ⊗ Y) (X' ⊗ Y') ≫
        eHomWhiskerRight V (l.mu X Y) (F.obj (X' ⊗ Y')) :=
  l.mu_naturality X X' Y Y'

example (X : C) :
    ((λ_ (F.obj X)).hom =
        l.epsilon ▷ F.obj X ≫ l.mu (𝟙_ C) X ≫
          (eHomEquiv V).symm
            (eHomEquiv V (λ_ X).hom ≫ F.map (𝟙_ C ⊗ X) X)) ∧
    ((ρ_ (F.obj X)).hom =
        F.obj X ◁ l.epsilon ≫ l.mu X (𝟙_ C) ≫
          (eHomEquiv V).symm
            (eHomEquiv V (ρ_ X).hom ≫ F.map (X ⊗ 𝟙_ C) X)) :=
  l.unit X

example (X Y Z : C) :
    l.mu X Y ▷ F.obj Z ≫ l.mu (X ⊗ Y) Z ≫
        (eHomEquiv V).symm
          (eHomEquiv V (α_ X Y Z).hom ≫
            F.map ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))) =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        F.obj X ◁ l.mu Y Z ≫ l.mu X (Y ⊗ Z) :=
  l.assoc X Y Z

example : True := by
  fail_if_success
    let _ : F.obj (𝟙_ C) ⟶ 𝟙_ D := l.epsilon
  fail_if_success
    let _ : ∀ X Y : C, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y :=
      l.mu
  fail_if_success
    exact (inferInstance : LaxMonoidalData dC dD F)
  exact True.intro

end Lax

section ConstructorAndDeletionGuards

variable (epsilon : 𝟙_ D ⟶ F.obj (𝟙_ C))
variable (mu : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y))
variable (hmu : ∀ X X' Y Y' : C,
  (F.map X X' ⊗ₘ F.map Y Y') ≫
        dD.tensorMap (F.obj X) (F.obj X') (F.obj Y) (F.obj Y') ≫
      eHomWhiskerLeft V (F.obj X ⊗ F.obj Y) (mu X' Y') =
    dC.tensorMap X X' Y Y' ≫ F.map (X ⊗ Y) (X' ⊗ Y') ≫
      eHomWhiskerRight V (mu X Y) (F.obj (X' ⊗ Y')))
variable (hunit : ∀ X : C,
  ((λ_ (F.obj X)).hom =
      epsilon ▷ F.obj X ≫ mu (𝟙_ C) X ≫
        (eHomEquiv V).symm
          (eHomEquiv V (λ_ X).hom ≫ F.map (𝟙_ C ⊗ X) X)) ∧
  ((ρ_ (F.obj X)).hom =
      F.obj X ◁ epsilon ≫ mu X (𝟙_ C) ≫
        (eHomEquiv V).symm
          (eHomEquiv V (ρ_ X).hom ≫ F.map (X ⊗ 𝟙_ C) X)))
variable (hassoc : ∀ X Y Z : C,
  mu X Y ▷ F.obj Z ≫ mu (X ⊗ Y) Z ≫
      (eHomEquiv V).symm
        (eHomEquiv V (α_ X Y Z).hom ≫
          F.map ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))) =
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
      F.obj X ◁ mu Y Z ≫ mu X (Y ⊗ Z))

example : LaxMonoidalData dC dD F where
  epsilon := epsilon
  mu := mu
  mu_naturality := hmu
  unit := hunit
  assoc := hassoc

example : True := by
  fail_if_success
    exact LaxMonoidalData.mk epsilon mu hunit hassoc
  fail_if_success
    exact LaxMonoidalData.mk epsilon mu hmu hassoc
  fail_if_success
    exact LaxMonoidalData.mk epsilon mu hmu hunit
  exact True.intro

end ConstructorAndDeletionGuards

section Strong

variable (l : LaxMonoidalData dC dD F)
variable (s : StrongMonoidalData l)

example : IsIso l.epsilon := s.unitIso

example (X Y : C) : IsIso (l.mu X Y) := s.tensorIso X Y

example : True := by
  fail_if_success
    exact (inferInstance : IsIso l.epsilon)
  fail_if_success
    exact (inferInstance : StrongMonoidalData l)
  exact True.intro

example :
    let _ : IsIso l.epsilon := s.unitIso
    l.epsilon ≫ inv l.epsilon = 𝟙 _ := by
  let _ : IsIso l.epsilon := s.unitIso
  exact IsIso.hom_inv_id l.epsilon

example (X Y : C) :
    let _ : IsIso (l.mu X Y) := s.tensorIso X Y
    l.mu X Y ≫ inv (l.mu X Y) = 𝟙 _ := by
  let _ : IsIso (l.mu X Y) := s.tensorIso X Y
  exact IsIso.hom_inv_id (l.mu X Y)

example :
    let _ : IsIso l.epsilon := s.unitIso
    inv l.epsilon ≫ l.epsilon = 𝟙 _ := by
  let _ : IsIso l.epsilon := s.unitIso
  simp

example (X Y : C) :
    let _ : IsIso (l.mu X Y) := s.tensorIso X Y
    inv (l.mu X Y) ≫ l.mu X Y = 𝟙 _ := by
  let _ : IsIso (l.mu X Y) := s.tensorIso X Y
  simp

end Strong

section StrongConstructorGuards

variable (l : LaxMonoidalData dC dD F)
variable (hunit : IsIso l.epsilon)
variable (htensor : ∀ X Y : C, IsIso (l.mu X Y))

example : StrongMonoidalData l where
  unitIso := hunit
  tensorIso := htensor

example : True := by
  fail_if_success
    exact ({ tensorIso := htensor } : StrongMonoidalData l)
  fail_if_success
    exact ({ unitIso := hunit } : StrongMonoidalData l)
  exact True.intro

end StrongConstructorGuards

section Braided

variable [BraidedCategory C] [BraidedCategory D]
variable (l : LaxMonoidalData dC dD F)
variable (b : LaxBraidedData l)

example (X Y : C) :
    l.mu X Y ≫
        (eHomEquiv V).symm
          (eHomEquiv V (β_ X Y).hom ≫ F.map (X ⊗ Y) (Y ⊗ X)) =
      (β_ (F.obj X) (F.obj Y)).hom ≫ l.mu Y X :=
  b.braided X Y

example : True := by
  fail_if_success
    exact (inferInstance : LaxBraidedData l)
  exact True.intro

end Braided

section BraidedConstructorGuard

variable [BraidedCategory C] [BraidedCategory D]
variable (l : LaxMonoidalData dC dD F)
variable (hbraided : ∀ X Y : C,
  l.mu X Y ≫
      (eHomEquiv V).symm
        (eHomEquiv V (β_ X Y).hom ≫ F.map (X ⊗ Y) (Y ⊗ X)) =
    (β_ (F.obj X) (F.obj Y)).hom ≫ l.mu Y X)

example : LaxBraidedData l where
  braided := hbraided

example : True := by
  fail_if_success
    exact ({} : LaxBraidedData l)
  exact True.intro

end BraidedConstructorGuard

section TargetBraidingDeletionGuard

variable (l : LaxMonoidalData dC dD F)
variable (hC : BraidedCategory C)

example : True := by
  let _ : BraidedCategory C := hC
  fail_if_success
    let _ : Prop := LaxBraidedData l
  exact True.intro

end TargetBraidingDeletionGuard

section SourceBraidingDeletionGuard

variable (l : LaxMonoidalData dC dD F)
variable (hD : BraidedCategory D)

example : True := by
  let _ : BraidedCategory D := hD
  fail_if_success
    let _ : Prop := LaxBraidedData l
  exact True.intro

end SourceBraidingDeletionGuard

section UniverseClients

variable (V₀ : Type) [Category.{0} V₀] [MonoidalCategory V₀]
  [BraidedCategory V₀]
variable (C₀ : Type) [Category.{0} C₀] [MonoidalCategory C₀]
  [EnrichedOrdinaryCategory V₀ C₀]
variable (D₀ : Type) [Category.{0} D₀] [MonoidalCategory D₀]
  [EnrichedOrdinaryCategory V₀ D₀]
variable (dC₀ : EnrichedMonoidalCategoryData V₀ C₀)
variable (dD₀ : EnrichedMonoidalCategoryData V₀ D₀)
variable (F₀ : EnrichedFunctor V₀ C₀ D₀)

#check LaxMonoidalData dC₀ dD₀ F₀

variable (V₁ : Type 1) [Category.{1} V₁] [MonoidalCategory V₁]
  [BraidedCategory V₁]
variable (C₁ : Type 1) [Category.{1} C₁] [MonoidalCategory C₁]
  [EnrichedOrdinaryCategory V₁ C₁]
variable (D₁ : Type 1) [Category.{1} D₁] [MonoidalCategory D₁]
  [EnrichedOrdinaryCategory V₁ D₁]
variable (dC₁ : EnrichedMonoidalCategoryData V₁ C₁)
variable (dD₁ : EnrichedMonoidalCategoryData V₁ D₁)
variable (F₁ : EnrichedFunctor V₁ C₁ D₁)

#check LaxMonoidalData dC₁ dD₁ F₁

end UniverseClients

end CategoryTheory.EnrichedFunctor.MonoidalFunctorTests

#print axioms CategoryTheory.EnrichedFunctor.LaxMonoidalData
#print axioms CategoryTheory.EnrichedFunctor.StrongMonoidalData
#print axioms CategoryTheory.EnrichedFunctor.LaxBraidedData
