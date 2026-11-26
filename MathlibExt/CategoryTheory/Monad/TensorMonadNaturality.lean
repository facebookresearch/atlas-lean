/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monad.MonoidalBar

/-!
# Tensor monads vary with internal monoids

An internal monoid morphism `f : M → N` gives a monad morphism between `M ⊗ -` and `N ⊗ -`,
with component `f.hom ▷ X`. The unit and multiplication conditions are the monoid morphism
laws.

This construction preserves identities and composition and gives the corresponding morphism
between regular right modules, after restriction along the monad morphism.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monad

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Internal monoid morphism induces a tensor monad morphism.

The components `f.hom ▷ X` define a natural transformation respecting tensor-monad unit and
multiplication. -/
noncomputable def tensorMonadHom {M N : Mon C} (f : M ⟶ N) :
    tensorMonad M.X ⟶ tensorMonad N.X where
  toNatTrans :=
    { app := fun X => f.hom ▷ X
      naturality := fun _ _ g => MonoidalCategory.whisker_exchange f.hom g }
  app_η := fun X => by
    rw [tensorMonad_eta_app, tensorMonad_eta_app]
    calc
      ((λ_ X).inv ≫ (MonObj.one (X := M.X) ▷ X)) ≫ (f.hom ▷ X) =
          (λ_ X).inv ≫
            ((MonObj.one (X := M.X) ▷ X) ≫ (f.hom ▷ X)) :=
        Category.assoc _ _ _
      _ = (λ_ X).inv ≫ ((MonObj.one (X := M.X) ≫ f.hom) ▷ X) :=
        congrArg ((λ_ X).inv ≫ ·)
          (MonoidalCategory.comp_whiskerRight _ _ _).symm
      _ = (λ_ X).inv ≫ (MonObj.one (X := N.X) ▷ X) := by
        rw [IsMonHom.one_hom]
  app_μ := fun X => by
    change (tensorMonad M.X).μ.app X ≫ (f.hom ▷ X) =
      ((tensorMonad M.X).map (f.hom ▷ X) ≫
        (f.hom ▷ (tensorMonad N.X).obj X)) ≫
          (tensorMonad N.X).μ.app X
    have hMap : (tensorMonad M.X).map (f.hom ▷ X) =
        M.X ◁ (f.hom ▷ X) := rfl
    have hWhisker : f.hom ▷ (tensorMonad N.X).obj X =
        f.hom ▷ (N.X ⊗ X) := rfl
    rw [hMap, hWhisker, tensorMonad_mu_app, tensorMonad_mu_app,
      tensorLeftTensor_inv_app, tensorLeftTensor_inv_app]
    have hAssoc := associator_inv_naturality f.hom f.hom (𝟙 X)
    simp only [tensorHom_id] at hAssoc
    calc
      _ = (α_ M.X M.X X).inv ≫
          ((MonObj.mul (X := M.X) ≫ f.hom) ▷ X) := by
        rw [comp_whiskerRight]
        simp only [Category.assoc]
      _ = (α_ M.X M.X X).inv ≫
          (((f.hom ⊗ₘ f.hom) ≫ MonObj.mul (X := N.X)) ▷ X) := by
        rw [IsMonHom.mul_hom]
      _ = (α_ M.X M.X X).inv ≫
          ((f.hom ⊗ₘ f.hom) ▷ X) ≫
          (MonObj.mul (X := N.X) ▷ X) := by
        rw [comp_whiskerRight]
      _ = ((f.hom ⊗ₘ (f.hom ▷ X)) ≫
            (α_ N.X N.X X).inv) ≫
          (MonObj.mul (X := N.X) ▷ X) := by
        rw [← Category.assoc, ← hAssoc]
      _ = _ := by
        rw [tensorHom_def']
        simp only [Category.assoc]

/-- Tensor monad morphism component is tensoring the monoid map.

At object `X`, the component is `f.hom ▷ X`. -/
@[simp]
theorem tensorMonadHom_app {M N : Mon C} (f : M ⟶ N) (X : C) :
    (tensorMonadHom f).app X = f.hom ▷ X :=
  rfl

/-- Tensor monad morphism respects the unit.

The source unit followed by the component equals the target unit. -/
@[reassoc]
theorem tensorMonadHom_η {M N : Mon C} (f : M ⟶ N) (X : C) :
    (tensorMonad M.X).η.app X ≫ (tensorMonadHom f).app X =
      (tensorMonad N.X).η.app X :=
  (tensorMonadHom f).app_η X

/-- Tensor monad morphism respects multiplication.

The source multiplication followed by the component equals the two component maps followed by
target multiplication. -/
@[reassoc]
theorem tensorMonadHom_μ {M N : Mon C} (f : M ⟶ N) (X : C) :
    (tensorMonad M.X).μ.app X ≫ (tensorMonadHom f).app X =
      ((tensorMonad M.X).map ((tensorMonadHom f).app X) ≫
        (tensorMonadHom f).app ((tensorMonad N.X).obj X)) ≫
          (tensorMonad N.X).μ.app X :=
  (tensorMonadHom f).app_μ X

/-- Identity monoid map gives the identity tensor monad map.

The tensor-monad morphism of the identity internal monoid map is the identity. -/
@[simp]
theorem tensorMonadHom_id (M : Mon C) :
    tensorMonadHom (𝟙 M) = 𝟙 (tensorMonad M.X) := by
  apply MonadHom.ext
  funext X
  change (𝟙 M : M ⟶ M).hom ▷ X = 𝟙 (M.X ⊗ X)
  rw [show (𝟙 M : M ⟶ M).hom = 𝟙 M.X by rfl, id_whiskerRight]

/-- Tensor monad maps preserve monoid map composition.

The map of a composite internal monoid morphism equals the composite of its tensor-monad
morphisms. -/
@[simp]
theorem tensorMonadHom_comp {M N P : Mon C} (f : M ⟶ N) (g : N ⟶ P) :
    tensorMonadHom (f ≫ g) = tensorMonadHom f ≫ tensorMonadHom g := by
  apply MonadHom.ext
  funext X
  change (f ≫ g).hom ▷ X = (f.hom ▷ X) ≫ (g.hom ▷ X)
  rw [show (f ≫ g).hom = f.hom ≫ g.hom by rfl, comp_whiskerRight]

/-- Monoid map induces a restricted regular right module map.

The monad morphism gives a map from the source regular right module to the target regular
module restricted along that morphism. -/
noncomputable def tensorMonadRegularRightModuleHom {M N : Mon C} (f : M ⟶ N) :
    RightModule.regular (tensorMonad M.X) ⟶
      (rightModuleRestrictAlongHom (tensorMonadHom f)).obj
        (RightModule.regular (tensorMonad N.X)) where
  f := (tensorMonadHom f).toNatTrans
  h := by
    apply NatTrans.ext
    funext X
    change (tensorMonadHom f).app ((tensorMonad M.X).obj X) ≫
        ((tensorMonad N.X).map ((tensorMonadHom f).app X) ≫
          (tensorMonad N.X).μ.app X) =
      (tensorMonad M.X).μ.app X ≫ (tensorMonadHom f).app X
    rw [← Category.assoc, ← (tensorMonadHom f).naturality]
    exact ((tensorMonadHom f).app_μ X).symm

end CategoryTheory.Monad

end
