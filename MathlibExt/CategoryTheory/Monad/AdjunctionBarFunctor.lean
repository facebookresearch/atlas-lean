/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monad.AdjunctionBarResolution

/-!
# Functoriality of the augmented adjunction Bar

The free Bar construction associated to an adjunction is functorial in its coefficient object.
Counit naturality gives a natural augmentation, and these maps form a functor into augmented
simplicial objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe uC vC uD vD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ D} {U : D ⥤ C}

/-- The free Bar is the algebra-Bar bifunctor with fixed counit right module. -/
def freeBarFunctor (adj : F ⊣ U) : D ⥤ SimplicialObject D :=
  (((Functor.const D).obj adj.freeRightModule).prod' (Monad.comparison adj)) ⋙
    Monad.algebraBarFunctor (T := adj.toMonad) (D := D)

/-- The bundled functor has the objectwise free Bar. -/
@[simp]
theorem freeBarFunctor_obj (adj : F ⊣ U) (M : D) :
    (freeBarFunctor adj).obj M = adj.freeBar M := rfl

/-- Each degree map is the free functor applied to the iterated restricted map. -/
theorem freeBarFunctor_map_app_mk (adj : F ⊣ U) {M N : D} (f : M ⟶ N) (n : ℕ) :
    ((freeBarFunctor adj).map f).app (op (SimplexCategory.mk n)) =
      F.map ((Monad.monadPow adj.toMonad n).map (U.map f)) := by
  change F.map ((Monad.monadPow adj.toMonad n).map (U.map f)) ≫ (𝟙 _) = _
  exact Category.comp_id _

/-- The counit augmentation is natural in every coefficient morphism. -/
def freeBarAugmentationNat (adj : F ⊣ U) : freeBarFunctor adj ⟶ SimplicialObject.const D where
  app M := (adj.freeBarAugmented M).hom
  naturality M N f := by
    apply SimplicialObject.toConst_ext_zero
    change ((freeBarFunctor adj).map f).app (op (SimplexCategory.mk 0)) ≫
        (adj.freeBarAugmented N).hom.app (op (SimplexCategory.mk 0)) =
      (adj.freeBarAugmented M).hom.app (op (SimplexCategory.mk 0)) ≫ f
    rw [freeBarFunctor_map_app_mk, freeBarAugmented_hom_zero, freeBarAugmented_hom_zero]
    exact adj.counit.naturality f

/-- The Bar and its counit augmentation form a augmented functor. -/
def freeBarAugmentedFunctor (adj : F ⊣ U) : D ⥤ SimplicialObject.Augmented D where
  obj M := adj.freeBarAugmented M
  map f :=
    { left := (freeBarFunctor adj).map f
      right := f
      w := (freeBarAugmentationNat adj).naturality f }
  map_id M := by
    apply Comma.hom_ext
    · exact (freeBarFunctor adj).map_id M
    · rfl
  map_comp f g := by
    apply Comma.hom_ext
    · exact (freeBarFunctor adj).map_comp f g
    · rfl

/-- The augmented functor retains the full augmentation object. -/
@[simp]
theorem freeBarAugmentedFunctor_obj (adj : F ⊣ U) (M : D) :
    (freeBarAugmentedFunctor adj).obj M = adj.freeBarAugmented M := rfl

/-- Every augmented map has the algebra-Bar map on its source. -/
@[simp]
theorem freeBarAugmentedFunctor_map_left (adj : F ⊣ U) {M N : D} (f : M ⟶ N) :
    ((freeBarAugmentedFunctor adj).map f).left = (freeBarFunctor adj).map f := rfl

/-- Every augmented map has the coefficient morphism as its target component. -/
@[simp]
theorem freeBarAugmentedFunctor_map_right (adj : F ⊣ U) {M N : D} (f : M ⟶ N) :
    ((freeBarAugmentedFunctor adj).map f).right = f := rfl

end CategoryTheory.Adjunction
