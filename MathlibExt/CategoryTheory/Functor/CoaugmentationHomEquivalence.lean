/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Functor.CoaugmentedTestRetract

/-!
# Explicit Hom equivalences from the original coaugmentation retraction

The existing complete Hom retraction gives an equivalence for every map
inverted by a coaugmented functor, at every target with invertible
coaugmentation. Its inverse uses the original maps in their original order.
The equivalence is natural in the full original arrow and its target.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory

namespace CategoryTheory.Functor.CoaugmentationHomTests

variable {C : Type u} [Category.{v} C] {Q : C ⥤ C} (η : 𝟭 C ⟶ Q)

/-- The inverse Hom test uses the existing original source-unit/target-unit retraction. -/
def liftHom {X Y E : C} (f : X ⟶ Y)
    [IsIso (Q.map f)] [IsIso (η.app E)] (g : X ⟶ E) : Y ⟶ E :=
  CoaugmentedTestRetract.homRetraction Q η Y E
    (CategoryTheory.inv (Q.map f) ≫ Q.map g)

/-- The constructed inverse retains all four actual maps, without an input reflection premise. -/
theorem liftHom_formula {X Y E : C} (f : X ⟶ Y)
    [IsIso (Q.map f)] [IsIso (η.app E)] (g : X ⟶ E) :
    liftHom η f g = η.app Y ≫ CategoryTheory.inv (Q.map f) ≫
      Q.map g ≫ CategoryTheory.inv (η.app E) := by
  simp only [liftHom, CoaugmentedTestRetract.homRetraction, Category.assoc]

/-- The original naturality retraction proves that the constructed inverse solves the Hom test. -/
theorem comp_liftHom {X Y E : C} (f : X ⟶ Y)
    [IsIso (Q.map f)] [IsIso (η.app E)] (g : X ⟶ E) :
    f ≫ liftHom η f g = g := by
  dsimp only [liftHom]
  rw [← CoaugmentedTestRetract.homRetraction_source,
    IsIso.hom_inv_id_assoc, CoaugmentedTestRetract.homRetraction_map]

/-- The same original retraction proves the other inverse identity. -/
theorem liftHom_comp {X Y E : C} (f : X ⟶ Y)
    [IsIso (Q.map f)] [IsIso (η.app E)] (g : Y ⟶ E) :
    liftHom η f (f ≫ g) = g := by
  dsimp only [liftHom]
  rw [Q.map_comp, IsIso.inv_hom_id_assoc, CoaugmentedTestRetract.homRetraction_map]

/-- Original precomposition and the actual inverse form a full Hom equivalence. -/
def homEquiv {X Y E : C} (f : X ⟶ Y)
    [IsIso (Q.map f)] [IsIso (η.app E)] : (Y ⟶ E) ≃ (X ⟶ E) where
  toFun g := f ≫ g
  invFun := liftHom η f
  left_inv := liftHom_comp η f
  right_inv := comp_liftHom η f

/-- The forward function is exactly precomposition by the original arrow. -/
theorem homEquiv_apply {X Y E : C} (f : X ⟶ Y)
    [IsIso (Q.map f)] [IsIso (η.app E)] (g : Y ⟶ E) :
    homEquiv η f g = f ≫ g := rfl

/-- The inverse function is the original source unit, inverse functor image,
functor action and inverse target unit. -/
theorem homEquiv_symm_apply {X Y E : C} (f : X ⟶ Y)
    [IsIso (Q.map f)] [IsIso (η.app E)] (g : X ⟶ E) :
    (homEquiv η f).symm g =
      η.app Y ≫ CategoryTheory.inv (Q.map f) ≫ Q.map g ≫
        CategoryTheory.inv (η.app E) :=
  liftHom_formula η f g

/-- Every complete original arrow square is natural for the explicit inverse. -/
theorem liftHom_source {X Y X' Y' E : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    [IsIso (Q.map f)] [IsIso (Q.map f')] [IsIso (η.app E)]
    (a : X' ⟶ X) (b : Y' ⟶ Y) (w : f' ≫ b = a ≫ f) (g : X ⟶ E) :
    b ≫ liftHom η f g = liftHom η f' (a ≫ g) := by
  apply (CoaugmentedTestRetract.precomp_bijective_of_map_isIso Q η f').1
  change f' ≫ (b ≫ liftHom η f g) = f' ≫ liftHom η f' (a ≫ g)
  rw [← Category.assoc, w, Category.assoc, comp_liftHom, comp_liftHom]

/-- The forward Hom equivalence retains the same entire original arrow square. -/
theorem homEquiv_source {X Y X' Y' E : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    [IsIso (Q.map f)] [IsIso (Q.map f')] [IsIso (η.app E)]
    (a : X' ⟶ X) (b : Y' ⟶ Y) (w : f' ≫ b = a ≫ f) (g : Y ⟶ E) :
    homEquiv η f' (b ≫ g) = a ≫ homEquiv η f g := by
  change f' ≫ (b ≫ g) = a ≫ (f ≫ g)
  rw [← Category.assoc, w, Category.assoc]

/-- Both inverse functions are natural on the original complete arrow square. -/
theorem homEquiv_symm_source {X Y X' Y' E : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    [IsIso (Q.map f)] [IsIso (Q.map f')] [IsIso (η.app E)]
    (a : X' ⟶ X) (b : Y' ⟶ Y) (w : f' ≫ b = a ≫ f) (g : X ⟶ E) :
    b ≫ (homEquiv η f).symm g = (homEquiv η f').symm (a ≫ g) :=
  liftHom_source η f f' a b w g

/-- Original admissible target maps are natural for the explicit inverse. -/
theorem liftHom_target {X Y E E' : C} (f : X ⟶ Y)
    [IsIso (Q.map f)] [IsIso (η.app E)] [IsIso (η.app E')]
    (g : X ⟶ E) (k : E ⟶ E') :
    liftHom η f (g ≫ k) = liftHom η f g ≫ k := by
  dsimp only [liftHom]
  rw [Q.map_comp, ← Category.assoc, CoaugmentedTestRetract.homRetraction_target]

/-- The forward Hom function preserves every original admissible target map. -/
theorem homEquiv_target {X Y E E' : C} (f : X ⟶ Y)
    [IsIso (Q.map f)] [IsIso (η.app E)] [IsIso (η.app E')]
    (g : Y ⟶ E) (k : E ⟶ E') :
    homEquiv η f (g ≫ k) = homEquiv η f g ≫ k :=
  (Category.assoc f g k).symm

/-- The inverse Hom function preserves the same original target maps. -/
theorem homEquiv_symm_target {X Y E E' : C} (f : X ⟶ Y)
    [IsIso (Q.map f)] [IsIso (η.app E)] [IsIso (η.app E')]
    (g : X ⟶ E) (k : E ⟶ E') :
    (homEquiv η f).symm (g ≫ k) = (homEquiv η f).symm g ≫ k :=
  liftHom_target η f g k

end CategoryTheory.Functor.CoaugmentationHomTests
