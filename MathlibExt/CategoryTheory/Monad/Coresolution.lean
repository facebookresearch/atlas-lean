/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Monad.PowerOpposite
public import MathlibExt.CategoryTheory.Comonad.BarResolution

/-!
# Coaugmented monad coresolutions

The augmented comonad resolution in the opposite category gives a
coaugmented cosimplicial monad resolution. Augmented duality and
whiskering supply its identities and maps. Degree isomorphisms identify
its operators with source-ordered monad insertions.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.Monad

variable {C : Type u} [Category.{v} C]

/-- The actual coaugmented coresolution is the native dual augmented resolution functor. -/
def coresolutionAugmentedFunctor (T : Monad C) :
    C ⥤ CosimplicialObject.Augmented C :=
  (Comonad.resolutionAugmentedFunctor (Monad.op T)).rightOp ⋙
    (simplicialCosimplicialAugmentedEquiv Cᵒᵖ).functor ⋙
      CosimplicialObject.Augmented.whiskeringObj (Cᵒᵖ)ᵒᵖ C (unopUnop C)

/-- The actual canonical coaugmented object at X. -/
def coresolutionAugmented (T : Monad C) (X : C) : CosimplicialObject.Augmented C :=
  (coresolutionAugmentedFunctor T).obj X

/-- The canonical cosimplicial coresolution, functorial in the original object. -/
def coresolutionFunctor (T : Monad C) : C ⥤ CosimplicialObject C :=
  coresolutionAugmentedFunctor T ⋙ CosimplicialObject.Augmented.drop

/-- The underlying actual cosimplicial object. -/
def coresolution (T : Monad C) (X : C) : CosimplicialObject C :=
  (coresolutionAugmented T X).right

/-- The actual coaugmentation point is the original object. -/
theorem coresolutionAugmented_point (T : Monad C) (X : C) :
    (coresolutionAugmented T X).left = X := by
  change (Comonad.resolutionAugmented (Monad.op T) (Opposite.op X)).right.unop = X
  rw [Comonad.resolutionAugmented_point]

/-- The actual degree object is the dual native comonad power. -/
theorem coresolution_obj (T : Monad C) (X : C) (n : ℕ) :
    (coresolution T X).obj (SimplexCategory.mk n) =
      ((Comonad.comonadPow (Monad.op T) (n + 1)).obj (Opposite.op X)).unop := by
  change ((Comonad.resolutionAugmented (Monad.op T) (Opposite.op X)).left.obj
    (Opposite.op (SimplexCategory.mk n))).unop = _
  rw [Comonad.resolutionAugmented_left, Comonad.resolutionBar_obj]

/-- Actual cofaces use the dual source-ordered counit insertions. -/
theorem coresolution_map_δ (T : Monad C) (X : C) {n : ℕ} (i : Fin (n + 2)) :
    (coresolution T X).map (SimplexCategory.δ i) =
      (Comonad.cobarEpsilonAtPos (Monad.op T) (n + 1) i (Opposite.op X)).unop := by
  change ((Comonad.resolutionBar (Monad.op T) (Opposite.op X)).map
    (SimplexCategory.δ i).op).unop = _
  exact congrArg Quiver.Hom.unop
    (Comonad.resolutionBar_map_δ_op (Monad.op T) (Opposite.op X) i)

/-- Actual codegeneracies use the dual source-ordered comultiplication insertions. -/
theorem coresolution_map_σ (T : Monad C) (X : C) {n : ℕ} (i : Fin (n + 1)) :
    (coresolution T X).map (SimplexCategory.σ i) =
      (Comonad.cobarDeltaAtPos (Monad.op T) (n + 1) i (Opposite.op X)).unop := by
  change ((Comonad.resolutionBar (Monad.op T) (Opposite.op X)).map
    (SimplexCategory.σ i).op).unop = _
  exact congrArg Quiver.Hom.unop
    (Comonad.resolutionBar_map_σ_op (Monad.op T) (Opposite.op X) i)

/-- The actual degree-zero coaugmentation is the original monad unit. -/
theorem coresolutionAugmented_hom_zero (T : Monad C) (X : C) :
    (coresolutionAugmented T X).hom.app (SimplexCategory.mk 0) = T.η.app X := by
  change 𝟙 _ ≫ ((Comonad.resolutionAugmented (Monad.op T) (Opposite.op X)).hom.app
    (Opposite.op (SimplexCategory.mk 0))).unop = T.η.app X
  simp only [Category.id_comp, Comonad.resolutionAugmented_hom_zero,
    Monad.op_ε_app]
  rfl

/-- The actual coresolution map retains the native iterated map in each degree. -/
theorem coresolutionFunctor_map_app (T : Monad C) {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    ((coresolutionFunctor T).map f).app (SimplexCategory.mk n) =
      ((Comonad.comonadPow (Monad.op T) (n + 1)).map f.op).unop := by
  change ((Comonad.resolutionHom (Monad.op T) f.op).left.app
    (Opposite.op (SimplexCategory.mk n))).unop = _
  exact congrArg Quiver.Hom.unop
    (Comonad.resolutionHom_left_app (Monad.op T) f.op n)

/-- The point component of the actual augmented coresolution map is the original morphism. -/
theorem coresolutionAugmentedFunctor_map_left (T : Monad C) {X Y : C} (f : X ⟶ Y) :
    ((coresolutionAugmentedFunctor T).map f).left = f := by
  change (Comonad.resolutionHom (Monad.op T) f.op).right.unop = f
  rw [Comonad.resolutionHom_right]
  rfl

/-- The actual degree object has explicit native monad-power coordinates. -/
def coresolutionObjIso (T : Monad C) (X : C) (n : ℕ) :
    (coresolution T X).obj (SimplexCategory.mk n) ≅ (monadPow T (n + 1)).obj X :=
  eqToIso (coresolution_obj T X n) ≪≫ (monadPowOpIso T (n + 1)).app X

/-- The actual degree coordinates use the native opposite-power comparison. -/
@[simp]
theorem coresolutionObjIso_hom (T : Monad C) (X : C) (n : ℕ) :
    (coresolutionObjIso T X n).hom = (monadPowOpIso T (n + 1)).hom.app X := by
  induction n generalizing X with
  | zero =>
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      exact Category.id_comp _
  | succ n ih =>
      exact ih (T.obj X)

/-- These explicit degree coordinates preserve the actual higher object maps. -/
theorem coresolutionObjIso_naturality (T : Monad C) {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    ((coresolutionFunctor T).map f).app (SimplexCategory.mk n) ≫
        (coresolutionObjIso T Y n).hom =
      (coresolutionObjIso T X n).hom ≫ (monadPow T (n + 1)).map f := by
  rw [coresolutionFunctor_map_app, coresolutionObjIso_hom, coresolutionObjIso_hom]
  change ((Comonad.comonadPow (Monad.op T) (n + 1)).map f.op).unop ≫
      (monadPowOpIso T (n + 1)).hom.app Y =
    (monadPowOpIso T (n + 1)).hom.app X ≫ (monadPow T (n + 1)).map f
  exact (monadPowOpIso T (n + 1)).hom.naturality f

/-- The actual cofaces are the existing monad unit insertions in degree coordinates. -/
theorem coresolutionObjIso_coface (T : Monad C) (X : C) {n : ℕ} (i : Fin (n + 2)) :
    (coresolution T X).map (SimplexCategory.δ i) ≫
        (coresolutionObjIso T X (n + 1)).hom =
      (coresolutionObjIso T X n).hom ≫ barEtaAtPos T (n + 1) i X := by
  rw [coresolution_map_δ, coresolutionObjIso_hom, coresolutionObjIso_hom]
  change (Comonad.cobarEpsilonAtPos (Monad.op T) (n + 1) i (Opposite.op X)).unop ≫
      (monadPowOpIso T (n + 2)).hom.app X =
    (monadPowOpIso T (n + 1)).hom.app X ≫ barEtaAtPos T (n + 1) i X
  exact cobarEpsilonAtPos_op T (n + 1) i X

/-- The actual codegeneracies are the existing monad multiplication insertions. -/
theorem coresolutionObjIso_codegeneracy (T : Monad C) (X : C) {n : ℕ} (i : Fin (n + 1)) :
    (coresolution T X).map (SimplexCategory.σ i) ≫ (coresolutionObjIso T X n).hom =
      (coresolutionObjIso T X (n + 1)).hom ≫ barMuAtPos T (n + 1) i X := by
  rw [coresolution_map_σ, coresolutionObjIso_hom, coresolutionObjIso_hom]
  change (Comonad.cobarDeltaAtPos (Monad.op T) (n + 1) i (Opposite.op X)).unop ≫
      (monadPowOpIso T (n + 1)).hom.app X =
    (monadPowOpIso T (n + 2)).hom.app X ≫ barMuAtPos T (n + 1) i X
  exact cobarDeltaAtPos_op T (n + 1) i X

end CategoryTheory.Monad

end
