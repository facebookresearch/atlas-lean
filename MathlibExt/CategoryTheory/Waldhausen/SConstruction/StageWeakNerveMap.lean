/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.SimplicialStageMap
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakNerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Weak-stage nerve maps

For exact categories `C` and `D` over the same universes `u, v` with their
local standard Waldhausen structures (`ExactCategory.waldhausenCategory`),
an additive exact functor `F : C ⥤ D` induces a levelwise nerve map
`stageWeakNerveMap F : stageWeakNerve C ⟶ stageWeakNerve D`
as `Functor.whiskerRight (simplicialStageMapWeak C D F) nerveFunctor`.

Only app computation, the `mk₀` and `mk₁` action laws, and the identity/composition laws
needed by later diagonal/realization consumers are added, reusing
`simplicialStageMapWeak_id` and `simplicialStageMapWeak_comp` with
`Functor.whiskerRight_id'` and `Functor.whiskerRight_comp`. No bundled
exact-category category or lifting is introduced.

Nonclaims: no diagonal, realization, additivity, K-theory, G-theory, spectrum,
or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

/-- Levelwise weak-stage nerve map with components `nerveFunctor.map`. -/
def stageWeakNerveMap :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      stageWeakNerve C ⟶ stageWeakNerve D) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact Functor.whiskerRight (simplicialStageMapWeak C D F) nerveFunctor

/-- App computation for `stageWeakNerveMap`. -/
@[simp]
theorem stageWeakNerveMap_app (a : SimplexCategoryᵒᵖ) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakNerveMap C D F).app a =
        nerveFunctor.map ((simplicialStageMapWeak C D F).app a)) := by
  rfl

/-- Identity functor induces the identity weak-stage nerve map. -/
@[simp]
theorem stageWeakNerveMap_id :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      stageWeakNerveMap C C (𝟭 C) = 𝟙 (stageWeakNerve C)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  unfold stageWeakNerveMap
  rw [simplicialStageMapWeak_id]
  exact Functor.whiskerRight_id' _

/-- Composite functors induce composite weak-stage nerve maps. -/
@[simp]
theorem stageWeakNerveMap_comp (E : Type u) [Category.{v} E]
    [Preadditive E] [Limits.HasZeroObject E]
    [HasBinaryBiproducts E] [ExactCategory E]
    (G : D ⥤ E) [G.Additive] [Functor.IsExact G] :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      stageWeakNerveMap C E (F ⋙ G) =
        stageWeakNerveMap C D F ≫ stageWeakNerveMap D E G) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  unfold stageWeakNerveMap
  rw [simplicialStageMapWeak_comp]
  exact Functor.whiskerRight_comp _ _ _

/-- Action of a `stageWeakNerveMap` component on a `mk₀` simplex. -/
@[simp]
theorem stageWeakNerveMap_app_mk₀ (a : SimplexCategoryᵒᵖ)
    (X : (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      StageWeakCategory C a.unop.len)) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      ((stageWeakNerveMap C D F).app a).app (op ⦋0⦌) (ComposableArrows.mk₀ X) =
        ComposableArrows.mk₀ ((mapStageWeak C D F a.unop.len).obj X)) := by
  rw [stageWeakNerveMap_app, simplicialStageMapWeak_app]
  exact CategoryTheory.nerveMap_app_mk₀ _ _

/-- Action of a `stageWeakNerveMap` component on a `mk₁` simplex. -/
@[simp]
theorem stageWeakNerveMap_app_mk₁ (a : SimplexCategoryᵒᵖ)
    {X Y : (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      StageWeakCategory C a.unop.len)} (φ : X ⟶ Y) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      ((stageWeakNerveMap C D F).app a).app (op ⦋1⦌) (ComposableArrows.mk₁ φ) =
        ComposableArrows.mk₁ ((mapStageWeak C D F a.unop.len).map φ)) := by
  rw [stageWeakNerveMap_app, simplicialStageMapWeak_app]
  exact CategoryTheory.nerveMap_app_mk₁ _ _

end CategoryTheory.Waldhausen.SConstruction
