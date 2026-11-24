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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageFunctoriality
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.SimplicialStage
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.SimplicialStageWeak

/-!
# Levelwise simplicial stage maps

For exact categories `C` and `D` over the same universes `u, v` with their
local standard Waldhausen structures (`ExactCategory.waldhausenCategory`),
an additive exact functor `F : C ⥤ D` induces levelwise simplicial maps
`simplicialStageMap F : simplicialStage C ⟶ simplicialStage D` and
`simplicialStageMapWeak F : simplicialStageWeak C ⟶ simplicialStageWeak D`.

Components are `mapStage` / `mapStageWeak` at each degree `a.unop.len`;
naturality is the strict reindex commutation `mapStage_reindex` /
`mapStageWeak_reindex`. Orientation is covariant on simplicial objects via
contravariant stage reindexing along `f.unop`. Only app computation and the
identity/composition laws needed by later levelwise nerve maps are added,
reusing `mapStage_id` / `mapStage_comp` and `mapStageWeak_id` /
`mapStageWeak_comp`. No bundled exact-category category or lifting is
introduced.

Nonclaims: no nerve, diagonal, realization, additivity theorem, K-theory,
G-theory, spectrum, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

/-- Levelwise simplicial stage map with components `mapStage`. -/
def simplicialStageMap :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      simplicialStage C ⟶ simplicialStage D) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact
    { app := fun a => (mapStage C D F a.unop.len).toCatHom
      naturality := fun {a b} f => by
        apply Cat.ext
        exact mapStage_reindex C D F f.unop }

/-- Levelwise simplicial weak-stage map with components `mapStageWeak`. -/
def simplicialStageMapWeak :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      simplicialStageWeak C ⟶ simplicialStageWeak D) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact
    { app := fun a => (mapStageWeak C D F a.unop.len).toCatHom
      naturality := fun {a b} f => by
        apply Cat.ext
        exact mapStageWeak_reindex C D F f.unop }

/-- App computation for `simplicialStageMap`. -/
@[simp]
theorem simplicialStageMap_app (a : SimplexCategoryᵒᵖ) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (simplicialStageMap C D F).app a =
        (mapStage C D F a.unop.len).toCatHom) := by
  rfl

/-- App computation for `simplicialStageMapWeak`. -/
@[simp]
theorem simplicialStageMapWeak_app (a : SimplexCategoryᵒᵖ) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (simplicialStageMapWeak C D F).app a =
        (mapStageWeak C D F a.unop.len).toCatHom) := by
  rfl

/-- Identity functor induces the identity simplicial stage map. -/
@[simp]
theorem simplicialStageMap_id :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      simplicialStageMap C C (𝟭 C) = 𝟙 (simplicialStage C)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  ext a
  exact mapStage_id C a.unop.len

/-- Composite functors induce composite simplicial stage maps. -/
@[simp]
theorem simplicialStageMap_comp (E : Type u) [Category.{v} E]
    [Preadditive E] [Limits.HasZeroObject E]
    [HasBinaryBiproducts E] [ExactCategory E]
    (G : D ⥤ E) [G.Additive] [Functor.IsExact G] :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      simplicialStageMap C E (F ⋙ G) =
        simplicialStageMap C D F ≫ simplicialStageMap D E G) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  ext a
  exact mapStage_comp C D F a.unop.len E G

/-- Identity functor induces the identity simplicial weak-stage map. -/
@[simp]
theorem simplicialStageMapWeak_id :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      simplicialStageMapWeak C C (𝟭 C) = 𝟙 (simplicialStageWeak C)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  ext a
  exact mapStageWeak_id C a.unop.len

/-- Composite functors induce composite simplicial weak-stage maps. -/
@[simp]
theorem simplicialStageMapWeak_comp (E : Type u) [Category.{v} E]
    [Preadditive E] [Limits.HasZeroObject E]
    [HasBinaryBiproducts E] [ExactCategory E]
    (G : D ⥤ E) [G.Additive] [Functor.IsExact G] :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      simplicialStageMapWeak C E (F ⋙ G) =
        simplicialStageMapWeak C D F ≫ simplicialStageMapWeak D E G) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  ext a
  exact mapStageWeak_comp C D F a.unop.len E G

end CategoryTheory.Waldhausen.SConstruction
