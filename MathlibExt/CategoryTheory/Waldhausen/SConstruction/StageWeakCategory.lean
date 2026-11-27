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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeak
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Stage weak-equivalence category

Bundles pointwise stage weak equivalences `stageWeak C n` as the wide
subcategory `StageWeakCategory C n`, with its faithful inclusion into
`Stage C n` and contravariant reindexing restricting `reindexStage`.

Nonclaims: no simplicial object, nerve, realization, two-of-three,
saturation, gluing, Q/S comparison, K-theory, or G-theory.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
  (n : ℕ)

/-- Bundled stage weak-equivalence category as the wide subcategory cut out by
`stageWeak C n`. Objects are all `Stage C n` objects; morphisms are pointwise
weak equivalences. -/
abbrev StageWeakCategory :=
  WideSubcategory (stageWeak C n)

/-- Faithful inclusion into `Stage C n`, reused from `wideSubcategoryInclusion`. -/
abbrev stageWeakInclusion : StageWeakCategory C n ⥤ Stage C n :=
  wideSubcategoryInclusion (stageWeak C n)

/-- Object part of `stageWeakInclusion` is the identity. -/
@[simp]
theorem stageWeakInclusion_obj (X : StageWeakCategory C n) :
    (stageWeakInclusion C n).obj X = X.obj :=
  rfl

/-- Morphism part of `stageWeakInclusion` is the underlying map. -/
@[simp]
theorem stageWeakInclusion_map {X Y : StageWeakCategory C n} (f : X ⟶ Y) :
    (stageWeakInclusion C n).map f = f.hom :=
  rfl

/-- Contravariant reindexing of weak-equivalence stages: a simplex map
`a ⟶ b` gives `StageWeakCategory C b.len ⥤ StageWeakCategory C a.len`,
restricting `reindexStage f` along `stageWeak_of_reindexStage`. -/
def reindexStageWeak {a b : SimplexCategory} (f : a ⟶ b) :
    StageWeakCategory C b.len ⥤ StageWeakCategory C a.len where
  obj X := ⟨(reindexStage f).obj X.obj⟩
  map {X Y} φ :=
    ⟨(reindexStage f).map φ.hom, stageWeak_of_reindexStage C f φ.hom φ.property⟩
  map_id X := by
    apply WideSubcategory.hom_ext
    simp
  map_comp {X Y Z} φ ψ := by
    apply WideSubcategory.hom_ext
    simp

/-- Object part of `reindexStageWeak` restricts `reindexStage`. -/
@[simp]
theorem reindexStageWeak_obj {a b : SimplexCategory} (f : a ⟶ b)
    (X : StageWeakCategory C b.len) :
    (reindexStageWeak C f).obj X = ⟨(reindexStage f).obj X.obj⟩ :=
  rfl

/-- Morphism part of `reindexStageWeak` restricts `reindexStage`. -/
@[simp]
theorem reindexStageWeak_map {a b : SimplexCategory} (f : a ⟶ b)
    {X Y : StageWeakCategory C b.len} (φ : X ⟶ Y) :
    (reindexStageWeak C f).map φ =
      ⟨(reindexStage f).map φ.hom, stageWeak_of_reindexStage C f φ.hom φ.property⟩ :=
  rfl

/-- Identity simplex map reindexes to the identity weak-stage functor. -/
@[simp]
theorem reindexStageWeak_id (a : SimplexCategory) :
    reindexStageWeak C (𝟙 a) = 𝟭 (StageWeakCategory C a.len) := by
  rfl

/-- Composition of simplex maps reindexes contravariantly on weak stages. -/
@[simp]
theorem reindexStageWeak_comp {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    reindexStageWeak C (f ≫ g) =
      reindexStageWeak C g ⋙ reindexStageWeak C f := by
  rfl

end CategoryTheory.Waldhausen.SConstruction
