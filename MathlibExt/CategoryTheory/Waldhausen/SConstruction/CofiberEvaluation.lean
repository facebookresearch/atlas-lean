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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Cofiber-sequence evaluation functors

Pointwise evaluations of cofiber sequences at the `0 → 1 → 2` positions:
`source`, `middle`, and `quotient` compose `CofiberSequenceCategory.forget`
with functor-category `evaluation` at `0`, `1`, and `2` of `Fin 3`.
Objects and maps compute to `ComposableArrows.obj'` and `ComposableArrows.app'`.

This file claims no Waldhausen or exact preservation, no additivity, no
simplicial object, nerve, or realization content, no K-theory or G-theory
content, no spectra, and no Q/S comparison.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

namespace CofiberSequenceCategory

/-- First object of a cofiber sequence, via `forget` and `evaluation` at `0`. -/
def source : CofiberSequenceCategory C ⥤ C :=
  forget C ⋙ (evaluation (Fin 3) C).obj ⟨0, by decide⟩

/-- Second object of a cofiber sequence, via `forget` and `evaluation` at `1`. -/
def middle : CofiberSequenceCategory C ⥤ C :=
  forget C ⋙ (evaluation (Fin 3) C).obj ⟨1, by decide⟩

/-- Third object of a cofiber sequence, via `forget` and `evaluation` at `2`. -/
def quotient : CofiberSequenceCategory C ⥤ C :=
  forget C ⋙ (evaluation (Fin 3) C).obj ⟨2, by decide⟩

/-- `source` on objects is the `0`th component. -/
@[simp]
theorem source_obj (S : CofiberSequenceCategory C) :
    (source C).obj S = ComposableArrows.obj' S.obj 0 := rfl

/-- `middle` on objects is the `1`st component. -/
@[simp]
theorem middle_obj (S : CofiberSequenceCategory C) :
    (middle C).obj S = ComposableArrows.obj' S.obj 1 := rfl

/-- `quotient` on objects is the `2`nd component. -/
@[simp]
theorem quotient_obj (S : CofiberSequenceCategory C) :
    (quotient C).obj S = ComposableArrows.obj' S.obj 2 := rfl

/-- `source` on maps is the `0`th component. -/
@[simp]
theorem source_map {S T : CofiberSequenceCategory C} (φ : S ⟶ T) :
    (source C).map φ = ComposableArrows.app' φ.hom 0 := rfl

/-- `middle` on maps is the `1`st component. -/
@[simp]
theorem middle_map {S T : CofiberSequenceCategory C} (φ : S ⟶ T) :
    (middle C).map φ = ComposableArrows.app' φ.hom 1 := rfl

/-- `quotient` on maps is the `2`nd component. -/
@[simp]
theorem quotient_map {S T : CofiberSequenceCategory C} (φ : S ⟶ T) :
    (quotient C).map φ = ComposableArrows.app' φ.hom 2 := rfl

end CofiberSequenceCategory

end CategoryTheory.Waldhausen.SConstruction
