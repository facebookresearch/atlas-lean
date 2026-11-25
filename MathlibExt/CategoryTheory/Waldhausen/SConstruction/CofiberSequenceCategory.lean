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

public import MathlibExt.CategoryTheory.Waldhausen.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Cofiber sequences as a full subcategory of composable pairs

Bundles composable pairs `X ⟶ Y ⟶ Z` whose `0 → 1` and `1 → 2` legs form an
`IsCofibrationSequence` as the full subcategory `CofiberSequenceCategory C`,
with the inherited category from `ObjectProperty.FullSubcategory` and the
fully faithful forgetful functor. This file only bundles the category; it
proves no extraction, morphism functor, equivalence, reindexing, simplicial
object, weak-equivalence nerve, realization, Q/S comparison, or K/G-theory
content.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Object property on `ComposableArrows C 2` asserting the `0 → 1` and
`1 → 2` legs form an `IsCofiberSequence`. -/
def cofiberSequenceProperty : ObjectProperty (ComposableArrows C 2) :=
  fun S => IsCofiberSequence (S.map' 0 1) (S.map' 1 2)

/-- Cofiber sequences as the full subcategory cut out by `cofiberSequenceProperty`.
Inherits category, full, and faithful instances from `FullSubcategory`. -/
abbrev CofiberSequenceCategory :=
  (cofiberSequenceProperty C).FullSubcategory

namespace CofiberSequenceCategory

/-- Fully faithful forgetful functor to `ComposableArrows C 2`, reused from `FullSubcategory.ι`. -/
abbrev forget : CofiberSequenceCategory C ⥤ ComposableArrows C 2 :=
  (cofiberSequenceProperty C).ι

/-- The forgetful functor `CofiberSequenceCategory.forget` is fully faithful,
reused from `fullyFaithfulι`. -/
abbrev fullyFaithfulForget : (forget C).FullyFaithful :=
  (cofiberSequenceProperty C).fullyFaithfulι

end CofiberSequenceCategory

end CategoryTheory.Waldhausen.SConstruction
