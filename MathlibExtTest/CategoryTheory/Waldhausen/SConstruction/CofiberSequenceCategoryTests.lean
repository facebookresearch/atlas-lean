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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

/-!
# Cofiber-sequence category consumer tests

Focused public-API checks for the bundled `CofiberSequenceCategory`: the `mk₂`
pair satisfies the defining property from an actual `IsCofibrationSequence`,
the two generating maps read back through the public forgetful functor, and
the forgetful functor's fully faithful round-trip. No extraction, equivalence,
reindexing, simplicial object, weak-equivalence nerve, realization, G-theory,
or Q/S comparison.
-/

open CategoryTheory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategoryTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

-- Shared witness packaging `mk₂ f g` with its cofiber-sequence proof.
private abbrev mkTestObj (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    CofiberSequenceCategory C :=
  ⟨ComposableArrows.mk₂ f g, by
    have h01 : (ComposableArrows.mk₂ f g).map' 0 1 = f := rfl
    have h12 : (ComposableArrows.mk₂ f g).map' 1 2 = g := rfl
    show IsCofibrationSequence (C := C) ((ComposableArrows.mk₂ f g).map' 0 1)
      ((ComposableArrows.mk₂ f g).map' 1 2)
    rw [h01, h12]
    exact hSeq⟩

-- The `mk₂` pair satisfies the defining property from an actual sequence.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
example (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    cofiberSequenceProperty C (ComposableArrows.mk₂ f g) :=
  (mkTestObj C X Y Z f g hSeq).property

-- Both generating maps read back through the public forgetful functor.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
example (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    ((CofiberSequenceCategory.forget C).obj (mkTestObj C X Y Z f g hSeq)).map' 0 1 = f ∧
    ((CofiberSequenceCategory.forget C).obj (mkTestObj C X Y Z f g hSeq)).map' 1 2 = g :=
  ⟨rfl, rfl⟩

/-- Fully faithful forgetful functor round-trip on morphisms. -/
example (S T : CofiberSequenceCategory C) (f : S ⟶ T) :
    (CofiberSequenceCategory.fullyFaithfulForget C).preimage
      ((CofiberSequenceCategory.forget C).map f) = f :=
  (CofiberSequenceCategory.fullyFaithfulForget C).preimage_map f

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategoryTests
