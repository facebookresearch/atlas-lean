/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Naive fibrations and fibrant objects for a specified anodyne class

The specified class has naive fibrations given by its native right lifting
class. Naive fibrant objects are those whose terminal maps belong to that
class. Equivalently, maps from sources of specified anodyne maps extend to
their targets. This predicate is independent of the chosen terminal object.

These primitives apply to any specified morphism class. Applied to an exact
cylinder's anodyne system in a presheaf category, they give Cisinski's
Definition 2.4.18 (July 30, 2026 version).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (An : MorphismProperty C)

/-- The right lifting class of the specified anodyne maps. -/
abbrev naiveFibrations : MorphismProperty C := An.rlp

variable [HasTerminal C]

/-- Objects whose terminal maps lift against every specified anodyne map. -/
def naiveFibrantObjects : ObjectProperty C :=
  fun X ↦ An.naiveFibrations (terminal.from X)

lemma naiveFibrantObjects_iff (X : C) :
    An.naiveFibrantObjects X ↔ An.naiveFibrations (terminal.from X) :=
  Iff.rfl

/-- For a terminal target, right lifting is exactly the extension property. -/
lemma naiveFibrantObjects_iff_extensions (X : C) :
    An.naiveFibrantObjects X ↔
      ∀ {A B : C} (i : A ⟶ B), An i →
        ∀ f : A ⟶ X, ∃ g : B ⟶ X, i ≫ g = f := by
  constructor
  · intro h A B i hi f
    have hip : HasLiftingProperty i (terminal.from X) := h i hi
    have sq : CommSq f i (terminal.from X) (terminal.from B) :=
      ⟨terminal.hom_ext _ _⟩
    have : sq.HasLift := hip.sq_hasLift sq
    exact ⟨sq.lift, sq.fac_left⟩
  · intro h A B i hi
    refine ⟨?_⟩
    intro f g sq
    obtain ⟨l, hl⟩ := h i hi f
    exact CommSq.HasLift.mk'
      { l := l
        fac_left := hl
        fac_right := terminal.hom_ext _ _ }

/-- Any map to any terminal object tests the same naive fibrancy predicate. -/
lemma naiveFibrantObjects_iff_of_isTerminal {X T : C} (p : X ⟶ T)
    (hT : IsTerminal T) :
    An.naiveFibrantObjects X ↔ An.naiveFibrations p := by
  change An.rlp (terminal.from X) ↔ An.rlp p
  symm
  apply An.rlp.arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (IsTerminal.uniqueUpToIso hT terminalIsTerminal)

end CategoryTheory.MorphismProperty
