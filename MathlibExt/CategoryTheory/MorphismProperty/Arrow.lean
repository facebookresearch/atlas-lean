/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Projections from categories of arrows with a morphism property

The right-hand component determines a square whose target structure morphism
is a monomorphism.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty.Arrow

variable {C : Type u} [Category.{v} C]
variable (P Q W : MorphismProperty C) [Q.IsMultiplicative] [W.IsMultiplicative]

/-- The projection to the codomain is faithful on any category of arrows whose
structure morphisms are monomorphisms. -/
theorem rightProjection_faithful (hP : P ≤ monomorphisms C) :
    (MorphismProperty.Arrow.forget P Q W ⋙ CategoryTheory.Arrow.rightFunc).Faithful := by
  constructor
  intro X Y f g h
  change f.right = g.right at h
  let _ : Mono Y.hom := hP Y.hom Y.prop
  apply MorphismProperty.Arrow.Hom.ext
  · apply (cancel_mono Y.hom).1
    rw [MorphismProperty.Arrow.w f, MorphismProperty.Arrow.w g, h]
  · exact h

end CategoryTheory.MorphismProperty.Arrow
