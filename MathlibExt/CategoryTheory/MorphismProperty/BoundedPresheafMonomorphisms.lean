/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.MorphismProperty.ArrowObjectProperty
public import Mathlib.CategoryTheory.Elements
public import Mathlib.SetTheory.Cardinal.Order

/-! # One bounded-monomorphism property for original presheaves

Both original total-element types have the same literal infinite site bound.
The ordinary Arrow view is derived from this single morphism property, so
filtration cells and bounded representative families use the same predicate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace CategoryTheory.MorphismProperty

/-- Original monomorphisms whose two literal total-element types are bounded
by the maximum of aleph-zero and the cardinality of the original site arrows. -/
def boundedPresheafMonomorphisms (E : Type u) [SmallCategory E] :
    MorphismProperty (Eᵒᵖ ⥤ Type u) := fun A B f =>
  Mono f ∧
    Cardinal.mk A.Elements ≤ max Cardinal.aleph0 (Cardinal.mk (CategoryTheory.Arrow E)) ∧
    Cardinal.mk B.Elements ≤ max Cardinal.aleph0 (Cardinal.mk (CategoryTheory.Arrow E))

end CategoryTheory.MorphismProperty

namespace CategoryTheory.Presheaf

/-- The ordinary Arrow view of the same bounded presheaf monomorphism property. -/
abbrev boundedMonoArrows (E : Type u) [SmallCategory E] :
    ObjectProperty (CategoryTheory.Arrow (Eᵒᵖ ⥤ Type u)) :=
  (MorphismProperty.boundedPresheafMonomorphisms E).arrowObjectProperty

end CategoryTheory.Presheaf
