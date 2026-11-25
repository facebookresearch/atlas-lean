/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.MorphismProperty.ArrowObjectProperty
public import Mathlib.CategoryTheory.Presentable.Comma

/-!
# Accessible classes of morphisms

This file defines accessibility of a morphism class through its full
subcategory of the arrow category and the accessibility of that inclusion.
It is distinct from literal smallness and from closure under filtered
colimits.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

open CategoryTheory

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- A morphism class is cardinal-accessible when its full arrow subcategory
is cardinal-accessible and its inclusion into the arrow category is a
cardinal-accessible functor. -/
class IsCardinalAccessible (W : MorphismProperty C) (κ : Cardinal.{w})
    [Fact κ.IsRegular] : Prop where
  isCardinalAccessibleCategory :
    CategoryTheory.IsCardinalAccessibleCategory
      W.arrowObjectProperty.FullSubcategory κ
  isCardinalAccessible_ι :
    Functor.IsCardinalAccessible W.arrowObjectProperty.ι κ

attribute [instance]
  IsCardinalAccessible.isCardinalAccessibleCategory
  IsCardinalAccessible.isCardinalAccessible_ι

/-- A morphism class is accessible when it is cardinal-accessible for some
regular cardinal. -/
@[pp_with_univ]
class IsAccessible (W : MorphismProperty C) : Prop where
  exists_cardinal (W) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), W.IsCardinalAccessible κ

end CategoryTheory.MorphismProperty
