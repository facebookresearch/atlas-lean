/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.MorphismProperty.CodomainRetracts

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace CategoryTheory.MorphismProperty

-- The client is generic in the category and supplies only literal Under
-- retract closure, rather than an arbitrary-arrow retract instance.
example {C : Type u} [Category.{v} C] [HasPushouts C]
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    (hcod : ∀ (X : C) (A B : Under X), Retract A B → P B.hom → P A.hom)
    {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}
    (h : RetractArrow f g) (hg : P g) : P f := by
  let : P.IsStableUnderRetracts := isStableUnderRetracts_of_codomainRetracts P hcod
  exact MorphismProperty.of_retract h hg

-- The resulting instance is usable through the native retract closure API.
example {C : Type u} [Category.{v} C] [HasPushouts C]
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    (hcod : ∀ (X : C) (A B : Under X), Retract A B → P B.hom → P A.hom) :
    P.retracts ≤ P := by
  let : P.IsStableUnderRetracts := isStableUnderRetracts_of_codomainRetracts P hcod
  exact P.retracts_le

end CategoryTheory.MorphismProperty
