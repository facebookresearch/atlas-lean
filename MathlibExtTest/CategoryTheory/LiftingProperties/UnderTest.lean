/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.LiftingProperties.Under

/-!
# Tests for lifting properties in under categories
-/

set_option autoImplicit false

open CategoryTheory

universe v u

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C]

example {K : C} {P Q : Under K} (i : P ⟶ Q)
    {X Y : C} (p : X ⟶ Y) :
    HasLiftingProperty i.right p ↔
      ∀ (t : K ⟶ X), HasLiftingProperty i
        (Under.homMk p rfl : Under.mk t ⟶ Under.mk (t ≫ p)) :=
  hasLiftingProperty_right_iff_forall i p

end CategoryTheory.Under
