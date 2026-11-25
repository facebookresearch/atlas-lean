/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Monoidal.Closed.UncurryComposition

set_option autoImplicit false

universe u v
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

example {A X Y H : C} (g : A ⟶ H) (f : H ⟶ (ihom X).obj Y) :
    (β_ A X).hom ≫ MonoidalClosed.uncurry (g ≫ f) =
      (β_ X A).inv ≫ (X ◁ g) ≫ MonoidalClosed.uncurry f :=
  MonoidalClosed.braiding_uncurry_comp g f

#print axioms CategoryTheory.MonoidalClosed.braiding_uncurry_comp
