/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braiding and uncurrying composites

In a symmetric monoidal closed category, uncurrying a composite coefficient
map commutes with the source braiding. The resulting formula uses the
inverse swapped braiding, tensoring of the first map and uncurrying of the
second, combining symmetry with uncurrying naturality.
-/

set_option autoImplicit false
noncomputable section

namespace CategoryTheory.MonoidalClosed

open CategoryTheory MonoidalCategory
universe uC vC
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

/-- Every original closed coefficient composite retains the source braid and whole uncurry. -/
theorem braiding_uncurry_comp {A X Y H : C}
    (g : A ⟶ H) (f : H ⟶ (ihom X).obj Y) :
    (β_ A X).hom ≫ MonoidalClosed.uncurry (g ≫ f) =
      (β_ X A).inv ≫ (X ◁ g) ≫ MonoidalClosed.uncurry f := by
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding X A, MonoidalClosed.uncurry_natural_left]

end CategoryTheory.MonoidalClosed
