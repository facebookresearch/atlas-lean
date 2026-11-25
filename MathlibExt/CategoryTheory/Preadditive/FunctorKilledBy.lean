/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module
public import MathlibExt.CategoryTheory.Preadditive.KilledBy
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # Torsion of the actual components determines torsion of a functor object -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory
namespace CategoryTheory.Preadditive
variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- A functor object is killed by `m` if every actual value object is killed by `m`. -/
theorem isKilledBy_functor_of_components (F : C ⥤ D) (m : ℕ)
    (hF : ∀ X, IsKilledBy (F.obj X) m) : IsKilledBy F m := by
  change m • (𝟙 F : F ⟶ F) = 0
  ext X
  exact hF X

end CategoryTheory.Preadditive
