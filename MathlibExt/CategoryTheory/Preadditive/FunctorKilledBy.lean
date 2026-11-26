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

/-!
# Componentwise annihilation in a functor category

Let C be any category and D a preadditive category. The functor category
C ⥤ D is preadditive, with addition of natural transformations computed
at each object. If m∈ℕ annihilates the identity of every value F(X),
then it annihilates the identity natural transformation of F.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory
namespace CategoryTheory.Preadditive
variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- Let C be a category, D preadditive, F:C → D a functor and m∈ℕ.
If m•1_{F(X)}=0 for every X in C, then m•1_F=0 as a natural
transformation in the preadditive functor category: F is killed by m. -/
theorem isKilledBy_functor_of_components (F : C ⥤ D) (m : ℕ)
    (hF : ∀ X, IsKilledBy (F.obj X) m) : IsKilledBy F m := by
  change m • (𝟙 F : F ⟶ F) = 0
  ext X
  exact hF X

end CategoryTheory.Preadditive
