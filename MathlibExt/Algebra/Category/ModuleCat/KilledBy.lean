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
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Modules annihilated by a vanishing natural scalar

Let R be a ring and m a natural number whose image in R is zero. Then m·x = 0 for every
element of every R-module. Equivalently, m times the identity morphism of that module object
is zero. The ring and module carrier may lie in independent universes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Preadditive
namespace ModuleCat
variable {R : Type u} [Ring R]

/-- A vanishing natural scalar annihilates module elements.

If the natural-number cast of m in R is zero, then m·x = 0 for every x in an R-module A. -/
theorem nsmul_eq_zero_of_natCast (A : ModuleCat.{w} R) (m : ℕ) (hm : (m : R) = 0) (x : A) :
    m • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul R, hm, zero_smul]

/-- A vanishing natural scalar annihilates the module identity.

If (m : R) = 0, the module object A satisfies IsKilledBy A m: the natural-number multiple
m·id_A is the zero morphism. -/
theorem isKilledBy_of_natCast (A : ModuleCat.{w} R) (m : ℕ) (hm : (m : R) = 0) :
    IsKilledBy A m := by
  change m • (𝟙 A : A ⟶ A) = 0
  ext x
  exact nsmul_eq_zero_of_natCast A m hm x

end ModuleCat
