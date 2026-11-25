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

/-! # Actual object torsion from the actual coefficient ring's characteristic -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Preadditive
namespace ModuleCat
variable {R : Type u} [Ring R]

/-- The actual scalar-ring equation kills every element of an actual module over that ring. -/
theorem nsmul_eq_zero_of_natCast (A : ModuleCat.{w} R) (m : ℕ) (hm : (m : R) = 0) (x : A) :
    m • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul R, hm, zero_smul]

/-- The actual scalar-ring equation kills the identity of the actual module object. -/
theorem isKilledBy_of_natCast (A : ModuleCat.{w} R) (m : ℕ) (hm : (m : R) = 0) :
    IsKilledBy A m := by
  change m • (𝟙 A : A ⟶ A) = 0
  ext x
  exact nsmul_eq_zero_of_natCast A m hm x

end ModuleCat
