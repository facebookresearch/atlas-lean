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

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.Rat.Cast.CharZero
public import MathlibExt.Algebra.Category.ModuleCat.PIDGlobalDimension

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

variable {R : Type u} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] [Small.{v} R]

example (M : ModuleCat.{v} R) : HasProjectiveDimensionLE M 1 :=
  hasProjectiveDimensionLE_one_of_isPrincipalIdealRing M

example [HasExt.{w} (ModuleCat.{v} R)]
    (M A : ModuleCat.{v} R) (p : ℕ) (hp : 2 ≤ p) :
    Subsingleton (Abelian.Ext.{w} M A p) :=
  subsingleton_ext_of_two_le_of_isPrincipalIdealRing M A p hp

example [HasExt.{w} (ModuleCat.{v} R)]
    (M A : ModuleCat.{v} R) (p : ℕ) (hp : 2 ≤ p) :
    IsZero (AddCommGrpCat.of (Abelian.Ext.{w} M A p)) :=
  isZero_ext_of_two_le_of_isPrincipalIdealRing M A p hp

example [HasExt.{w} (ModuleCat.{v} R)]
    (M A : ModuleCat.{v} R) (p : ℕ) (hp : 2 ≤ p)
    (x : Abelian.Ext.{w} M A p) : x = 0 :=
  ext_eq_zero_of_two_le_of_isPrincipalIdealRing M A p hp x

section Integer

variable (M A : ModuleCat.{v} ℤ)

example : HasProjectiveDimensionLE M 1 :=
  hasProjectiveDimensionLE_one_of_isPrincipalIdealRing M

example : Subsingleton (Abelian.Ext.{v} M A 2) :=
  subsingleton_ext_of_two_le_of_isPrincipalIdealRing M A 2 le_rfl

example : IsZero (AddCommGrpCat.of (Abelian.Ext.{v} M A 2)) :=
  isZero_ext_of_two_le_of_isPrincipalIdealRing M A 2 le_rfl

example (x : Abelian.Ext.{v} M A 5) : x = 0 :=
  ext_eq_zero_of_two_le_of_isPrincipalIdealRing M A 5 (by decide) x

example : HasProjectiveDimensionLT M 3 := by
  let _ : HasProjectiveDimensionLE M 1 :=
    hasProjectiveDimensionLE_one_of_isPrincipalIdealRing M
  infer_instance

end Integer

section IntegerInfinite

variable (A : ModuleCat.{0} ℤ)

example : HasProjectiveDimensionLE
    (ModuleCat.of ℤ (ℕ → ℤ) : ModuleCat.{0} ℤ) 1 :=
  hasProjectiveDimensionLE_one_of_isPrincipalIdealRing _

example : Subsingleton
    (Abelian.Ext.{0}
      (ModuleCat.of ℤ (ℕ → ℤ) : ModuleCat.{0} ℤ) A 3) :=
  subsingleton_ext_of_two_le_of_isPrincipalIdealRing _ A 3 (by decide)

end IntegerInfinite

section Rational

example (M : ModuleCat.{0} ℚ) : HasProjectiveDimensionLE M 1 :=
  hasProjectiveDimensionLE_one_of_isPrincipalIdealRing M

example : HasProjectiveDimensionLE
    (ModuleCat.of ℚ (ℕ → ℚ) : ModuleCat.{0} ℚ) 1 :=
  hasProjectiveDimensionLE_one_of_isPrincipalIdealRing _

end Rational

end ModuleCat

end
