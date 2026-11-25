/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.InitialVanishing

/-! # Tests for initial-category homology vanishing -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v vA u uA

namespace CategoryTheory.CategoryHomologyInitialVanishingTests

variable {C : Type u} [Category.{v} C]
  {A : Type uA} [Category.{vA} A] [Abelian A]
  [HasCoproducts.{max u v} A]
  (M : CategoryTheory.Functor C A)
  [∀ {X Y : C} (f : X ⟶ Y), IsIso (M.map f)]

example (i : C) (hi : IsInitial i) :
    (CategoryTheory.nerve C).IsConnected :=
  CategoryHomology.nerveIsConnectedOfIsInitial hi

example (i : C) (hi : IsInitial i) :
    CategoryHomology.homologyWithCoefficients M 0 ≅ M.obj i :=
  CategoryHomology.homologyWithCoefficientsZeroIsoOfIsInitial M i hi

example (i : C) (hi : IsInitial i) (n : ℕ) (hn : 1 ≤ n) :
    IsZero (CategoryHomology.homologyWithCoefficients M n) :=
  CategoryHomology.isZero_homologyWithCoefficients_of_isInitial
    M i hi n hn

end CategoryTheory.CategoryHomologyInitialVanishingTests

end
