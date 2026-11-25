/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.WeightedBar

/-! # Tests for the terminal-weight/coefficient-bar comparison -/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.CategoryHomology

universe v u vA uA

namespace CategoryTheory.CategoryHomologyWeightedBarTests

variable {C : Type u} [Category.{v} C]
  {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{max u v} A]
  (M : C ⥤ A)

example (n : ℕ) :
    StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) M n ≅
      coefficientBarObj M n :=
  terminalWeightCoefficientBarDegreeIso M n

example (n : ℕ) (i : Fin (n + 2)) :
    (terminalWeightCoefficientBarDegreeIso M (n + 1)).hom ≫
        coefficientBarFace M i =
      StrictOrdinaryWeightedBar.wbarδ
          (CategoryBar.replUnit C) M n i ≫
        (terminalWeightCoefficientBarDegreeIso M n).hom :=
  terminalWeightCoefficientBarDegreeIso_face M n i

example : terminalWeightBarComplex M ≅ coefficientBarComplex M :=
  terminalWeightCoefficientBarComplexIso M

end CategoryTheory.CategoryHomologyWeightedBarTests

end
