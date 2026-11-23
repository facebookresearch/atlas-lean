/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarIdentityComparison

import MathlibExt.CategoryTheory.CategoryHomology.Constant

/-! # Tests for the identity-nerve coefficient-bar comparison -/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarIdentityComparisonTests

universe vG uG vA uA

section Generic

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable (M : G ⥤ A)
variable [HasCoproducts.{max uG vG} A]

example (n : ℕ) :
    nervePullbackCoefficientFamily (𝟙 (CategoryTheory.nerve G)) M n =
      coefficientBarFamily M n :=
  nervePullbackCoefficientFamily_id M n

example (n : ℕ) :
    nervePullbackCoefficientObj (𝟙 (CategoryTheory.nerve G)) M n =
      coefficientBarObj M n :=
  nervePullbackCoefficientObj_id M n

example {n : ℕ} (F : (CategoryTheory.nerve G) _⦋n⦌) :
    nervePullbackCoefficientι (𝟙 (CategoryTheory.nerve G)) M F =
      coefficientBarι M F :=
  nervePullbackCoefficientι_id M F

example {n : ℕ} (i : Fin (n + 2))
    (F : (CategoryTheory.nerve G) _⦋n + 1⦌) :
    nervePullbackCoefficientFaceHom
        (𝟙 (CategoryTheory.nerve G)) M i F =
      coefficientFaceHom M i F :=
  nervePullbackCoefficientFaceHom_id M i F

example {n : ℕ} (i : Fin (n + 1))
    (F : (CategoryTheory.nerve G) _⦋n⦌) :
    nervePullbackCoefficientDegeneracyHom
        (𝟙 (CategoryTheory.nerve G)) M i F =
      coefficientDegeneracyHom M i F :=
  nervePullbackCoefficientDegeneracyHom_id M i F

example {n : ℕ} (i : Fin (n + 2)) :
    nervePullbackCoefficientFace (𝟙 (CategoryTheory.nerve G)) M i =
      coefficientBarFace M i :=
  nervePullbackCoefficientFace_id M i

example {n : ℕ} (i : Fin (n + 1)) :
    nervePullbackCoefficientDegeneracy (𝟙 (CategoryTheory.nerve G)) M i =
      coefficientBarDegeneracy M i :=
  nervePullbackCoefficientDegeneracy_id M i

example :
    nervePullbackCoefficientData (𝟙 (CategoryTheory.nerve G)) M ≅
      coefficientBarData M :=
  nervePullbackCoefficientDataIdIso M

example (n : ℕ) :
    (nervePullbackCoefficientDataIdIso M).hom.app n = 𝟙 _ :=
  nervePullbackCoefficientDataIdIso_hom_app M n

example (n : ℕ) :
    (nervePullbackCoefficientDataIdIso M).inv.app n = 𝟙 _ :=
  nervePullbackCoefficientDataIdIso_inv_app M n

example :
    nervePullbackCoefficientSimplicial
        (𝟙 (CategoryTheory.nerve G)) M ≅
      coefficientBarSimplicial M :=
  nervePullbackCoefficientSimplicialIdIso M

example (n : ℕ) :
    (nervePullbackCoefficientSimplicialIdIso M).hom.app
        (op (SimplexCategory.mk n)) = 𝟙 _ :=
  nervePullbackCoefficientSimplicialIdIso_hom_app M n

example (n : ℕ) :
    (nervePullbackCoefficientSimplicialIdIso M).inv.app
        (op (SimplexCategory.mk n)) = 𝟙 _ :=
  nervePullbackCoefficientSimplicialIdIso_inv_app M n

section Preadditive

variable [Preadditive A]

example :
    nervePullbackCoefficientComplex (𝟙 (CategoryTheory.nerve G)) M ≅
      coefficientBarComplex M :=
  nervePullbackCoefficientComplexIdIso M

example (n : ℕ) :
    (nervePullbackCoefficientComplexIdIso M).hom.f n = 𝟙 _ :=
  nervePullbackCoefficientComplexIdIso_hom_f M n

example (n : ℕ) :
    (nervePullbackCoefficientComplexIdIso M).inv.f n = 𝟙 _ :=
  nervePullbackCoefficientComplexIdIso_inv_f M n

end Preadditive

end Generic

section ConstantCategoryNerve

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable [HasCoproducts.{max uG vG} A]
variable (R : A)

example :
    nervePullbackCoefficientComplex (𝟙 (CategoryTheory.nerve G))
        ((Functor.const G).obj R) ≅
      (CategoryTheory.nerve G).chainComplex R :=
  nervePullbackCoefficientComplexIdIso ((Functor.const G).obj R) ≪≫
    constantCoefficientBarComplexIso G A R

end ConstantCategoryNerve

section RaisedUniverses

variable {G : Type 1} [Category.{1} G]
variable {A : Type 2} [Category.{1} A] [Preadditive A]
variable (M : G ⥤ A) [HasCoproducts.{1} A]

example :
    nervePullbackCoefficientData (𝟙 (CategoryTheory.nerve G)) M ≅
      coefficientBarData M :=
  nervePullbackCoefficientDataIdIso M

example :
    nervePullbackCoefficientSimplicial
        (𝟙 (CategoryTheory.nerve G)) M ≅
      coefficientBarSimplicial M :=
  nervePullbackCoefficientSimplicialIdIso M

example :
    nervePullbackCoefficientComplex (𝟙 (CategoryTheory.nerve G)) M ≅
      coefficientBarComplex M :=
  nervePullbackCoefficientComplexIdIso M

end RaisedUniverses

#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientFamily_id
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientObj_id
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientι_id
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom_id
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom_id
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientFace_id
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracy_id
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientDataIdIso
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientDataIdIso_hom_app
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientDataIdIso_inv_app
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientSimplicialIdIso
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientSimplicialIdIso_hom_app
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientSimplicialIdIso_inv_app
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientComplexIdIso
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientComplexIdIso_hom_f
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientComplexIdIso_inv_f

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarIdentityComparisonTests
