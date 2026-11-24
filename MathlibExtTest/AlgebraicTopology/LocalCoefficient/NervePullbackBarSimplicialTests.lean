/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarSimplicial

/-!
# Tests for nerve-pullback bar simplicial and chain assembly

These clients pin the independent-universe Data, simplicial-object, and
unnormalized alternating-complex shapes and their computation formulas. The
identity nerve map is instantiated only as a shape test; no comparison
equality or isomorphism is claimed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarSimplicialTests

universe vG uG vA uA

section Generic

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)
variable [HasCoproducts.{max uG vG} A]

example : SimplicialObject.Data A := nervePullbackCoefficientData φ M

example (n : ℕ) : (nervePullbackCoefficientData φ M).obj n =
    nervePullbackCoefficientObj φ M n :=
  nervePullbackCoefficientData_obj φ M n

example {n : ℕ} (i : Fin (n + 2)) :
    (nervePullbackCoefficientData φ M).δ i =
      nervePullbackCoefficientFace φ M i :=
  nervePullbackCoefficientData_δ φ M i

example {n : ℕ} (i : Fin (n + 1)) :
    (nervePullbackCoefficientData φ M).σ i =
      nervePullbackCoefficientDegeneracy φ M i :=
  nervePullbackCoefficientData_σ φ M i

example : SimplicialObject A := nervePullbackCoefficientSimplicial φ M

example (n : ℕ) :
    (nervePullbackCoefficientSimplicial φ M).obj
        (op (SimplexCategory.mk n)) =
      nervePullbackCoefficientObj φ M n :=
  nervePullbackCoefficientSimplicial_obj φ M n

example {n : ℕ} (i : Fin (n + 2)) :
    (nervePullbackCoefficientSimplicial φ M).map
        (SimplexCategory.δ i).op =
      nervePullbackCoefficientFace φ M i :=
  nervePullbackCoefficientSimplicial_map_δ φ M i

example {n : ℕ} (i : Fin (n + 1)) :
    (nervePullbackCoefficientSimplicial φ M).map
        (SimplexCategory.σ i).op =
      nervePullbackCoefficientDegeneracy φ M i :=
  nervePullbackCoefficientSimplicial_map_σ φ M i

section Preadditive

variable [Preadditive A]

example : ChainComplex A ℕ := nervePullbackCoefficientComplex φ M

example (n : ℕ) : (nervePullbackCoefficientComplex φ M).X n =
    nervePullbackCoefficientObj φ M n :=
  nervePullbackCoefficientComplex_X φ M n

example (n : ℕ) :
    (nervePullbackCoefficientComplex φ M).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        nervePullbackCoefficientFace φ M i :=
  nervePullbackCoefficientComplex_d φ M n

end Preadditive

end Generic

section IdentityNerveShape

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable (M : G ⥤ A)
variable [HasCoproducts.{max uG vG} A]

example : SimplicialObject.Data A :=
  nervePullbackCoefficientData (𝟙 (CategoryTheory.nerve G)) M

example : SimplicialObject A :=
  nervePullbackCoefficientSimplicial (𝟙 (CategoryTheory.nerve G)) M

example (n : ℕ) :
    (nervePullbackCoefficientSimplicial
        (𝟙 (CategoryTheory.nerve G)) M).obj
          (op (SimplexCategory.mk n)) =
      nervePullbackCoefficientObj (𝟙 (CategoryTheory.nerve G)) M n :=
  nervePullbackCoefficientSimplicial_obj
    (𝟙 (CategoryTheory.nerve G)) M n

example {n : ℕ} (i : Fin (n + 2)) :
    (nervePullbackCoefficientSimplicial
        (𝟙 (CategoryTheory.nerve G)) M).map
          (SimplexCategory.δ i).op =
      nervePullbackCoefficientFace (𝟙 (CategoryTheory.nerve G)) M i :=
  nervePullbackCoefficientSimplicial_map_δ
    (𝟙 (CategoryTheory.nerve G)) M i

example {n : ℕ} (i : Fin (n + 1)) :
    (nervePullbackCoefficientSimplicial
        (𝟙 (CategoryTheory.nerve G)) M).map
          (SimplexCategory.σ i).op =
      nervePullbackCoefficientDegeneracy (𝟙 (CategoryTheory.nerve G)) M i :=
  nervePullbackCoefficientSimplicial_map_σ
    (𝟙 (CategoryTheory.nerve G)) M i

section Preadditive

variable [Preadditive A]

example : ChainComplex A ℕ :=
  nervePullbackCoefficientComplex (𝟙 (CategoryTheory.nerve G)) M

example (n : ℕ) :
    (nervePullbackCoefficientComplex
        (𝟙 (CategoryTheory.nerve G)) M).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        nervePullbackCoefficientFace
          (𝟙 (CategoryTheory.nerve G)) M i :=
  nervePullbackCoefficientComplex_d
    (𝟙 (CategoryTheory.nerve G)) M n

end Preadditive

end IdentityNerveShape

section RaisedUniverses

variable {G : Type 1} [Category.{1} G]
variable {A : Type 2} [Category.{1} A] [Preadditive A]
variable {X : SSet.{1}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)
variable [HasCoproducts.{1} A]

example : SimplicialObject.Data A := nervePullbackCoefficientData φ M

example : SimplicialObject A := nervePullbackCoefficientSimplicial φ M

example : ChainComplex A ℕ := nervePullbackCoefficientComplex φ M

end RaisedUniverses

#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientData
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientData_obj
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientData_δ
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientData_σ
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientSimplicial
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientSimplicial_obj
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientSimplicial_map_δ
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientSimplicial_map_σ
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientComplex
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientComplex_X
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientComplex_d

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarSimplicialTests
