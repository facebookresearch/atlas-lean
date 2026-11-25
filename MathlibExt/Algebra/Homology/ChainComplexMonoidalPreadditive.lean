/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality

/-!
# Monoidal preadditivity for chain complexes

The total-complex tensor product on `ChainComplex C ℕ` is additive in each
variable. This factors the repeated local instance proofs into one named
reusable construction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  [HasZeroObject C] [HasFiniteCoproducts C]
  [∀ Z : C, PreservesFiniteCoproducts (tensorLeft Z)]
  [∀ Z : C, PreservesFiniteCoproducts (tensorRight Z)]

noncomputable local instance chainComplexMonoidalCategoryForPreadditive :
    MonoidalCategory (ChainComplex C ℕ) :=
  HomologicalComplex.monoidalCategory C (ComplexShape.down ℕ)

/-- Preadditivity of the total-complex monoidal structure on chain complexes,
proved directly from the tensor-hom formulas. Install locally via
`local instance ... := HomologicalComplex.chainComplexMonoidalPreadditive`. -/
theorem chainComplexMonoidalPreadditive :
    MonoidalPreadditive (ChainComplex C ℕ) where
  whiskerLeft_zero := by
    intros X Y Z
    change HomologicalComplex.tensorHom (𝟙 X) (0 : Y ⟶ Z) = 0
    exact HomologicalComplex.tensorHom_zero (𝟙 X)
  zero_whiskerRight := by
    intros X Y Z
    change HomologicalComplex.tensorHom (0 : Y ⟶ Z) (𝟙 X) = 0
    exact HomologicalComplex.zero_tensorHom (𝟙 X)
  whiskerLeft_add := by
    intros X Y Z f g
    change HomologicalComplex.tensorHom (𝟙 X) (f + g) =
      HomologicalComplex.tensorHom (𝟙 X) f +
        HomologicalComplex.tensorHom (𝟙 X) g
    have h := HomologicalComplex.tensorHom_sum (𝟙 X)
      (s := (Finset.univ : Finset Bool))
      (g := fun b => if b then f else g)
    rw [Fintype.sum_bool] at h
    simpa using h
  add_whiskerRight := by
    intros X Y Z f g
    change HomologicalComplex.tensorHom (f + g) (𝟙 X) =
      HomologicalComplex.tensorHom f (𝟙 X) +
        HomologicalComplex.tensorHom g (𝟙 X)
    have h := HomologicalComplex.sum_tensorHom
      (s := (Finset.univ : Finset Bool))
      (f := fun b => if b then f else g) (g := 𝟙 X)
    rw [Fintype.sum_bool] at h
    simpa using h

end HomologicalComplex
