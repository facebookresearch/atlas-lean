/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantTensorPowers

set_option autoImplicit false
noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace MathlibExtTest.CofibrantTensorPowersTests

section WeakContracts

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [CategoryWithCofibrations C] [HasInitial C] [HasPushouts C]
  [(cofibrations C).RespectsIso]

example
    (hPP : PushoutProductLe (cofibrations C) (cofibrations C) (cofibrations C))
    (X Y : C) [IsCofibrant X] [IsCofibrant Y]
    [PreservesColimit (Functor.empty.{0} C) (tensorLeft (⊥_ C))]
    [PreservesColimit (Functor.empty.{0} C) (tensorLeft X)]
    [PreservesColimit (Functor.empty.{0} C) (tensorRight Y)] :
    IsCofibrant (X ⊗ Y) :=
  isCofibrant_tensorObj_of_pushoutProduct hPP X Y

example
    (hPP : PushoutProductLe (cofibrations C) (cofibrations C) (cofibrations C))
    (K : C) [IsCofibrant K] [IsCofibrant (𝟙_ C)]
    [PreservesColimit (Functor.empty.{0} C) (tensorLeft (⊥_ C))]
    [∀ n : ℕ, PreservesColimit (Functor.empty.{0} C)
      (tensorLeft (TensorPower.tensorPowObj K n))]
    [PreservesColimit (Functor.empty.{0} C) (tensorRight K)] (r : ℕ) :
    IsCofibrant (TensorPower.tensorPowObj K r) :=
  isCofibrant_tensorPowObj_of_pushoutProduct hPP K r

omit [(cofibrations C).RespectsIso] in
example (P : MorphismProperty C) [P.RespectsIso]
    (hPP : PushoutProductLe (cofibrations C) P P)
    (K : C) [IsCofibrant K] {A B : C} (j : A ⟶ B)
    [PreservesColimit (Functor.empty.{0} C) (tensorRight A)]
    [PreservesColimit (Functor.empty.{0} C) (tensorRight B)]
    (hj : P j) : P (𝟙 K ⊗ₘ j) := by
  simpa only [id_tensorHom] using whiskerLeft_mem_of_isCofibrant P hPP K j hj

example (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [CategoryWithCofibrations C] [HasInitial C] [HasPushouts C] : True := by
  fail_if_success have : ModelCategory C := inferInstance
  fail_if_success have : MonoidalClosed C := inferInstance
  fail_if_success have : SymmetricCategory C := inferInstance
  fail_if_success have : HasPullbacks C := inferInstance
  trivial

end WeakContracts

section SelectedModel

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [ModelCategory C]
  [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

example :
    (inferInstance : CategoryWithCofibrations C) =
      (inferInstance : ModelCategory C).categoryWithCofibrations :=
  rfl

example :
    (inferInstance : HasFiniteColimits C) =
      (inferInstance : ModelCategory C).cm1b :=
  rfl

example (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    IsCofibrant (X ⊗ Y) :=
  IsClosedSymmetricMonoidalModelCategory.isCofibrant_tensorObj X Y

example (K : C) [IsCofibrant K] [IsCofibrant (𝟙_ C)] (r : ℕ) :
    IsCofibrant (TensorPower.tensorPowObj K r) :=
  IsClosedSymmetricMonoidalModelCategory.isCofibrant_tensorPowObj K r

example (K : C) [IsCofibrant K] {A B : C} (j : A ⟶ B)
    (hj : cofibrations C j) : cofibrations C (𝟙 K ⊗ₘ j) := by
  simpa only [id_tensorHom] using
    IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_cofibrations K j hj

example (K : C) [IsCofibrant K] {A B : C} (j : A ⟶ B)
    (hj : trivialCofibrations C j) : trivialCofibrations C (𝟙 K ⊗ₘ j) := by
  simpa only [id_tensorHom] using
    IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_trivialCofibrations K j hj

end SelectedModel

section UniverseCorners

example (C₁ : Type 1) [Category.{0} C₁] [MonoidalCategory C₁]
    [CategoryWithCofibrations C₁] [HasInitial C₁] [HasPushouts C₁]
    [(cofibrations C₁).RespectsIso]
    (hPP : PushoutProductLe (cofibrations C₁) (cofibrations C₁) (cofibrations C₁))
    (K : C₁) [IsCofibrant K] [IsCofibrant (𝟙_ C₁)]
    [PreservesColimit (Functor.empty.{0} C₁) (tensorLeft (⊥_ C₁))]
    [∀ n : ℕ, PreservesColimit (Functor.empty.{0} C₁)
      (tensorLeft (TensorPower.tensorPowObj K n))]
    [PreservesColimit (Functor.empty.{0} C₁) (tensorRight K)] (r : ℕ) :
    IsCofibrant (TensorPower.tensorPowObj K r) :=
  isCofibrant_tensorPowObj_of_pushoutProduct hPP K r

example (C₀ : Type) [Category.{1} C₀] [MonoidalCategory C₀]
    [CategoryWithCofibrations C₀] [HasInitial C₀] [HasPushouts C₀]
    [(cofibrations C₀).RespectsIso]
    (hPP : PushoutProductLe (cofibrations C₀) (cofibrations C₀) (cofibrations C₀))
    (K : C₀) [IsCofibrant K] [IsCofibrant (𝟙_ C₀)]
    [PreservesColimit (Functor.empty.{0} C₀) (tensorLeft (⊥_ C₀))]
    [∀ n : ℕ, PreservesColimit (Functor.empty.{0} C₀)
      (tensorLeft (TensorPower.tensorPowObj K n))]
    [PreservesColimit (Functor.empty.{0} C₀) (tensorRight K)] (r : ℕ) :
    IsCofibrant (TensorPower.tensorPowObj K r) :=
  isCofibrant_tensorPowObj_of_pushoutProduct hPP K r

end UniverseCorners

#print axioms isCofibrant_tensorObj_of_pushoutProduct
#print axioms isCofibrant_tensorPowObj_of_pushoutProduct
#print axioms whiskerLeft_mem_of_isCofibrant
#print axioms IsClosedSymmetricMonoidalModelCategory.isCofibrant_tensorObj
#print axioms IsClosedSymmetricMonoidalModelCategory.isCofibrant_tensorPowObj
#print axioms IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_cofibrations
#print axioms IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_trivialCofibrations

end MathlibExtTest.CofibrantTensorPowersTests
