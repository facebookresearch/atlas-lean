/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Category.Grp.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Additivity of integer tensor products of abelian groups

In the integer-tensor monoidal category `Ab`, tensoring morphisms is
additive in each variable. Thus each left and right tensor functor is
additive, making the monoidal category monoidal preadditive.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory

namespace AddCommGrpCat

set_option backward.isDefEq.respectTransparency.types false in
/-- For abelian groups in universe `s`, tensor product over `ℤ` is
additive in each morphism variable. The category `AddCommGrpCat.{s}`
therefore has a monoidal preadditive structure for its integer tensor product. -/
instance monoidalPreadditive.{s} : MonoidalPreadditive AddCommGrpCat.{s} where
  whiskerLeft_zero := by
    intros
    apply ConcreteCategory.ext_apply
    intro t
    induction t using TensorProduct.inductionOn <;> simp_all
  zero_whiskerRight := by
    intros
    apply ConcreteCategory.ext_apply
    intro t
    induction t using TensorProduct.inductionOn <;> simp_all
  whiskerLeft_add := by
    intros
    apply ConcreteCategory.ext_apply
    intro t
    induction t using TensorProduct.inductionOn <;> simp_all [TensorProduct.tmul_add] ; abel
  add_whiskerRight := by
    intros
    apply ConcreteCategory.ext_apply
    intro t
    induction t using TensorProduct.inductionOn <;> simp_all [TensorProduct.add_tmul] ; abel

end AddCommGrpCat
