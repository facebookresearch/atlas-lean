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
# Additivity of the integer tensor product of abelian groups

The tensor product over `ℤ` makes `AddCommGrpCat` monoidal preadditive.
In particular, tensoring with an abelian group is an additive functor.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory

namespace AddCommGrpCat

set_option backward.isDefEq.respectTransparency.types false in
/-- The integer tensor product of abelian groups is additive in each variable. -/
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
