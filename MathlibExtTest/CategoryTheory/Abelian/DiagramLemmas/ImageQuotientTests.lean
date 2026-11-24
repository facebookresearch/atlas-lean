/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Abelian.DiagramLemmas.ImageQuotient

/-! # Tests for quotients of nested images -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace CategoryTheory.ImageQuotientTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A X B T : C} (a : A ⟶ B) (x : X ⟶ B) (b : B ⟶ T)

example : image (a ≫ b) ⟶ image b := imageCompMap a b

example : Mono (imageCompMap a b) := inferInstance

example (hxb : x ≫ b = 0) (hS : (ShortComplex.mk x b hxb).Exact) :
    cokernel (biprod.desc a x) ≅ cokernel (imageCompMap a b) :=
  imageQuotientBiprodIso a x b hxb hS

example (hxb : x ≫ b = 0) (hS : (ShortComplex.mk x b hxb).Exact) :
    factorThruImage b ≫ imageToBiprodQuotient a x b hxb hS =
      cokernel.π (biprod.desc a x) :=
  factorThruImage_imageToBiprodQuotient a x b hxb hS

end CategoryTheory.ImageQuotientTests

end
