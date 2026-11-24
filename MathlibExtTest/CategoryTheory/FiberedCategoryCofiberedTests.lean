/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.Cofibered

/-! # Tests for cofibered categories -/

@[expose] public section

noncomputable section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FiberedCategoryCofiberedTests

variable {S : Type u₁} {X : Type u₂}
  [Category.{v₁} S] [Category.{v₂} X]
  (p : X ⥤ S) [p.IsCofibered]
  {a : X} {R T : S} (ha : p.obj a = R) (f : R ⟶ T)

example : X :=
  Functor.IsCofibered.pushforwardObj ha f

example : a ⟶ Functor.IsCofibered.pushforwardObj ha f :=
  Functor.IsCofibered.pushforwardMap ha f

example : p.IsStronglyCocartesian f
    (Functor.IsCofibered.pushforwardMap ha f) :=
  inferInstance

example : p.obj (Functor.IsCofibered.pushforwardObj ha f) = T :=
  Functor.IsCofibered.pushforwardObj_proj ha f

end CategoryTheory.FiberedCategoryCofiberedTests

end
