/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedPushforward

/-! # Tests for pushforward between fibers of a cofibered functor -/

@[expose] public section

noncomputable section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FiberedCategoryCofiberedPushforwardTests

variable {S : Type u₁} {X : Type u₂}
  [Category.{v₁} S] [Category.{v₂} X]
  (p : X ⥤ S) [p.IsCofibered]
  {R T : S} (f : R ⟶ T)

example : p.Fiber R ⥤ p.Fiber T :=
  Functor.IsCofibered.fiberPushforwardFunctor f

example (a : p.Fiber R) : p.Fiber T :=
  Functor.IsCofibered.fiberPushforwardObj f a

example (a : p.Fiber R) (b : p.Fiber T) (v : a.1 ⟶ b.1)
    (hv : p.IsHomLift f v) :
    Functor.IsCofibered.fiberPushforwardObj f a ⟶ b :=
  Functor.IsCofibered.fiberPushforwardFactorHom f a b v hv

example :
    Functor.IsCofibered.fiberPushforwardFunctor (p := p) (𝟙 R) ≅
      𝟭 (p.Fiber R) :=
  Functor.IsCofibered.fiberPushforwardIdIso

example {U : S} (g : T ⟶ U) :
    Functor.IsCofibered.fiberPushforwardFunctor (p := p) f ⋙
        Functor.IsCofibered.fiberPushforwardFunctor g ≅
      Functor.IsCofibered.fiberPushforwardFunctor (f ≫ g) :=
  Functor.IsCofibered.fiberPushforwardCompIso f g

example : Pseudofunctor (LocallyDiscrete S) Cat.{v₂, u₂} :=
  Functor.IsCofibered.fiberPseudofunctor (p := p)

end CategoryTheory.FiberedCategoryCofiberedPushforwardTests

end
