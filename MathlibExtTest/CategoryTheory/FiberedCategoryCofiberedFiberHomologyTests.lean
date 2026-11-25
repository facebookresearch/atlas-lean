/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedFiberHomology

/-! # Tests for homology coefficients of a cofibered category -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.FiberedCategoryCofiberedFiberHomologyTests

variable {S : Type u₁} {X : Type u₂}
  [Category.{v₁} S] [Category.{v₂} X]
  (p : CategoryTheory.Functor X S) [p.IsCofibered]
  (A : Type u₃) [Category.{v₃} A] [Preadditive A]
  [HasCoproducts.{max u₂ v₂} A] [CategoryWithHomology A]
  (R : A) (n : ℕ)

example : CategoryTheory.Functor S A :=
  Functor.IsCofibered.fiberHomologyFunctor (p := p) A R n

end CategoryTheory.FiberedCategoryCofiberedFiberHomologyTests

end
