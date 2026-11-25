/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedFiberHomologyBar

/-! # Tests for the category bar on homology of cofibered fibers -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.FiberedCategoryCofiberedFiberHomologyBarTests

variable {S : Type u₁} {X : Type u₂}
  [Category.{v₁} S] [Category.{v₂} X]
  (p : CategoryTheory.Functor X S) [p.IsCofibered]
  (A : Type u₃) [Category.{v₃} A] [Abelian A]
  [HasCoproducts.{max u₂ v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (R : A)

example (q : ℕ) : SimplicialObject A :=
  Functor.IsCofibered.fiberHomologyBarSimplicial (p := p) A R q

example (q : ℕ) : ChainComplex A ℕ :=
  Functor.IsCofibered.fiberHomologyBarComplex (p := p) A R q

example (pDegree qDegree : ℕ) : A :=
  Functor.IsCofibered.fiberHomologyCategoryHomology
    (p := p) A R pDegree qDegree

end CategoryTheory.FiberedCategoryCofiberedFiberHomologyBarTests

end
