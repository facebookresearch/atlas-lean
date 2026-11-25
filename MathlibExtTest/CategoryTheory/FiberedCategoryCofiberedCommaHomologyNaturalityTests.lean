/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaHomologyNaturality

/-! # Tests for naturality of cofibered comma/fiber homology -/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Functor.IsCofibered

universe u vA uA

namespace CategoryTheory.Functor.IsCofiberedCommaHomologyNaturalityTests

variable {S X : Type u} [Category.{0} S] [Category.{0} X]
  {p : X ⥤ S} [p.IsCofibered]
  {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{u} A] [CategoryWithHomology A]

example (R : A) (n : ℕ) :
    costructuredHomologyFunctor (p := p) A R n ≅
      fiberHomologyFunctor (p := p) A R n :=
  costructuredFiberHomologyNatIso (p := p) A R n

end CategoryTheory.Functor.IsCofiberedCommaHomologyNaturalityTests

end
