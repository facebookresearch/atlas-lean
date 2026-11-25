/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaHomology

/-! # Tests for the cofibered comma/fiber homology comparison -/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Functor.IsCofibered

universe u vA uA

namespace CategoryTheory.Functor.IsCofiberedCommaHomologyTests

variable {S X : Type u} [Category.{0} S] [Category.{0} X]
  {p : X ⥤ S} [p.IsCofibered]
  {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{u} A] [CategoryWithHomology A]

example (s : S) (R : A) (n : ℕ) :
    (nerve (CostructuredArrow p s)).homology R n ≅
      (nerve (p.Fiber s)).homology R n :=
  costructuredFiberHomologyIso (p := p) A s R n

end CategoryTheory.Functor.IsCofiberedCommaHomologyTests

end
