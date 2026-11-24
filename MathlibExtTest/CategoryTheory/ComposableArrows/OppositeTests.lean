/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: toskua
Co-Authored-By: Roy Toskas <uife8x27@avocadolabs.ai>
-/

module

import MathlibExt.CategoryTheory.ComposableArrows.Opposite

/-!
# ComposableArrows opposite public contract

Compile-level pin: reversal commutes with pushing a chain forward along a
functor.
-/

open CategoryTheory

universe u₁ v₁ u₂ v₂

namespace MathlibExtTest.CategoryTheory.ComposableArrows.OppositeTests

variable {C' : Type u₁} {B' : Type u₂} [Category.{v₁} C'] [Category.{v₂} B']

example (H : C' ⥤ B') (n : ℕ) (X : ComposableArrows C' n) :
    ComposableArrows.op (X ⋙ H) = ComposableArrows.op X ⋙ H.op :=
  ComposableArrows.op_mapFunctor H n X

end MathlibExtTest.CategoryTheory.ComposableArrows.OppositeTests
