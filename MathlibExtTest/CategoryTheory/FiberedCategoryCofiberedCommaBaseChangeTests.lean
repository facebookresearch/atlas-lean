/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaBaseChange

/-! # Tests for cofibered comma base change -/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Functor.IsCofibered

universe vS vX uS uX

namespace CategoryTheory.Functor.IsCofiberedCommaBaseChangeTests

variable {S : Type uS} {X : Type uX}
  [Category.{vS} S] [Category.{vX} X]
  {p : X ⥤ S} [p.IsCofibered]

example {s t : S} (g : s ⟶ t) :
    CostructuredArrow.map g ⋙ costructuredToFiber (p := p) t ≅
      costructuredToFiber (p := p) s ⋙
        fiberPushforwardFunctor (p := p) g :=
  costructuredToFiberBaseChangeIso (p := p) g

end CategoryTheory.Functor.IsCofiberedCommaBaseChangeTests

end
