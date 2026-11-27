/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedComma

/-! # Tests for cofibered right comma functors -/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Functor.IsCofibered

universe vS vX uS uX

namespace CategoryTheory.Functor.IsCofiberedCommaTests

variable {S : Type uS} {X : Type uX}
  [Category.{vS} S] [Category.{vX} X]
  {p : X ⥤ S} [p.IsCofibered]

example (s : S) : p.Fiber s ⥤ CostructuredArrow p s :=
  fiberToCostructuredArrow s

example (s : S) : CostructuredArrow p s ⥤ p.Fiber s :=
  costructuredToFiber s

example {s : S} {a b : CostructuredArrow p s} (f : a ⟶ b) :
    pushforwardMap (costructuredSourceFiber a).2 a.hom ≫
        ((costructuredToFiber s).map f).1 =
      f.left ≫ pushforwardMap (costructuredSourceFiber b).2 b.hom :=
  pushforwardMap_comp_costructuredToFiberMap f

end CategoryTheory.Functor.IsCofiberedCommaTests

end
