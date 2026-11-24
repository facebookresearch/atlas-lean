/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaAdjunction

/-! # Tests for the cofibered comma/fiber adjunction -/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Functor.IsCofibered

universe vS vX uS uX

namespace CategoryTheory.Functor.IsCofiberedCommaAdjunctionTests

variable {S : Type uS} {X : Type uX}
  [Category.{vS} S] [Category.{vX} X]
  {p : X ⥤ S} [p.IsCofibered]

example (s : S) :
    costructuredToFiber (p := p) s ⊣
      fiberToCostructuredArrow (p := p) s :=
  costructuredToFiberAdjunction (p := p) s

example (s : S) (a : CostructuredArrow p s) (b : p.Fiber s) :
    ((costructuredToFiber s).obj a ⟶ b) ≃
      (a ⟶ (fiberToCostructuredArrow s).obj b) :=
  costructuredFiberHomEquiv s a b

end CategoryTheory.Functor.IsCofiberedCommaAdjunctionTests

end
