/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
Actual weak Arrow colimits from the original base weak-comparison closure.
Private external preparation; both projected cocones and every caller square
are kept. This is not a closure claim about only composable weak maps.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.WeakArrowColimits

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {J : Type w} [Category.{w'} J] [W.IsStableUnderColimitsOfShape J]

/-- The original base closure applies to both complete projections of the actual Arrow cocone. -/
theorem of_actual_colimit (K : J ⥤ Arrow C) (c : Cocone K) (hc : IsColimit c)
    [PreservesColimit K (Arrow.leftFunc (C := C))]
    [PreservesColimit K (Arrow.rightFunc (C := C))]
    (hK : ∀ j : J, W (K.obj j).hom) : W c.pt.hom := by
  let α : K ⋙ Arrow.leftFunc ⟶ K ⋙ Arrow.rightFunc :=
    Functor.whiskerLeft K Arrow.leftToRight
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := W) (J := J)
    (K ⋙ Arrow.leftFunc) (K ⋙ Arrow.rightFunc)
    (Arrow.leftFunc.mapCocone c) (Arrow.rightFunc.mapCocone c)
    (isColimitOfPreserves Arrow.leftFunc hc) (isColimitOfPreserves Arrow.rightFunc hc)
    α hK c.pt.hom (fun j => (c.ι.app j).w)

end HomotopicalAlgebra.WeakArrowColimits
