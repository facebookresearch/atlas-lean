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
# Morphism properties of Arrow colimits

Let W be a morphism property stable under colimits of shape J. The colimit arrow of a
J-diagram in Arrow C belongs to W when every diagram arrow does and both Arrow projections
preserve the chosen colimit. The proof uses the two projected colimit cocones and the
natural transformation formed by the diagram arrows.
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

/-- The two projected colimit cocones transfer W to the colimit arrow. -/
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
