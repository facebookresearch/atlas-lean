/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits

/-! # Original cocone consumers of inner-Hom colimit preservation -/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits

namespace SimplicialSpace.InnerHomColimitsTest

/-- The actual supplied colimit, with its original diagram and point, is preserved. -/
noncomputable def mappedOriginalColimit {D : Type w} [Category.{v} D]
    (Z : SimplicialSpace.{u}) (F : D ⥤ SimplicialSpace.{u})
    (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((innerHomFunctor.{u}.flip.obj Z).rightOp.mapCocone c) := by
  let _ : PreservesColimitsOfShape D (innerHomFunctor.{u}.flip.obj Z).rightOp :=
    innerHom_rightOp_preservesColimitsOfShape D Z
  exact isColimitOfPreserves (innerHomFunctor.{u}.flip.obj Z).rightOp hc

/-- Every mapped cocone component is the original inner restriction after unop. -/
theorem mapped_original_projection {D : Type w} [Category.{v} D]
    (Z : SimplicialSpace.{u}) (F : D ⥤ SimplicialSpace.{u})
    (c : Cocone F) (d : D) :
    (((innerHomFunctor.{u}.flip.obj Z).rightOp.mapCocone c).ι.app d).unop =
      (innerHomFunctor.{u}.map (c.ι.app d).op).app Z := by
  simp only [Functor.mapCocone_ι_app, Functor.rightOp_map_unop, Functor.flip_obj_map]

/-- The original diagram morphism and both original cocone components still commute. -/
theorem mapped_original_triangle {D : Type w} [Category.{v} D]
    (Z : SimplicialSpace.{u}) (F : D ⥤ SimplicialSpace.{u})
    (c : Cocone F) {d d' : D} (f : d ⟶ d') :
    (innerHomFunctor.{u}.map (c.ι.app d').op).app Z ≫
        (innerHomFunctor.{u}.map (F.map f).op).app Z =
      (innerHomFunctor.{u}.map (c.ι.app d).op).app Z := by
  rw [← NatTrans.comp_app, ← Functor.map_comp, ← CategoryTheory.op_comp, c.w f]

/-- Each actual strict initial-segment colimit is preserved, in particular at limit stages. -/
noncomputable def mappedIioColimit {J : Type w} [LinearOrder J]
    (Z : SimplicialSpace.{u}) (F : J ⥤ SimplicialSpace.{u}) (j : J)
    (c : Cocone ((Subtype.mono_coe (· ∈ Set.Iio j)).functor ⋙ F))
    (hc : IsColimit c) :
    IsColimit ((innerHomFunctor.{u}.flip.obj Z).rightOp.mapCocone c) :=
  mappedOriginalColimit Z _ c hc

/-- Supplied empty coproducts are included, without an inhabitedness premise. -/
noncomputable def mappedEmptyColimit (Z : SimplicialSpace.{u})
    (F : Discrete PEmpty.{w + 1} ⥤ SimplicialSpace.{u})
    (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((innerHomFunctor.{u}.flip.obj Z).rightOp.mapCocone c) :=
  mappedOriginalColimit Z F c hc

end SimplicialSpace.InnerHomColimitsTest
