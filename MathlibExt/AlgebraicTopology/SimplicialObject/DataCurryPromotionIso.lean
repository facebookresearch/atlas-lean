/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialObject.DataEvaluation
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Currying commutes with promotion of simplicial data

The canonical evaluation/promotion isomorphism in every indexing object
assembles into a natural isomorphism. Its two maps are identities on
every original coefficient, with independent indexing and target
object/Hom universes.
-/

noncomputable section

universe uA vA uC vC

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.Data

variable {A : Type uA} [Category.{vA} A] {C : Type uC} [Category.{vC} C]

/-- Both original currying/promotion routes retain every original coefficient
and its complete operators. -/
def curryPromotionIso (X : Data (A ⥤ C)) :
    X.toSimplicialObject.flip ≅ curryObj X ⋙ toSimplicialFunctor :=
  NatIso.ofComponents (evalToSimplicialIso X) (by
    intro a b f
    apply NatTrans.ext
    funext q
    obtain ⟨⟨n⟩⟩ := q
    change (X.toSimplicialObject.obj (Opposite.op ⦋n⦌)).map f ≫ 𝟙 _ =
      𝟙 _ ≫ (toSimplicialFunctor.map ((curryObj X).map f)).app (Opposite.op ⦋n⦌)
    rw [Category.comp_id, Category.id_comp, toSimplicialFunctor_map_app_mk]
    rfl)

/-- The forward comparison is the identity on every original indexing object
and scalar coefficient. -/
theorem curryPromotionIso_hom_app (X : Data (A ⥤ C)) (a : A) (q : SimplexCategoryᵒᵖ) :
    ((curryPromotionIso X).hom.app a).app q = 𝟙 _ := rfl

/-- The inverse comparison is the identity on every original indexing object
and scalar coefficient. -/
theorem curryPromotionIso_inv_app (X : Data (A ⥤ C)) (a : A) (q : SimplexCategoryᵒᵖ) :
    ((curryPromotionIso X).inv.app a).app q = 𝟙 _ := rfl

end CategoryTheory.SimplicialObject.Data
