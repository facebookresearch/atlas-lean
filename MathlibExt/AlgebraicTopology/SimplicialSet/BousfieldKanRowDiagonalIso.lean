/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointComparison

/-!
# The SAME Bousfield--Kan carrier and the diagonal of its fixed rows

Evaluation after promotion and promotion after evaluation retain all original
weighted-bar operators. Their actual component equality and the original
bar's naturality give the identity-component diagonal isomorphism.
-/

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet

variable {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v})

/-- The actual original weighted-bar outer map is the SAME complete map of its fixed inner row. -/
theorem wbarOuterMap_row (a : SimplexCategoryᵒᵖ)
    {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c) :
    ((StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).map f).app a =
      (wbarRow D a).map f :=
  SimplicialObject.Data.evalToSimplicial_map_eq
    (StrictOrdinaryWeightedBar.wbarData (CategoryBar.replUnit J) D) a f.unop

/-- The original full BK diagonal map agrees with the diagonal map of its original fixed rows. -/
theorem bkHocolim_rowDiagonal_map {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (bkHocolim D).map f = (simplicialDiagonalFunctor.obj (wbarRowFunctor D)).map f := by
  have h := NatTrans.naturality
    ((StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).map f) f
  change (bkHocolim D).map f =
    (wbarRow D a).map f ≫ (wbarInnerMap D f).app b
  exact h.trans (congrArg (fun h => h ≫ (wbarInnerMap D f).app b) (wbarOuterMap_row D a f))

/-- Both whole identity-component maps identify the SAME original BK carrier with its
fixed-row diagonal. -/
def bkHocolimRowDiagonalIso : bkHocolim D ≅ simplicialDiagonalFunctor.obj (wbarRowFunctor D) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    change (bkHocolim D).map f ≫ 𝟙 _ = 𝟙 _ ≫
      (simplicialDiagonalFunctor.obj (wbarRowFunctor D)).map f
    exact (Category.comp_id _).trans ((bkHocolim_rowDiagonal_map D f).trans
      (Category.id_comp _).symm))

/-- The original diagonal comparison retains every actual simplex without changing coordinates. -/
theorem bkHocolimRowDiagonalIso_hom_app (a : SimplexCategoryᵒᵖ) :
    (bkHocolimRowDiagonalIso D).hom.app a = 𝟙 _ := rfl

/-- The actual inverse comparison also retains every original simplex. -/
theorem bkHocolimRowDiagonalIso_inv_app (a : SimplexCategoryᵒᵖ) :
    (bkHocolimRowDiagonalIso D).inv.app a = 𝟙 _ := rfl

end SSet
