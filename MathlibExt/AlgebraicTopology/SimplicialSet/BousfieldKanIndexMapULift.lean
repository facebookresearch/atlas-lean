/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanElementsDiagonalIndexMap

/-!
# The same full Bousfield--Kan index map at independent universes

The established full elements diagonal identifies both original BK
carriers. Their index map retains every original chain, coefficient
and arrow through the canonical elements functors and nerve lift.
The coefficient lift preserves both complete scalar directions.
-/

noncomputable section

universe u w vJ vK

open CategoryTheory Opposite

namespace SSet

variable {J : Type u} {K : Type (max u w)} [Category.{vJ} J] [Category.{max vJ vK} K]
variable {D : J ⥤ SSet.{max u vJ}} {E : K ⥤ SSet.{max u w vJ vK}}

/-- The full original index map retains the complete original source BK carrier with its explicit coefficient universe
lift. -/
def bkHocolimIndexMapULift (Φ : J ⥤ K)
    (α : D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E) :
    uliftFunctor.{max u w vJ vK,max u vJ}.obj (bkHocolim D) ⟶ bkHocolim E :=
  uliftFunctor.map (bkHocolimElementsDiagonalIso D).hom ≫
    bkElementsDiagonalIndexMapULift Φ α ≫ (bkHocolimElementsDiagonalIso E).inv

/-- The complete original BK index map is the same full elements diagonal map under both original inverse
comparisons. -/
theorem bkHocolimIndexMapULift_diagonalIso (Φ : J ⥤ K)
    (α : D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E) :
    bkHocolimIndexMapULift Φ α ≫ (bkHocolimElementsDiagonalIso E).hom =
      uliftFunctor.map (bkHocolimElementsDiagonalIso D).hom ≫ bkElementsDiagonalIndexMapULift Φ α := by
  change (uliftFunctor.map (bkHocolimElementsDiagonalIso D).hom ≫
    bkElementsDiagonalIndexMapULift Φ α ≫ (bkHocolimElementsDiagonalIso E).inv) ≫
      (bkHocolimElementsDiagonalIso E).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every whole original BK coefficient reads the same complete original index functor on its entire elements chain. -/
theorem bkHocolimIndexMapULift_elements (Φ : J ⥤ K)
    (α : D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E)
    (q : SimplexCategoryᵒᵖ) (a : (bkHocolim D).obj q) :
    (bkHocolimElementsDiagonalIso E).hom.app q
      ((bkHocolimIndexMapULift Φ α).app q
        (uliftObjEquiv.{max u vJ,max u w vJ vK} (bkHocolim D) q a)) =
      ((bkElementsIndexFunctor Φ α q).mapComposableArrows q.unop.len).obj
        ((bkHocolimElementsDiagonalIso D).hom.app q a) := by
  have h := ConcreteCategory.congr_hom (C := Type (max u w vJ vK))
    (NatTrans.congr_app (bkHocolimIndexMapULift_diagonalIso Φ α) q)
      (uliftObjEquiv.{max u vJ,max u w vJ vK} (bkHocolim D) q a)
  have hLift : (uliftFunctor.{max u w vJ vK,max u vJ}.map (bkHocolimElementsDiagonalIso D).hom).app q
      (uliftObjEquiv.{max u vJ,max u w vJ vK} (bkHocolim D) q a) =
        uliftObjEquiv.{max u vJ,max u w vJ vK}
          (simplicialDiagonalFunctor.obj (bkElementsRows D)) q
            ((bkHocolimElementsDiagonalIso D).hom.app q a) := rfl
  exact h.trans ((congrArg ((bkElementsDiagonalIndexMapULift Φ α).app q) hLift).trans
    (bkElementsDiagonalIndexMapULift_chain Φ α q ((bkHocolimElementsDiagonalIso D).hom.app q a)))

end SSet
