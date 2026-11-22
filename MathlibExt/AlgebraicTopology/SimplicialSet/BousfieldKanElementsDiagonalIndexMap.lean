/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanElementsIndexMap
import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftDiagonal

/-!
# The full original coefficient-elements diagonal index map

The canonical coefficient lift and full original elements row map
retain both scalar directions. Every entire original chain is mapped
by the same original index and coefficient functor.
-/

noncomputable section

universe u w vJ vK

open CategoryTheory Opposite

namespace SSet

variable {J : Type u} {K : Type (max u w)} [Category.{vJ} J] [Category.{max vJ vK} K]
variable {D : J ⥤ SSet.{max u vJ}} {E : K ⥤ SSet.{max u w vJ vK}}

/-- The actual original full elements diagonal map retains its same complete coefficient universe lift. -/
def bkElementsDiagonalIndexMapULift (Φ : J ⥤ K)
    (α : D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E) :
    uliftFunctor.{max u w vJ vK,max u vJ}.obj (simplicialDiagonalFunctor.obj (bkElementsRows D)) ⟶
      simplicialDiagonalFunctor.obj (bkElementsRows E) :=
  (uliftDiagonalIso (bkElementsRows D)).hom ≫
    simplicialDiagonalFunctor.map (bkElementsIndexRowsULift Φ α)

/-- Every whole original native elements chain retains the complete original index and coefficient map. -/
theorem bkElementsDiagonalIndexMapULift_chain (Φ : J ⥤ K)
    (α : D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E)
    (q : SimplexCategoryᵒᵖ) (F : (simplicialDiagonalFunctor.obj (bkElementsRows D)).obj q) :
    (bkElementsDiagonalIndexMapULift Φ α).app q
      (uliftObjEquiv.{max u vJ,max u w vJ vK} (simplicialDiagonalFunctor.obj (bkElementsRows D)) q F) =
        ((bkElementsIndexFunctor Φ α q).mapComposableArrows q.unop.len).obj F := rfl

end SSet
