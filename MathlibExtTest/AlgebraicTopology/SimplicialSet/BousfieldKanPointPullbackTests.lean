/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointPullback

public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

universe u

namespace SSet

variable {J : Type u} [Category.{0} J]

-- The monomorphism instance is available from the standalone public import.
example (E : J ⥤ SSet.{u}) (j : J) : Mono (bkPointInclusion E j) :=
  inferInstance

-- Recover the total-space point from the inverse strict-fiber identification.
example (E : J ⥤ SSet.{u}) (j : J) :
    (bkPointStrictFiberIso E j).inv ≫ toTop.map (bkPointInclusion E j) =
      pullback.fst (toTop.map (bkHocolimToNerve E))
        (TopCat.const (X := TopCat.of PUnit) (bkPointRealizedVertex j)) := by
  apply (cancel_epi (bkPointStrictFiberIso E j).hom).mp
  rw [Iso.hom_inv_id_assoc, bkPointStrictFiberIso_hom_fst]

-- The comparison over the strict-fiber model still carries the canonical constant path.
example (E : J ⥤ SSet.{u}) (j : J) :
    (bkPointStrictFiberIso E j).inv ≫ bkPointFiberComparison E j =
      TopCat.strictFiberToHomotopyFiber (toTop.map (bkHocolimToNerve E))
        (bkPointRealizedVertex j) := by
  apply (cancel_epi (bkPointStrictFiberIso E j).hom).mp
  rw [Iso.hom_inv_id_assoc,
    bkPointStrictFiberIso_hom_comp_strictFiberToHomotopyFiber]

end SSet

end
