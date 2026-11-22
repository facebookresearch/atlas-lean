/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceAmbientHomNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceJointCoefficientCuts

/-!
# Both SAME full original cut ambient Hom squares

The actual native prefix and suffix maps retain their original endpoint
and cut-joint equations. Their complete raw Hom maps commute with the
SAME full ambient interval coefficient isomorphisms, without fibrancy or
comparison outcomes as hypotheses.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace OriginalBeadInterval SimplicialEnrichment

variable (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints)

/-- The SAME complete original cut-prefix Hom map, with its original source and cut vertex. -/
def leftCutHomMap : hom (Cut.leftData T j hj).object.{u}
    (sourceVertex (Cut.leftData T j hj)) (targetVertex (Cut.leftData T j hj)) ⟶
      hom T.object.{u} (sourceVertex T) (nativeVertex T j) :=
  pointedHomMap (Cut.leftMap T j hj)
    ((SSet.yonedaEquiv_comp (Cut.leftData T j hj).source (Cut.leftMap T j hj)).symm.trans
      (congrArg SSet.yonedaEquiv (Cut.leftMap_source T j hj)))
    ((SSet.yonedaEquiv_comp (Cut.leftData T j hj).target (Cut.leftMap T j hj)).symm.trans
      (congrArg SSet.yonedaEquiv (Cut.leftMap_target T j hj)))

/-- The SAME complete original cut-suffix Hom map, with its original cut vertex and target. -/
def rightCutHomMap : hom (Cut.rightData T j hj).object.{u}
    (sourceVertex (Cut.rightData T j hj)) (targetVertex (Cut.rightData T j hj)) ⟶
      hom T.object.{u} (nativeVertex T j) (targetVertex T) :=
  pointedHomMap (Cut.rightMap T j hj)
    ((SSet.yonedaEquiv_comp (Cut.rightData T j hj).source (Cut.rightMap T j hj)).symm.trans
      (congrArg SSet.yonedaEquiv (Cut.rightMap_source T j hj)))
    ((SSet.yonedaEquiv_comp (Cut.rightData T j hj).target (Cut.rightMap T j hj)).symm.trans
      (congrArg SSet.yonedaEquiv (Cut.rightMap_target T j hj)))

/-- The SAME whole prefix raw Hom square retains its complete original coefficient interval. -/
theorem leftCutHomMap_ambient :
    leftCutHomMap.{u} T j hj ≫ ambientIntervalMap T 0 j =
      ambientHomMap (Cut.leftData T j hj) ≫ (homIso.{u} 0 j (Fin.zero_le j)).hom := by
  have h := ambientIntervalMap_square_retarget (Cut.leftData T j hj) T (Cut.leftMap T j hj)
    (OriginalBeadInterval.operator 0 j (Fin.zero_le j)) (Cut.leftMap_ι T j hj) 0 j
      (embedding_zero 0 j (Fin.zero_le j)) (embedding_last 0 j (Fin.zero_le j))
  exact h.trans (congrArg (fun e => ambientHomMap (Cut.leftData T j hj) ≫ e)
    (homIso_hom.{u} 0 j (Fin.zero_le j)).symm)

/-- The SAME whole suffix raw Hom square retains its complete original coefficient interval. -/
theorem rightCutHomMap_ambient :
    rightCutHomMap.{u} T j hj ≫ ambientIntervalMap T j (Fin.last T.dimension) =
      ambientHomMap (Cut.rightData T j hj) ≫ (homIso.{u} j (Fin.last T.dimension) (Fin.le_last j)).hom := by
  have h := ambientIntervalMap_square_retarget (Cut.rightData T j hj) T (Cut.rightMap T j hj)
    (OriginalBeadInterval.operator j (Fin.last T.dimension) (Fin.le_last j)) (Cut.rightMap_ι T j hj)
      j (Fin.last T.dimension) (embedding_zero j (Fin.last T.dimension) (Fin.le_last j))
      (embedding_last j (Fin.last T.dimension) (Fin.le_last j))
  exact h.trans (congrArg (fun e => ambientHomMap (Cut.rightData T j hj) ≫ e)
    (homIso_hom.{u} j (Fin.last T.dimension) (Fin.le_last j)).symm)

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
