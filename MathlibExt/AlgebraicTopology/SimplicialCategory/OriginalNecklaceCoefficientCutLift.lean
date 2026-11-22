/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceCoefficientLiftMap

/-!
# The SAME original coefficient lift has its exact full cut formula

The actual complete raw lift is the original composition of both full
native cut lifts. Their literal raw Hom maps and every original interval
coefficient are retained, for any actual cut joint and scalar degree.
The formula follows from the proved full image square and ambient mono.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace OriginalBeadInterval SimplicialEnrichment

/-- EVERY SAME complete coefficient lift retains both original full cut maps and actual raw composition. -/
theorem coefficientLift_cut (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints)
    {q : SimplexCategoryᵒᵖ} (p : (fullCoefficient.{u} T).obj q) :
    coefficientLift T p =
      (eComp SSet.{u} (C := realization T.object.{u}) (sourceVertex T) (nativeVertex T j) (targetVertex T)).app q
        ((leftCutHomMap T j hj).app q (coefficientLift (Cut.leftData T j hj) (leftJointCoefficient T j hj p)),
          (rightCutHomMap T j hj).app q (coefficientLift (Cut.rightData T j hj) (rightJointCoefficient T j hj p))) := by
  symm
  apply coefficientLift_unique T p
  let l := coefficientLift (Cut.leftData T j hj) (leftJointCoefficient T j hj p)
  let r := coefficientLift (Cut.rightData T j hj) (rightJointCoefficient T j hj p)
  have hL := ConcreteCategory.congr_hom (congr_app (leftCutHomMap_ambient.{u} T j hj) q) l
  have hR := ConcreteCategory.congr_hom (congr_app (rightCutHomMap_ambient.{u} T j hj) q) r
  have hL' : (ambientIntervalMap T 0 j).app q ((leftCutHomMap T j hj).app q l) =
      (homIso.{u} 0 j (Fin.zero_le j)).hom.app q (leftJointCoefficient T j hj p).val :=
    hL.trans (congrArg ((homIso.{u} 0 j (Fin.zero_le j)).hom.app q)
      (coefficientLift_ambient (Cut.leftData T j hj) (leftJointCoefficient T j hj p)))
  have hR' : (ambientIntervalMap T j (Fin.last T.dimension)).app q ((rightCutHomMap T j hj).app q r) =
      (homIso.{u} j (Fin.last T.dimension) (Fin.le_last j)).hom.app q (rightJointCoefficient T j hj p).val :=
    hR.trans (congrArg ((homIso.{u} j (Fin.last T.dimension) (Fin.le_last j)).hom.app q)
      (coefficientLift_ambient (Cut.rightData T j hj) (rightJointCoefficient T j hj p)))
  have hc := ambientIntervalMap_composition_app.{u} T 0 j (Fin.last T.dimension) q
    ((leftCutHomMap T j hj).app q l) ((rightCutHomMap T j hj).app q r)
  exact hc.trans ((congrArg
    ((CompositionFace.composition (ULift.up.{u} (0 : Fin (T.dimension + 1))) (ULift.up.{u} j)
      (ULift.up.{u} (Fin.last T.dimension))).app q)
    (congrArg₂ Prod.mk hL' hR')).trans (jointCoefficient_composition T j hj p))

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
