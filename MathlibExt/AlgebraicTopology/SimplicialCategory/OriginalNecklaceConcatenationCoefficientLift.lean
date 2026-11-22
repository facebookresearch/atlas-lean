/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceConcatenationHom
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceCoefficientLiftMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceAmbientIntervalComposition

/-!
# Exact full original concatenation coefficient lift

The actual full lift on a concatenated native necklace is the original
raw composition of its complete prefix and suffix lifts. The proof uses
the full ambient squares, the original coefficient union and monicity.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace SSet.OriginalTwoBead.OrdinalCharts OriginalBead

/-- EVERY complete original joint flag retains both full original coefficient lifts in concatenation. -/
theorem coefficientLift_concat (T U : Data) {q : SimplexCategoryᵒᵖ}
    (p : (fullCoefficient.{u} T).obj q) (r : (fullCoefficient.{u} U).obj q)
    (s : (fullCoefficient.{u} (T.concat U)).obj q)
    (hs : s.val = (CoefficientGluing.map T.dimension U.dimension).app q (p.val, r.val)) :
    coefficientLift (T.concat U) s =
      (eComp SSet.{u} (C := realization (T.concat U).object.{u}) (sourceVertex (T.concat U))
        (nativeVertex (T.concat U) (pivot T.dimension U.dimension)) (targetVertex (T.concat U))).app q
          ((concatLeftHomMap T U).app q (coefficientLift T p),
            (concatRightHomMap T U).app q (coefficientLift U r)) := by
  symm
  apply coefficientLift_unique (T.concat U) s
  have hL := ConcreteCategory.congr_hom (congr_app (concatLeftHomMap_ambient.{u} T U) q)
    (coefficientLift T p)
  have hR := ConcreteCategory.congr_hom (congr_app (concatRightHomMap_ambient.{u} T U) q)
    (coefficientLift U r)
  have hL' : (ambientIntervalMap (T.concat U) 0 (pivot T.dimension U.dimension)).app q
      ((concatLeftHomMap T U).app q (coefficientLift T p)) =
        (CoefficientGluing.leftMap.{u} T.dimension U.dimension).app q p.val :=
    hL.trans (congrArg ((CoefficientGluing.leftMap.{u} T.dimension U.dimension).app q)
      (coefficientLift_ambient T p))
  have hR' : (ambientIntervalMap (T.concat U) (pivot T.dimension U.dimension)
      (Fin.last (T.concat U).dimension)).app q ((concatRightHomMap T U).app q (coefficientLift U r)) =
        (CoefficientGluing.rightMap.{u} T.dimension U.dimension).app q r.val :=
    hR.trans (congrArg ((CoefficientGluing.rightMap.{u} T.dimension U.dimension).app q)
      (coefficientLift_ambient U r))
  have hc := ambientIntervalMap_composition_app.{u} (T.concat U) 0 (pivot T.dimension U.dimension)
    (Fin.last (T.concat U).dimension) q ((concatLeftHomMap T U).app q (coefficientLift T p))
      ((concatRightHomMap T U).app q (coefficientLift U r))
  exact hc.trans ((congrArg
    ((CompositionFace.composition (ULift.up.{u} (0 : Fin ((T.concat U).dimension + 1)))
      (ULift.up.{u} (pivot T.dimension U.dimension)) (ULift.up.{u} (Fin.last (T.concat U).dimension))).app q)
      (congrArg₂ Prod.mk hL' hR')).trans hs.symm)

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
