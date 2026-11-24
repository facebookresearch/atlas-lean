/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanRowDiagonalComparison
import MathlibExt.CategoryTheory.CategoryBar.ElementsNaturality
import MathlibExt.CategoryTheory.CategoryBar.ElementsNerveReadbacks

/-!
# The original Bousfield--Kan diagonal of full coefficient-elements nerves

The canonical evaluated terminal-weight rows and the established
category-of-elements nerve comparison retain every original chain,
coefficient, arrow and scalar operator. Both inverse maps identify the
same original Bousfield--Kan carrier with this full native diagonal.
-/

noncomputable section

universe uJ vJ

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

variable {J : Type uJ} [Category.{vJ} J]

/-- The full native coefficient-elements nerve in each original inner degree. -/
def bkElementsRows (D : J ⥤ SSet.{max uJ vJ}) : SimplexCategoryᵒᵖ ⥤ SSet.{max uJ vJ} :=
  D.flip ⋙ Functor.elementsFunctor ⋙ nerveFunctor

/-- Both original row directions are the established weighted-row and full elements-nerve
isomorphisms. -/
def bkElementsRowIso (D : J ⥤ SSet.{max uJ vJ}) : wbarRowFunctor D ≅ bkElementsRows D :=
  NatIso.ofComponents (fun q => terminalWeightRowIso D q ≪≫
    CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D q)) (by
    intro a b θ
    change wbarInnerMap D θ ≫
        ((terminalWeightRowIso D b).hom ≫ (CategoryBar.replNerveSimplicialIso
          (wbarDegreeCoefficient D b)).hom) =
      ((terminalWeightRowIso D a).hom ≫ (CategoryBar.replNerveSimplicialIso
        (wbarDegreeCoefficient D a)).hom) ≫
        nerveMap (wbarDegreeCoefficientMap D θ).mapElements
    rw [← Category.assoc, terminalWeightRowIso_inner_naturality,
      Category.assoc, CategoryBar.replNerve_naturality, ← Category.assoc])

/-- Both full original inverse maps identify the SAME BK carrier with the full
coefficient-elements diagonal. -/
def bkHocolimElementsDiagonalIso (D : J ⥤ SSet.{max uJ vJ}) :
    bkHocolim D ≅ simplicialDiagonalFunctor.obj (bkElementsRows D) :=
  bkHocolimRowDiagonalIso D ≪≫ simplicialDiagonalFunctor.mapIso (bkElementsRowIso D)

/-- Every original coefficient is read through the same complete canonical weighted row and
elements nerve. -/
theorem bkHocolimElementsDiagonalIso_hom_app (D : J ⥤ SSet.{max uJ vJ}) (q : SimplexCategoryᵒᵖ) :
    (bkHocolimElementsDiagonalIso D).hom.app q =
      (terminalWeightRowIso D q).hom.app q ≫
        (CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D q)).hom.app q := rfl

end SSet
