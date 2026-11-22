/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceHocolimFlaggedRows
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceRawCoefficientFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanRowDiagonalComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagramIso
import MathlibExt.CategoryTheory.CategoryBar.ElementsNerveReadbacks

/-!
# The SAME original necklace homotopy colimit is the full flagged diagonal

The full native raw endpoint Hom coefficient diagram retains the actual
Bousfield--Kan carrier. Its entire original natural coefficient
isomorphism, canonical row diagonal and full flagged rows identify this
SAME carrier with the full original flagged diagonal. Every weighted
chain keeps its complete source input and coefficient readback.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

/-- The original full raw native Hom homotopy-colimit carrier over the SAME original input category. -/
def hocolim (K : SSet.{u}) (x y : K _⦋0⦌) : SSet.{u} := SSet.bkHocolim (rawCoefficientDiagram K x y)

/-- Both full inverse maps identify the original joint-coefficient homotopy colimit with its flagged diagonal. -/
def fullCoefficientHocolimIso (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.bkHocolim (fullCoefficientDiagram K x y) ≅ OriginalFlaggedNecklace.Components.diagonal K x y :=
  SSet.bkHocolimRowDiagonalIso (fullCoefficientDiagram K x y) ≪≫
    SSet.simplicialDiagonalFunctor.mapIso (fullCoefficientRowsIso K x y)

/-- Both full inverse maps identify the SAME native raw Hom homotopy colimit with the original flagged diagonal. -/
def hocolimFlaggedIso (K : SSet.{u}) (x y : K _⦋0⦌) :
    hocolim K x y ≅ OriginalFlaggedNecklace.Components.diagonal K x y :=
  SSet.bkHocolimDiagramIso (rawCoefficientDiagramIso K x y) ≪≫ fullCoefficientHocolimIso K x y

/-- Every SAME complete weighted chain retains its original source input and full joint coefficient. -/
theorem fullCoefficientHocolimIso_first (K : SSet.{u}) (x y : K _⦋0⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx (Object K x y) (CategoryBar.replUnit (Object K x y)) n)
    (a : ((fullCoefficientDiagram K x y).obj p.1.left).obj (op ⦋n⦌)) :
    (((fullCoefficientHocolimIso K x y).hom.app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit (Object K x y))
        (fullCoefficientDiagram K x y) n p).app (op ⦋n⦌) a)).obj 0) =
      toFlaggedObject ((degreeCoefficient K x y (op ⦋n⦌)).elementsMk p.1.left a) := by
  have hw := ConcreteCategory.congr_hom
    (SSet.terminalWeightRowIso_hom_rowIncl (fullCoefficientDiagram K x y) (op ⦋n⦌) n p) a
  rw [SSet.wbarRowIncl_eq_wbarIncl_app] at hw
  have hc := congrArg (fun z => ((elementsNerveIso K x y (op ⦋n⦌)).hom.app (op ⦋n⦌)
    ((CategoryBar.replNerveSimplicialIso (degreeCoefficient K x y (op ⦋n⦌))).hom.app (op ⦋n⦌) z)).obj 0) hw
  exact hc.trans (congrArg toFlaggedObject
    (CategoryBar.replNerveSimplicialIso_first (degreeCoefficient K x y (op ⦋n⦌)) n p.1 a p.2))

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
