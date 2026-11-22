/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceInputCoefficientElements
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointComparison
import MathlibExt.CategoryTheory.CategoryBar.ElementsNaturality

/-!
# The original necklace homotopy-colimit rows are full flagged nerves

The canonical terminal-weight row and elements-nerve isomorphisms,
followed by the actual full flagged-category isomorphism, retain every
original native chain and source coefficient. The original scalar
operators commute with this complete row comparison.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

/-- The SAME full original coefficient homotopy-colimit row is its complete flagged-category nerve. -/
def fullCoefficientRowIso (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.wbarRow (fullCoefficientDiagram K x y) q ≅ nerve (OriginalFlaggedNecklace.Object K x y q) :=
  SSet.terminalWeightRowIso (fullCoefficientDiagram K x y) q ≪≫
    CategoryBar.replNerveSimplicialIso (degreeCoefficient K x y q) ≪≫ elementsNerveIso K x y q

private theorem elementsNerveIso_scalar (K : SSet.{u}) (x y : K _⦋0⦌)
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    nerveMap (degreeCoefficientMap K x y θ).mapElements ≫ (elementsNerveIso K x y r).hom =
      (elementsNerveIso K x y q).hom ≫ nerveMap (OriginalFlaggedNecklace.scalarFunctor K x y θ) := by
  have h := congrArg (fun F => nerveMap F) (toFlagged_scalar K x y θ)
  exact h

private theorem triple_square {A B C D E F G H : SSet.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (a' : E ⟶ F) (b' : F ⟶ G) (c' : G ⟶ H)
    (i : A ⟶ E) (j : B ⟶ F) (k : C ⟶ G) (l : D ⟶ H)
    (h₁ : i ≫ a' = a ≫ j) (h₂ : j ≫ b' = b ≫ k) (h₃ : k ≫ c' = c ≫ l) :
    i ≫ (a' ≫ b' ≫ c') = (a ≫ b ≫ c) ≫ l := by
  rw [← Category.assoc, h₁, Category.assoc, ← Category.assoc j, h₂,
    Category.assoc, h₃]
  simp only [Category.assoc]

/-- EVERY original scalar operator retains the SAME complete original flagged row isomorphism. -/
theorem fullCoefficientRowIso_scalar (K : SSet.{u}) (x y : K _⦋0⦌)
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    SSet.wbarInnerMap (fullCoefficientDiagram K x y) θ ≫ (fullCoefficientRowIso K x y r).hom =
      (fullCoefficientRowIso K x y q).hom ≫ nerveMap (OriginalFlaggedNecklace.scalarFunctor K x y θ) := by
  have hd : SSet.wbarDegreeCoefficientMap (fullCoefficientDiagram K x y) θ =
      degreeCoefficientMap K x y θ := by
    ext T p
    rfl
  have h₁ := (SSet.terminalWeightRowIso_inner_naturality (fullCoefficientDiagram K x y) θ).trans
    (congrArg (fun α => (SSet.terminalWeightRowIso (fullCoefficientDiagram K x y) q).hom ≫
      CategoryBar.replMap α) hd)
  exact triple_square
    (SSet.terminalWeightRowIso (fullCoefficientDiagram K x y) q).hom
    (CategoryBar.replNerveSimplicialIso (degreeCoefficient K x y q)).hom
    (elementsNerveIso K x y q).hom
    (SSet.terminalWeightRowIso (fullCoefficientDiagram K x y) r).hom
    (CategoryBar.replNerveSimplicialIso (degreeCoefficient K x y r)).hom
    (elementsNerveIso K x y r).hom
    (SSet.wbarInnerMap (fullCoefficientDiagram K x y) θ)
    (CategoryBar.replMap (degreeCoefficientMap K x y θ))
    (nerveMap (degreeCoefficientMap K x y θ).mapElements)
    (nerveMap (OriginalFlaggedNecklace.scalarFunctor K x y θ)) h₁
    (CategoryBar.replNerve_naturality (degreeCoefficientMap K x y θ)) (elementsNerveIso_scalar K x y θ)

/-- The SAME entire original inner-row diagram is the complete original scalar flagged-nerve diagram. -/
def fullCoefficientRowsIso (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.wbarRowFunctor (fullCoefficientDiagram K x y) ≅ OriginalFlaggedNecklace.scalarNerveDiagram K x y :=
  NatIso.ofComponents (fullCoefficientRowIso K x y) (fun θ => fullCoefficientRowIso_scalar K x y θ)

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
