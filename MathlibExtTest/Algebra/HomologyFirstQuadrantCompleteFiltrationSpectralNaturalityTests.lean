/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationSpectralNaturality

/-! # Tests for complete-filtration spectral-object naturality -/

@[expose] public section

open CategoryTheory Limits ComposableArrows Pretriangulated

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantCompleteFiltrationSpectralNaturalityTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalCompleteFiltrationCochainDiagramNatTrans
#check horizontalCompleteFiltrationMappingConeNatTrans
#check horizontalCompleteFiltrationTriangulatedSpectralObjectMap

example (f : K ⟶ L) :
    horizontalCompleteFiltrationCochainDiagram K ⟶
      horizontalCompleteFiltrationCochainDiagram L :=
  horizontalCompleteFiltrationCochainDiagramNatTrans f

example (f : K ⟶ L) :
    (horizontalCompleteFiltrationCochainDiagramNatTrans f).app ⊤ =
      HomologicalComplex.extendMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex f ⊤)
        ComplexShape.embeddingDownNat :=
  horizontalCompleteFiltrationCochainDiagramNatTrans_app f ⊤

example (f : K ⟶ L) :
    horizontalCompleteFiltrationTriangulatedSpectralObject K ⟶
      horizontalCompleteFiltrationTriangulatedSpectralObject L :=
  horizontalCompleteFiltrationTriangulatedSpectralObjectMap f

-- Boundary check: the spectral-object square includes the bottom-to-zero
-- arrow followed by the zero-to-top arrow, in the required δ orientation.
example (f : K ⟶ L) :
    let u : (⊥ : EInt) ⟶ ((0 : ℤ) : EInt) := homOfLE bot_le
    let v : ((0 : ℤ) : EInt) ⟶ (⊤ : EInt) := homOfLE le_top
    (horizontalCompleteFiltrationTriangulatedSpectralObject K).δ u v ≫
        ((horizontalCompleteFiltrationTriangulatedSpectralObjectMap f).hom.app
          (mk₁ u))⟦(1 : ℤ)⟧' =
      (horizontalCompleteFiltrationTriangulatedSpectralObjectMap f).hom.app
          (mk₁ v) ≫
        (horizontalCompleteFiltrationTriangulatedSpectralObject L).δ u v :=
  (horizontalCompleteFiltrationTriangulatedSpectralObjectMap f).comm _ _

#print axioms horizontalCompleteFiltrationCochainDiagramNatTrans
#print axioms horizontalCompleteFiltrationMappingConeNatTrans
#print axioms horizontalCompleteFiltrationTriangulatedSpectralObjectMap

end HomologicalComplex₂.FirstQuadrantCompleteFiltrationSpectralNaturalityTests

namespace HomologicalComplex₂.FirstQuadrantCompleteFiltrationSpectralNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalCompleteFiltrationSpectralObjectMap

example (f : K ⟶ L) :
    horizontalCompleteFiltrationSpectralObject K ⟶
      horizontalCompleteFiltrationSpectralObject L :=
  horizontalCompleteFiltrationSpectralObjectMap f

#print axioms horizontalCompleteFiltrationSpectralObjectMap

end HomologicalComplex₂.FirstQuadrantCompleteFiltrationSpectralNaturalityTests

end
