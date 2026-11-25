/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCollapse

/-! # Tests for first-quadrant filtration collapse -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantCollapseTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

#check isZero_horizontalPage_add_two_of_isZero_secondPage
#check isZero_horizontalStablePage_of_isZero_secondPage
#check isZero_horizontalTotalHomologyGradedPiece_of_secondPage
#check horizontalTotalHomologyFiltrationStepMap_isIso_of_secondPage_isZero

example (p q : ℕ)
    (h : IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q))) :
    IsZero (horizontalTotalHomologyGradedPiece K p q) :=
  isZero_horizontalTotalHomologyGradedPiece_of_secondPage K p q h

example (p q : ℕ)
    (h : IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q))) :
    IsIso (horizontalTotalHomologyFiltrationStepMap K p q) :=
  horizontalTotalHomologyFiltrationStepMap_isIso_of_secondPage_isZero
    K p q h

example
    (h : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q)))
    (p q : ℕ) (hp : 1 ≤ p) :
    IsIso (horizontalTotalHomologyFiltrationStepMap K p q) :=
  horizontalTotalHomologyFiltrationStepMap_isIso_of_secondPage_isZero
    K p q (h p q hp)

#print axioms isZero_horizontalPage_add_two_of_isZero_secondPage
#print axioms isZero_horizontalStablePage_of_isZero_secondPage
#print axioms isZero_horizontalTotalHomologyGradedPiece_of_secondPage
#print axioms
  horizontalTotalHomologyFiltrationStepMap_isIso_of_secondPage_isZero

end HomologicalComplex₂.FirstQuadrantCollapseTests

end
