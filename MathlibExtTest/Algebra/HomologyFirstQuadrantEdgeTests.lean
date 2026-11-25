/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantEdge

/-! # Tests for the column-zero first-quadrant edge isomorphism -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantEdgeTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

#check horizontalZeroColumnPageHomologyIso
#check horizontalZeroColumnPageSuccIso
#check horizontalSecondPageZeroColumnPageIso
#check horizontalSecondPageZeroColumnStableIso
#check horizontalTotalHomologyGradedPieceZeroIsoFiltrationZero
#check horizontalTotalHomologyFiltrationZeroStageIso
#check horizontalTotalHomologyFiltrationZeroTotalIso
#check horizontalSecondPageZeroColumnTotalHomologyIso

example (n : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q))) :
    ((horizontalFirstQuadrantSpectralSequence K).page 2).X (0, n) ≅
      (K.total (ComplexShape.down ℕ)).homology n :=
  horizontalSecondPageZeroColumnTotalHomologyIso K n hpos

#print axioms horizontalZeroColumnPageHomologyIso
#print axioms horizontalSecondPageZeroColumnStableIso
#print axioms horizontalTotalHomologyGradedPieceZeroIsoFiltrationZero
#print axioms horizontalTotalHomologyFiltrationZeroStageIso
#print axioms horizontalTotalHomologyFiltrationZeroTotalIso
#print axioms horizontalSecondPageZeroColumnTotalHomologyIso

end HomologicalComplex₂.FirstQuadrantEdgeTests

end
