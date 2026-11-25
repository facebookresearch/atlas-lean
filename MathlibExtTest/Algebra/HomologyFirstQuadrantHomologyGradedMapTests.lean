/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedMap

/-! # Tests for maps on total-homology associated graded pieces -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyGradedMapTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalPrevTotalHomologyFiltrationMapOfBicomplex
#check horizontalTotalHomologyFiltrationStepMap_naturality
#check horizontalTotalHomologyFiltrationStepSquareOfBicomplex
#check horizontalTotalHomologyFiltrationStepSquareOfBicomplex_left
#check horizontalTotalHomologyFiltrationStepSquareOfBicomplex_right
#check horizontalTotalHomologyGradedPieceMapOfBicomplex

example (f : K ⟶ L) (p q : ℕ) :
    horizontalTotalHomologyFiltrationStepMap K p q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q ≫
        horizontalTotalHomologyFiltrationStepMap L p q :=
  horizontalTotalHomologyFiltrationStepMap_naturality f p q

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyFiltrationStepSquareOfBicomplex f p q).left =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q :=
  horizontalTotalHomologyFiltrationStepSquareOfBicomplex_left f p q

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyFiltrationStepSquareOfBicomplex f p q).right =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q :=
  horizontalTotalHomologyFiltrationStepSquareOfBicomplex_right f p q

-- At `p = 0`, the unified predecessor map is the zero-column map.
example (f : K ⟶ L) (q : ℕ) :
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex f 0 q =
      horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex f q := by
  simp [horizontalPrevTotalHomologyFiltrationMapOfBicomplex]

-- At `p = 1`, the unified predecessor map is the positive-column map.
example (f : K ⟶ L) (q : ℕ) :
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex f 1 q =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
        f 1 q (by omega) := by
  simp [horizontalPrevTotalHomologyFiltrationMapOfBicomplex]

-- Degree `q = 0` requires no separate construction.
example (f : K ⟶ L) (p : ℕ) :
    horizontalTotalHomologyGradedPiece K p 0 ⟶
      horizontalTotalHomologyGradedPiece L p 0 :=
  horizontalTotalHomologyGradedPieceMapOfBicomplex f p 0

-- Identity bicomplex maps are accepted; their identity law is deliberately
-- deferred to the functoriality leaf.
example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    horizontalTotalHomologyGradedPiece K p q ⟶
      horizontalTotalHomologyGradedPiece K p q :=
  horizontalTotalHomologyGradedPieceMapOfBicomplex (𝟙 K) p q

#print axioms horizontalPrevTotalHomologyFiltrationMapOfBicomplex
#print axioms horizontalTotalHomologyFiltrationStepMap_naturality
#print axioms horizontalTotalHomologyFiltrationStepSquareOfBicomplex
#print axioms horizontalTotalHomologyGradedPieceMapOfBicomplex

end HomologicalComplex₂.FirstQuadrantHomologyGradedMapTests

end
