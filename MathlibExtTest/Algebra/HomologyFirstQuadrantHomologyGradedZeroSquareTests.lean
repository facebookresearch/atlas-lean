/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedZeroSquare

/-! # Tests for the zero-column total-homology filtration square -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyGradedZeroSquareTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex
#check horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex_eq
#check horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
#check horizontalTotalHomologyFiltrationStepMap_naturality_zero

example (f : K ⟶ L) (q : ℕ) :
    horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex f q = 0 :=
  rfl

example (f : K ⟶ L) (q : ℕ) :
    horizontalTotalHomologyFiltrationStepMap K 0 q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f 0 q =
      horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex f q ≫
        horizontalTotalHomologyFiltrationStepMap L 0 q :=
  horizontalTotalHomologyFiltrationStepMap_naturality_zero f q

example (f : K ⟶ L) :
    horizontalTotalHomologyFiltrationStepMap K 0 0 ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f 0 0 =
      horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex f 0 ≫
        horizontalTotalHomologyFiltrationStepMap L 0 0 :=
  horizontalTotalHomologyFiltrationStepMap_naturality_zero f 0

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (q : ℕ) :
    horizontalTotalHomologyFiltrationStepMap K 0 q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
          (𝟙 K) 0 q =
      horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex (𝟙 K) q ≫
        horizontalTotalHomologyFiltrationStepMap K 0 q :=
  horizontalTotalHomologyFiltrationStepMap_naturality_zero (𝟙 K) q

#print axioms horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex
#print axioms horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex_eq
#print axioms horizontalTotalHomologyFiltrationStepMap_naturality_zero

end HomologicalComplex₂.FirstQuadrantHomologyGradedZeroSquareTests

end
