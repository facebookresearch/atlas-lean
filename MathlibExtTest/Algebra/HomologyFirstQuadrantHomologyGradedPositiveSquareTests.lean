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
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedPositiveSquare

/-! # Tests for the positive total-homology filtration square -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyGradedPositiveSquareTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
#check horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
#check horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_eq
#check horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_eq
#check horizontalTotalHomologyFiltrationStepMap_naturality_of_pos

example (f : K ⟶ L) (p q : ℕ) (hp : 0 < p) :
    horizontalTotalHomologyFiltrationStepMap K p q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex f p q hp ≫
        horizontalTotalHomologyFiltrationStepMap L p q :=
  horizontalTotalHomologyFiltrationStepMap_naturality_of_pos f p q hp

example (f : K ⟶ L) (q : ℕ) :
    horizontalTotalHomologyFiltrationStepMap K 1 q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f 1 q =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
          f 1 q (by omega) ≫
        horizontalTotalHomologyFiltrationStepMap L 1 q :=
  horizontalTotalHomologyFiltrationStepMap_naturality_of_pos
    f 1 q (by omega)

example (f : K ⟶ L) (p : ℕ) (hp : 0 < p) :
    horizontalTotalHomologyFiltrationStepMap K p 0 ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p 0 =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex f p 0 hp ≫
        horizontalTotalHomologyFiltrationStepMap L p 0 :=
  horizontalTotalHomologyFiltrationStepMap_naturality_of_pos f p 0 hp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) (hp : 0 < p) :
    horizontalTotalHomologyFiltrationStepMap K p q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
          (𝟙 K) p q =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
          (𝟙 K) p q hp ≫
        horizontalTotalHomologyFiltrationStepMap K p q :=
  horizontalTotalHomologyFiltrationStepMap_naturality_of_pos
    (𝟙 K) p q hp

#print axioms horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
#print axioms horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
#print axioms horizontalTotalHomologyFiltrationStepMap_naturality_of_pos

end HomologicalComplex₂.FirstQuadrantHomologyGradedPositiveSquareTests

end
