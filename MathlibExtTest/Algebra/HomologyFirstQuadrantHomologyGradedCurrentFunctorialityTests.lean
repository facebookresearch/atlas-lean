/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedCurrentFunctoriality

/-! # Tests for functoriality of the current homology-filtration stage -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyGradedCurrentFunctorialityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_id
#check horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_comp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
        (𝟙 K) p q = 𝟙 _ :=
  by simp

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
        (f ≫ g) p q =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex g p q :=
  by simp

-- The current-stage construction requires no positivity at column zero.
example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (q : ℕ) :
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
        (𝟙 K) 0 q = 𝟙 _ :=
  horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_id K 0 q

-- Total degree `p` is covered by the same composition law when `q = 0`.
example (f : K ⟶ L) (g : L ⟶ M) (p : ℕ) :
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
        (f ≫ g) p 0 =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p 0 ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex g p 0 :=
  horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_comp
    f g p 0

-- The bidegree `(0,0)` boundary is also functorial.
example (f : K ⟶ L) (g : L ⟶ M) :
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
        (f ≫ g) 0 0 =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f 0 0 ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex g 0 0 :=
  horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_comp
    f g 0 0

#print axioms horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_id
#print axioms horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_comp

end HomologicalComplex₂.FirstQuadrantHomologyGradedCurrentFunctorialityTests

end
