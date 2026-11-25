/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedPrevFunctoriality

/-! # Tests for positive predecessor homology-filtration functoriality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyGradedPrevFunctorialityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_id
#check horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_comp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) (hp : 0 < p) :
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
        (𝟙 K) p q hp = 𝟙 _ := by
  simp

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) (hp : 0 < p) :
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
        (f ≫ g) p q hp =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex f p q hp ≫
        horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex g p q hp := by
  simp

-- At the first positive column, the finite predecessor is stage zero.
example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (q : ℕ) :
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
        (𝟙 K) 1 q (by omega) = 𝟙 _ := by
  simp

-- Total degree `p` is covered by the same law when `q = 0`.
example (f : K ⟶ L) (g : L ⟶ M) (p : ℕ) (hp : 0 < p) :
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
        (f ≫ g) p 0 hp =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex f p 0 hp ≫
        horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex g p 0 hp := by
  simp

-- The first positive column in horizontal degree zero is also functorial.
example (f : K ⟶ L) (g : L ⟶ M) :
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
        (f ≫ g) 1 0 (by omega) =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
          f 1 0 (by omega) ≫
        horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
          g 1 0 (by omega) := by
  simp

#print axioms horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_id
#print axioms horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_comp

end HomologicalComplex₂.FirstQuadrantHomologyGradedPrevFunctorialityTests

end
