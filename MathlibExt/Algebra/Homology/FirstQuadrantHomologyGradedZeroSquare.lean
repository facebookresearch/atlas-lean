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

/-!
# The zero-column total-homology filtration square

At column zero, the preceding complete total-homology filtration stage has
integer index `-1` and is a zero object.  Consequently the predecessor map
of a bicomplex morphism is the zero morphism, and the consecutive-stage
square commutes by uniqueness of maps from that zero object.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- At column zero, the map on preceding complete homology-filtration stages
is the zero morphism between the stages at integer index `-1`. -/
noncomputable def horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex
    (_f : K ⟶ L) (q : ℕ) :
    (horizontalTotalHomologyFiltration K (0 + q)).obj
        ((((0 : ℤ) - 1 : ℤ) : EInt)) ⟶
      (horizontalTotalHomologyFiltration L (0 + q)).obj
        ((((0 : ℤ) - 1 : ℤ) : EInt)) :=
  0

@[simp]
theorem horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex_eq
    (f : K ⟶ L) (q : ℕ) :
    horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex f q = 0 :=
  rfl

/-- In column zero, a bicomplex map commutes with the consecutive complete
total-homology filtration step. -/
theorem horizontalTotalHomologyFiltrationStepMap_naturality_zero
    (f : K ⟶ L) (q : ℕ) :
    horizontalTotalHomologyFiltrationStepMap K 0 q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f 0 q =
      horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex f q ≫
        horizontalTotalHomologyFiltrationStepMap L 0 q := by
  have hLower : IsZero
      ((horizontalTotalHomologyFiltration K (0 + q)).obj
        ((((0 : ℤ) - 1 : ℤ) : EInt))) := by
    rw [Nat.zero_add, show (0 : ℤ) - 1 = -1 by omega]
    exact horizontalTotalHomologyFiltration_obj_isZero_of_neg
      K (-1) (by omega) q
  exact hLower.eq_of_src _ _

end HomologicalComplex₂

end
