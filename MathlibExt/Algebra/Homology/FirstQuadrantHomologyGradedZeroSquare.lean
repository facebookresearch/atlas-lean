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
# The column-zero homology-filtration square

Let C be an abelian category, f : K → L a map of first-quadrant bicomplexes, and q ∈ ℕ. In
total degree q, the predecessor stage for column zero is F_{−1}H_q(Tot), indexed by the finite
integer −1, and is a zero object.

The predecessor map is zero. Together with the current-stage map at column zero, it commutes
with the inclusion F_{−1} → F_0 and supplies the column-zero case of the consecutive-stage
naturality square.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be an abelian category, f : K → L a morphism of bicomplexes of shape (down ℕ,down ℕ),
and q ∈ ℕ. Define the map F_{−1}H_q(Tot(K)) → F_{−1}H_q(Tot(L)) to be zero. These are the
complete image-filtration stages at the finite integer (0:ℤ)−1 = −1, and both are zero
objects. This is the predecessor map assigned to column p=0. -/
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

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and q ∈ ℕ.
Let s_K : F_{−1}H_q(Tot(K)) → F_0H_q(Tot(K)) and s_L be the column-zero filtration steps. If
c(f) is the transported current-stage map at p=0 and a_0(f) is the zero predecessor map, then
s_K ≫ c(f) = a_0(f) ≫ s_L. Both composites have source the zero stage at index −1. -/
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
