/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedPrevFunctoriality

/-!
# Functoriality of the unified predecessor homology-filtration map

The all-column predecessor map preserves identities and composition.  In a
positive column this is the transported finite-stage law.  In column zero,
the complete predecessor has integer index `-1` and is a zero object, so both
laws follow from uniqueness of maps out of that source.

This file does not package the predecessor maps as a functor or construct the
step natural transformation.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The unified predecessor-stage map of an identity bicomplex morphism is
the identity, including at the genuinely zero predecessor in column zero. -/
@[simp 1100]
theorem horizontalPrevTotalHomologyFiltrationMapOfBicomplex_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex (𝟙 K) p q = 𝟙 _ := by
  by_cases hp : 0 < p
  · simpa only [horizontalPrevTotalHomologyFiltrationMapOfBicomplex,
      dite_eq_left hp] using
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_id K p q hp
  · have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    subst p
    have hLower : IsZero
        ((horizontalTotalHomologyFiltration K (0 + q)).obj
          ((((0 : ℤ) - 1 : ℤ) : EInt))) := by
      rw [Nat.zero_add, show (0 : ℤ) - 1 = -1 by omega]
      exact horizontalTotalHomologyFiltration_obj_isZero_of_neg
        K (-1) (by omega) q
    exact hLower.eq_of_src _ _

/-- Unified predecessor-stage maps preserve composition, including at the
genuinely zero predecessor in column zero. -/
@[simp 1100]
theorem horizontalPrevTotalHomologyFiltrationMapOfBicomplex_comp
    (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex (f ≫ g) p q =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex g p q := by
  by_cases hp : 0 < p
  · simpa only [horizontalPrevTotalHomologyFiltrationMapOfBicomplex,
      dite_eq_left hp] using
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_comp
        f g p q hp
  · have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    subst p
    have hLower : IsZero
        ((horizontalTotalHomologyFiltration K (0 + q)).obj
          ((((0 : ℤ) - 1 : ℤ) : EInt))) := by
      rw [Nat.zero_add, show (0 : ℤ) - 1 = -1 by omega]
      exact horizontalTotalHomologyFiltration_obj_isZero_of_neg
        K (-1) (by omega) q
    exact hLower.eq_of_src _ _

end HomologicalComplex₂

end
