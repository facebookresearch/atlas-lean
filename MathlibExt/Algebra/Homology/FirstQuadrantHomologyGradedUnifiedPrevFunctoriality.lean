/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedPrevFunctoriality

/-!
# Functorial predecessor maps in every column

Let C be an abelian category and n=p+q. The predecessor map on complete total-homology image
stages is the transported finite stage-(p−1) map for p>0 and the zero map between F_{−1}
stages for p=0.

These all-column maps preserve identity morphisms and composition. At p=0, the integer
predecessor is −1 and both stages are zero objects; this uses the complete-filtration boundary
rather than a natural predecessor at zero.
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

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and p,q ∈ ℕ. The
all-column predecessor-stage map induced by 𝟙_K is the identity on F_{(p:ℤ)−1}H_{p+q}(Tot(K)).
For p>0 this is the map transported from the finite stage p−1; for p=0 the stage is the zero
object F_{−1}, whose zero endomorphism equals its identity. -/
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

/-- Let C be an abelian category and f : K → L, g : L → M composable bicomplex morphisms of shape
(down ℕ,down ℕ). For p,q ∈ ℕ, the all-column maps on F_{(p:ℤ)−1}H_{p+q}(Tot) satisfy a(f ≫ g)
= a(f) ≫ a(g). For p>0 these are transported finite predecessor-stage maps; for p=0 all maps
have source the zero image stage at the finite integer −1. -/
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
