/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedZeroSquare

/-!
# Maps on associated graded total homology

Let C be an abelian category and f : K → L a morphism of bicomplexes of shape (down ℕ,down ℕ).
In total degree n=p+q, let s_K : F_{p−1}H_n(Tot(K)) → F_pH_n(Tot(K)) be the consecutive
complete image-stage inclusion.

The predecessor map is transported from the finite stage p−1 when p>0 and is the zero map
between the zero negative stages when p=0. Together with the current-stage map it gives a
commutative square s_K → s_L. Applying the cokernel functor to this square gives the map on
the associated graded piece at (p,q).
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
In total degree n=p+q, define F_{(p:ℤ)−1}H_n(Tot(K)) → F_{(p:ℤ)−1}H_n(Tot(L)). If p>0, it is
the finite predecessor-stage map at p−1 transported through the complete-to-finite
comparisons. If p=0, it is the zero map between the negative finite stages F_{−1}, which are
zero objects. The integer predecessor is retained in both cases. -/
noncomputable def horizontalPrevTotalHomologyFiltrationMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyFiltration K (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) ⟶
      (horizontalTotalHomologyFiltration L (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) := by
  by_cases hp : 0 < p
  · exact horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
      f p q hp
  · have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    subst p
    exact horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex f q

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
Put n=p+q, let s_K and s_L be the inclusions F_{p−1}H_n(Tot) → F_pH_n(Tot), c(f) the
transported current-stage map, and a(f) the all-column predecessor map. Then s_K ≫ c(f) = a(f)
≫ s_L. At p=0 the predecessor stages are the zero stages at the integer −1; no positivity
assumption is needed for this square. -/
theorem horizontalTotalHomologyFiltrationStepMap_naturality
    (f : K ⟶ L) (p q : ℕ) :
    horizontalTotalHomologyFiltrationStepMap K p q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q ≫
        horizontalTotalHomologyFiltrationStepMap L p q := by
  by_cases hp : 0 < p
  · simpa [horizontalPrevTotalHomologyFiltrationMapOfBicomplex, hp] using
      horizontalTotalHomologyFiltrationStepMap_naturality_of_pos f p q hp
  · have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    subst p
    simpa [horizontalPrevTotalHomologyFiltrationMapOfBicomplex, hp] using
      horizontalTotalHomologyFiltrationStepMap_naturality_zero f q

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
The predecessor and current image-stage maps in total degree p+q define a morphism in Arrow(C)
from s_K : F_{p−1}(K) → F_p(K) to s_L : F_{p−1}(L) → F_p(L). Its left component is the
all-column predecessor map a(f), its right component is the transported current map c(f), and
their equation is a(f) ≫ s_L = s_K ≫ c(f). -/
noncomputable def horizontalTotalHomologyFiltrationStepSquareOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    Arrow.mk (horizontalTotalHomologyFiltrationStepMap K p q) ⟶
      Arrow.mk (horizontalTotalHomologyFiltrationStepMap L p q) :=
  Arrow.homMk
    (horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q)
    (horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q)
    (horizontalTotalHomologyFiltrationStepMap_naturality f p q).symm

@[simp]
theorem horizontalTotalHomologyFiltrationStepSquareOfBicomplex_left
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyFiltrationStepSquareOfBicomplex f p q).left =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q :=
  rfl

@[simp]
theorem horizontalTotalHomologyFiltrationStepSquareOfBicomplex_right
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyFiltrationStepSquareOfBicomplex f p q).right =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q :=
  rfl

/-- Let C be an abelian category, f : K → L a morphism of bicomplexes of shape (down ℕ,down ℕ),
and p,q ∈ ℕ. Applying the cokernel functor to the commutative square of consecutive
image-stage inclusions defines Gr_pH_{p+q}(Tot(K)) → Gr_pH_{p+q}(Tot(L)). Here Gr_p is
coker(F_{p−1} → F_p), with predecessor computed in ℤ. If π_K and π_L are the cokernel
projections and c(f) the current-stage map, the induced map a satisfies π_K ≫ a = c(f) ≫ π_L. -/
noncomputable def horizontalTotalHomologyGradedPieceMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    horizontalTotalHomologyGradedPiece K p q ⟶
      horizontalTotalHomologyGradedPiece L p q :=
  (Limits.coker C).map
    (horizontalTotalHomologyFiltrationStepSquareOfBicomplex f p q)

end HomologicalComplex₂

end
