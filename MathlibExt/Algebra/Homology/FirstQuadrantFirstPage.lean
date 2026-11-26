/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSpectralSequenceSupport

/-!
# First-page terms as homology of consecutive filtration intervals

Let K be a nonnegative homological bicomplex in an abelian category C,
and let F_a be the complete horizontal filtration of Tot(K), indexed
by EInt = ℤ ∪ {−∞,+∞}. The pth consecutive interval has lower index
p−1 and upper index p.

Its relative homology in cochain degree −p−q is the first-page object:
E¹_(p,q) ≅ H_(−p−q)(Cone(F_(p−1) → F_p)).
The chain-to-cochain extension places total degree n at degree −n.
At p=0 the lower filtration stage is F_(−1)=0, so the formula
includes the zeroth column. The category object and morphism
worlds are independent.
-/

@[expose] public section

open CategoryTheory Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- For p ∈ ℕ, the lower first-page index is the finite element
p−1 of EInt, with subtraction performed in ℤ.
In particular the lower index at p=0 is −1. -/
def horizontalFirstPageLowerIndex (p : ℕ) : EInt :=
  @WithBotTop.coe ℤ ((p : ℤ) - 1)

/-- For p ∈ ℕ, the upper first-page index is p, viewed as a
finite element of EInt. Together with lower index p−1 it selects
the consecutive horizontal filtration interval for column p. -/
def horizontalFirstPageUpperIndex (p : ℕ) : EInt :=
  @WithBotTop.coe ℤ (p : ℤ)

theorem horizontalFirstPageIndex_le (p : ℕ) :
    horizontalFirstPageLowerIndex p ≤ horizontalFirstPageUpperIndex p :=
  WithBotTop.coe_monotone (by lia)

/-- For a nonnegative homological bicomplex K in an abelian
category, the relative first-page object is
H_(−p−q)(Cone(F_(p−1) → F_p)), for p,q ≥ 0.
It is the complete spectral object's interval homology after total
chain degree n is reindexed as cochain degree −n. -/
abbrev horizontalFirstPageRelativeHomology (p q : ℕ) : C :=
  ((horizontalCompleteFiltrationSpectralObject K).H (-(p : ℤ) - q)).obj
    (ComposableArrows.mk₁ (homOfLE (horizontalFirstPageIndex_le p)))

/-- For a nonnegative homological bicomplex K in an abelian
category C and p,q ≥ 0, the horizontal spectral sequence has
E¹_(p,q) ≅ H_(−p−q)(Cone(F_(p−1) → F_p)).
The finite indices are p−1 and p in EInt, so p=0 uses the zero
lower filtration stage. -/
noncomputable def horizontalFirstPageXIso (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      horizontalFirstPageRelativeHomology K p q :=
  (horizontalCompleteFiltrationSpectralObject K).spectralSequenceFirstPageXIso
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
    (p, q)
    (horizontalFirstPageLowerIndex p)
    (horizontalFirstPageUpperIndex p)
    rfl rfl (-(p : ℤ) - q) rfl

end HomologicalComplex₂

end
