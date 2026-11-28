/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyFiltration

/-!
# Late first-quadrant pages stabilize to a finite abutment term

Let K be a nonnegative homological bicomplex in an abelian category C,
with complete horizontal filtration F. For n=p+q, the page-r
four-stage presentation has indices
p−r ≤ p−1 ≤ p ≤ p+r−1.

The fixed finite abutment term A_(p,q) uses instead
−1 ≤ p−1 ≤ p ≤ n+1, in middle cochain degree −n.
If r≥p+1, the intervening lower stages are zero. If r≥q+2,
the intervening upper relative group vanishes in degree −n−1.
Thus every valid page satisfying both bounds has
E^r_(p,q) ≅ A_(p,q).

The first such page is r₀=max(p+1,q+2). The finite lower index is
the integer −1, and the upper index is n+1; the category object
and morphism universes are independent.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The finite lower index for the first-quadrant abutment term
is −1, viewed as an element of EInt.
It is a negative finite filtration stage, distinct from the
bottom element −∞. -/
abbrev horizontalAbutmentLowerIndex : EInt := ((-1 : ℤ) : EInt)

/-- For p,q∈ℕ, the fixed upper abutment index is p+q+1 in EInt.
It contains the chain degrees needed to compute total homology
in degree n=p+q. -/
abbrev horizontalAbutmentUpperIndex (p q : ℕ) : EInt :=
  (((p + q + 1 : ℕ) : ℤ) : EInt)

/-- For r∈ℤ and p∈ℕ, the lower outer filtration index of the
page-r term in horizontal degree p is the finite integer p−r
in EInt. -/
abbrev horizontalSpectralPageLowerIndex (r : ℤ) (p : ℕ) : EInt :=
  (((p : ℤ) - r : ℤ) : EInt)

/-- For r∈ℤ and p∈ℕ, the upper outer filtration index of the
page-r term in horizontal degree p is the finite integer p+r−1
in EInt. -/
abbrev horizontalSpectralPageUpperIndex (r : ℤ) (p : ℕ) : EInt :=
  (((p : ℤ) + r - 1 : ℤ) : EInt)

/-- For p,q∈ℕ, the canonical stable-page index is
r₀=max(p+1,q+2), computed in ℤ.
It is the least page meeting the lower and upper finite-abutment
bounds. -/
abbrev horizontalStablePageIndex (p q : ℕ) : ℤ :=
  max ((p : ℤ) + 1) ((q : ℤ) + 2)

/-- For p,q∈ℕ, the index r₀=max(p+1,q+2) satisfies 1≤r₀.
Thus it is a valid index for a spectral sequence starting at page 1. -/
theorem horizontalStablePageIndex_one_le (p q : ℕ) :
    1 ≤ horizontalStablePageIndex p q :=
  le_trans (by omega) (le_max_left _ _)

/-- For p,q∈ℕ, the canonical stable index satisfies
p+1≤max(p+1,q+2), the bound controlling the lower page stage. -/
theorem horizontalStablePageIndex_lower_bound (p q : ℕ) :
    (p : ℤ) + 1 ≤ horizontalStablePageIndex p q :=
  le_max_left _ _

/-- For p,q∈ℕ, the canonical stable index satisfies
q+2≤max(p+1,q+2), the bound controlling the upper page stage. -/
theorem horizontalStablePageIndex_upper_bound (p q : ℕ) :
    (q : ℤ) + 2 ≤ horizontalStablePageIndex p q :=
  le_max_right _ _

/-- For p,q∈ℕ and n=p+q, the middle first-page indices satisfy
−1≤p−1 and p≤n+1 in EInt.
Hence the consecutive interval p−1≤p lies between the fixed
finite abutment endpoints. -/
theorem horizontalAbutmentIndices_le (p q : ℕ) :
    horizontalAbutmentLowerIndex ≤ horizontalFirstPageLowerIndex p ∧
      horizontalFirstPageUpperIndex p ≤ horizontalAbutmentUpperIndex p q := by
  constructor
  · apply WithBotTop.coe_monotone
    omega
  · apply WithBotTop.coe_monotone
    push_cast
    omega

/-- For a nonnegative homological bicomplex K in an abelian
category and n=p+q, A_(p,q) is the complete spectral object's
four-stage E-term on −1→p−1→p→n+1.
Its connecting-map short complex uses relative cochain
homology degrees −n−1, −n and −n+1, with middle interval
F_(p−1) → F_p. -/
noncomputable abbrev horizontalFirstQuadrantAbutmentTerm (p q : ℕ) : C :=
  let X := horizontalCompleteFiltrationSpectralObject K
  X.E
    (homOfLE (horizontalAbutmentIndices_le p q).1)
    (homOfLE (horizontalFirstPageIndex_le p))
    (homOfLE (horizontalAbutmentIndices_le p q).2)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
      (-((p + q : ℕ) : ℤ) + 1)

/-- For r∈ℤ and p∈ℕ, the inequality p+1≤r implies
p−r≤−1 in EInt.
Thus the page's lower outer stage is no later than the fixed
finite lower abutment stage. -/
theorem horizontalStablePageLowerIndex_le (r : ℤ) (p : ℕ)
    (h : (p : ℤ) + 1 ≤ r) :
    horizontalSpectralPageLowerIndex r p ≤ horizontalAbutmentLowerIndex :=
  WithBotTop.coe_monotone (by
    omega)

/-- For r∈ℤ, p,q∈ℕ and n=p+q, the inequality q+2≤r implies
n+1≤p+r−1 in EInt.
Thus the page's upper outer stage contains the fixed finite
upper abutment stage. -/
theorem horizontalStablePageUpperIndex_le (r : ℤ) (p q : ℕ)
    (h : (q : ℤ) + 2 ≤ r) :
    horizontalAbutmentUpperIndex p q ≤
      horizontalSpectralPageUpperIndex r p :=
  WithBotTop.coe_monotone (by
    push_cast
    omega)

/-- For r≥1 and p∈ℕ, the first-page upper stage p satisfies
p≤p+r−1 in EInt.
This is the ordering of the middle upper and page upper indices. -/
theorem horizontalFirstPageUpperIndex_le_spectralPageUpper
    (r : ℤ) (p : ℕ) (hr : 1 ≤ r) :
    horizontalFirstPageUpperIndex p ≤
      horizontalSpectralPageUpperIndex r p :=
  WithBotTop.coe_monotone (by omega)

/-- For a nonnegative homological bicomplex K in an abelian
category, n=p+q and r≥p+1, the relative group of
F_(p−r) → F_(−1) is zero in cochain degree −n+1.
Both endpoint filtration complexes are zero. -/
theorem horizontalStableLowerRelativeHomologyIsZero
    (r : ℤ) (p q : ℕ) (h : (p : ℤ) + 1 ≤ r) :
    IsZero (((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q : ℕ) : ℤ) + 1)).obj
        (mk₁ (homOfLE (horizontalStablePageLowerIndex_le r p h)))) := by
  apply horizontalCompleteFiltrationSpectralObject_H_isZero_of_obj_isZero K
  · apply horizontalCompleteFiltrationCochainDiagram_obj_isZero_of_neg K
    omega
  · apply horizontalCompleteFiltrationCochainDiagram_obj_isZero_of_neg K
    omega

/-- For a nonnegative homological bicomplex K in an abelian
category, n=p+q and r≥q+2, the interval
F_(n+1) → F_(p+r−1) has zero cochain homology in degree −n−1.
Both stages exhaust the relevant total chain degree n+1. -/
theorem horizontalStableUpperRelativeHomologyIsZero
    (r : ℤ) (p q : ℕ) (h : (q : ℤ) + 2 ≤ r) :
    IsZero (((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q + 1 : ℕ) : ℤ))).obj
        (mk₁ (homOfLE (horizontalStablePageUpperIndex_le r p q h)))) := by
  let t : ℕ := p + q + 1
  let a : ℤ := (t : ℤ)
  let b : ℤ := (p : ℤ) + r - 1
  have ha : 0 ≤ a := by dsimp [a]; omega
  have hb : 0 ≤ b := by dsimp [b]; omega
  have hat : t ≤ a.toNat := by dsimp [a, t]; simp
  have hbt : t ≤ b.toNat := by dsimp [b, t]; omega
  have hsource : IsIso
      ((horizontalCompleteFilteredTotalToTotal K (a : EInt)).f t) :=
    horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg K a ha t hat
  have htarget : IsIso
      ((horizontalCompleteFilteredTotalToTotal K (b : EInt)).f t) :=
    horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg K b hb t hbt
  let _ := hsource
  let _ := htarget
  have hmap : IsIso ((horizontalCompleteFilteredTotalMap K
      (horizontalStablePageUpperIndex_le r p q h)).f t) :=
    horizontalCompleteFilteredTotalMap_f_isIso_of_toTotal K
      (horizontalStablePageUpperIndex_le r p q h) t
  let _ := hmap
  have hcochain : IsIso
      (((horizontalCompleteFiltrationCochainDiagram K).map
        (homOfLE (horizontalStablePageUpperIndex_le r p q h))).f
          (-(t : ℤ))) :=
    horizontalCompleteFiltrationCochainDiagram_map_f_isIso K
      (horizontalStablePageUpperIndex_le r p q h) t
  have hepi : Epi
      (((horizontalCompleteFiltrationCochainDiagram K).map
        (homOfLE (horizontalStablePageUpperIndex_le r p q h))).f
          (-(t : ℤ))) :=
    @IsIso.epi_of_iso _ _ _ _ _ hcochain
  let _ := hepi
  change IsZero (((horizontalCompleteFiltrationSpectralObject K).H
    (-(t : ℤ))).obj
      (mk₁ (homOfLE (horizontalStablePageUpperIndex_le r p q h))))
  exact horizontalCompleteFiltrationSpectralObject_H_isZero_of_epi_f K
    (horizontalStablePageUpperIndex_le r p q h) (-(t : ℤ))

/-- For a nonnegative homological bicomplex K in an abelian
category, p,q∈ℕ and r∈ℤ with r≥1, r≥p+1 and r≥q+2,
there is an isomorphism E^r_(p,q) ≅ A_(p,q).
The fixed finite term uses stages −1,p−1,p,p+q+1 in middle
cochain degree −p−q. -/
noncomputable def horizontalStablePageAbutmentIso
    (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    ((horizontalFirstQuadrantSpectralSequence K).page r).X (p, q) ≅
      horizontalFirstQuadrantAbutmentTerm K p q := by
  let X := horizontalCompleteFiltrationSpectralObject K
  let data :=
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
  let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -((p + q : ℕ) : ℤ)
  let n₂ : ℤ := -((p + q : ℕ) : ℤ) + 1
  let ePage := X.spectralSequencePageXIso data r hr (p, q)
    (horizontalSpectralPageLowerIndex r p)
    (horizontalFirstPageLowerIndex p)
    (horizontalFirstPageUpperIndex p)
    (horizontalSpectralPageUpperIndex r p)
    rfl rfl rfl rfl n₀ n₁ n₂ (by
      change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
      push_cast
      omega)
  let eLower := X.isoMapFourδ₁Toδ₀'
    (horizontalSpectralPageLowerIndex r p)
    horizontalAbutmentLowerIndex
    (horizontalFirstPageLowerIndex p)
    (horizontalFirstPageUpperIndex p)
    (horizontalSpectralPageUpperIndex r p)
    (horizontalStablePageLowerIndex_le r p hlower)
    (horizontalAbutmentIndices_le p q).1
    (horizontalFirstPageIndex_le p)
    (horizontalFirstPageUpperIndex_le_spectralPageUpper r p hr)
    n₀ n₁ n₂
    (horizontalStableLowerRelativeHomologyIsZero K r p q hlower)
  let eUpper := X.isoMapFourδ₄Toδ₃'
    horizontalAbutmentLowerIndex
    (horizontalFirstPageLowerIndex p)
    (horizontalFirstPageUpperIndex p)
    (horizontalAbutmentUpperIndex p q)
    (horizontalSpectralPageUpperIndex r p)
    (horizontalAbutmentIndices_le p q).1
    (horizontalFirstPageIndex_le p)
    (horizontalAbutmentIndices_le p q).2
    (horizontalStablePageUpperIndex_le r p q hupper)
    n₀ n₁ n₂
    (horizontalStableUpperRelativeHomologyIsZero K r p q hupper)
  exact ePage ≪≫ eLower ≪≫ eUpper.symm

/-- For a nonnegative homological bicomplex K in an abelian
category and p,q∈ℕ, the page r₀=max(p+1,q+2) satisfies
E^(r₀)_(p,q) ≅ A_(p,q), the fixed finite four-stage abutment term. -/
noncomputable def horizontalStablePageAbutmentIsoAtIndex (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page
      (horizontalStablePageIndex p q)).X (p, q) ≅
      horizontalFirstQuadrantAbutmentTerm K p q :=
  horizontalStablePageAbutmentIso K (horizontalStablePageIndex p q)
    (horizontalStablePageIndex_one_le p q) p q
    (horizontalStablePageIndex_lower_bound p q)
    (horizontalStablePageIndex_upper_bound p q)

end HomologicalComplex₂
