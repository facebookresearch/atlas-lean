/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyFiltration

/-!
# Stabilization of the first-quadrant spectral-sequence pages

For bidegree `(p,q)`, every page
`r ≥ max (p+1) (q+2)` is identified with a fixed finite abutment term of the
complete filtration spectral object.  The comparison uses the generic
outer-index isomorphisms: the lower intervening stages are zero, while the
upper intervening relative homology vanishes in the required degree.
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

/-- Fixed lower index used for the finite abutment term. -/
abbrev horizontalAbutmentLowerIndex : EInt := ((-1 : ℤ) : EInt)

/-- Fixed upper index containing the full three-term homology window in total
degree `p+q`. -/
abbrev horizontalAbutmentUpperIndex (p q : ℕ) : EInt :=
  (((p + q + 1 : ℕ) : ℤ) : EInt)

/-- Lower filtration index of the page-`r` term in column `p`. -/
abbrev horizontalSpectralPageLowerIndex (r : ℤ) (p : ℕ) : EInt :=
  (((p : ℤ) - r : ℤ) : EInt)

/-- Upper filtration index of the page-`r` term in column `p`. -/
abbrev horizontalSpectralPageUpperIndex (r : ℤ) (p : ℕ) : EInt :=
  (((p : ℤ) + r - 1 : ℤ) : EInt)

/-- First page at which bidegree `(p,q)` has reached both finite abutment
bounds. -/
abbrev horizontalStablePageIndex (p q : ℕ) : ℤ :=
  max ((p : ℤ) + 1) ((q : ℤ) + 2)

/-- The stable-page index is a valid page index. -/
theorem horizontalStablePageIndex_one_le (p q : ℕ) :
    1 ≤ horizontalStablePageIndex p q :=
  le_trans (by omega) (le_max_left _ _)

/-- Lower-bound inequality built into the stable-page index. -/
theorem horizontalStablePageIndex_lower_bound (p q : ℕ) :
    (p : ℤ) + 1 ≤ horizontalStablePageIndex p q :=
  le_max_left _ _

/-- Upper-bound inequality built into the stable-page index. -/
theorem horizontalStablePageIndex_upper_bound (p q : ℕ) :
    (q : ℤ) + 2 ≤ horizontalStablePageIndex p q :=
  le_max_right _ _

/-- The two middle filtration indices lie between the fixed finite abutment
bounds. -/
theorem horizontalAbutmentIndices_le (p q : ℕ) :
    horizontalAbutmentLowerIndex ≤ horizontalFirstPageLowerIndex p ∧
      horizontalFirstPageUpperIndex p ≤ horizontalAbutmentUpperIndex p q := by
  constructor
  · apply WithBotTop.coe_monotone
    omega
  · apply WithBotTop.coe_monotone
    push_cast
    omega

/-- Fixed finite spectral-object term to which sufficiently late pages at
`(p,q)` stabilize. -/
noncomputable abbrev horizontalFirstQuadrantAbutmentTerm (p q : ℕ) : C :=
  let X := horizontalCompleteFiltrationSpectralObject K
  X.E
    (homOfLE (horizontalAbutmentIndices_le p q).1)
    (homOfLE (horizontalFirstPageIndex_le p))
    (homOfLE (horizontalAbutmentIndices_le p q).2)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
      (-((p + q : ℕ) : ℤ) + 1)

/-- A page satisfying the lower stable bound begins no later than the fixed
lower abutment stage. -/
theorem horizontalStablePageLowerIndex_le (r : ℤ) (p : ℕ)
    (h : (p : ℤ) + 1 ≤ r) :
    horizontalSpectralPageLowerIndex r p ≤ horizontalAbutmentLowerIndex :=
  WithBotTop.coe_monotone (by
    omega)

/-- A page satisfying the upper stable bound ends no earlier than the fixed
upper abutment stage. -/
theorem horizontalStablePageUpperIndex_le (r : ℤ) (p q : ℕ)
    (h : (q : ℤ) + 2 ≤ r) :
    horizontalAbutmentUpperIndex p q ≤
      horizontalSpectralPageUpperIndex r p :=
  WithBotTop.coe_monotone (by
    push_cast
    omega)

/-- Every valid page contains the first-page upper filtration stage. -/
theorem horizontalFirstPageUpperIndex_le_spectralPageUpper
    (r : ℤ) (p : ℕ) (hr : 1 ≤ r) :
    horizontalFirstPageUpperIndex p ≤
      horizontalSpectralPageUpperIndex r p :=
  WithBotTop.coe_monotone (by omega)

/-- The relative homology between the page lower stage and the fixed lower
abutment stage is zero under the lower stable bound. -/
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

/-- The relative homology between the fixed and page upper stages is zero in
the degree needed for stabilization. -/
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

/-- Every sufficiently late page object at `(p,q)` is canonically isomorphic
to the fixed finite abutment term. -/
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

/-- Stabilization isomorphism on the first page satisfying both bounds. -/
noncomputable def horizontalStablePageAbutmentIsoAtIndex (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page
      (horizontalStablePageIndex p q)).X (p, q) ≅
      horizontalFirstQuadrantAbutmentTerm K p q :=
  horizontalStablePageAbutmentIso K (horizontalStablePageIndex p q)
    (horizontalStablePageIndex_one_le p q) p q
    (horizontalStablePageIndex_lower_bound p q)
    (horizontalStablePageIndex_upper_bound p q)

end HomologicalComplex₂
