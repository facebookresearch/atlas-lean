/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantConvergence
public import
  MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationSpectralNaturality
public import MathlibExt.Algebra.Homology.SpectralObjectMapNaturality

/-!
# Naturality of the bounded stable-page comparison with the canonical abutment

Let f : K → L be a map of nonnegative homological bicomplexes in an
abelian category C, and put n=p+q. The complete-filtration spectral
map induces a morphism on the fixed stable page
r₀=max(p+1,q+2).

The canonical abutment term B_(p,q) uses the four-stage interval
−∞→p−1→p→n+1, with relative degrees −n−1,−n,−n+1.
It also receives the map induced by f. For any valid page r meeting
r≥p+1 and r≥q+2, the stable-to-canonical comparisons χ_K,χ_L satisfy
χ_L ∘ m_r(f) = B_(p,q)(f) ∘ χ_K.
Here m_r(f) is the map of the page's four-stage spectral term,
transported through its page-object identifications.
The category object and morphism worlds are independent.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- For a map f : K → L of nonnegative homological bicomplexes
in an abelian category and p,q∈ℕ, the stable-page map is
E^(r₀)_K(p,q) → E^(r₀)_L(p,q), r₀=max(p+1,q+2).
It is the induced map on the page's four-stage spectral E-term
conjugated by the canonical page-object identifications. -/
noncomputable def horizontalStablePageMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page
      (horizontalStablePageIndex p q)).X (p, q) ⟶
      ((horizontalFirstQuadrantSpectralSequence L).page
        (horizontalStablePageIndex p q)).X (p, q) := by
  let data :=
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
  let r := horizontalStablePageIndex p q
  let hr := horizontalStablePageIndex_one_le p q
  let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -((p + q : ℕ) : ℤ)
  let n₂ : ℤ := -((p + q : ℕ) : ℤ) + 1
  let eK := (horizontalCompleteFiltrationSpectralObject K).spectralSequencePageXIso
    data r hr (p, q) (horizontalSpectralPageLowerIndex r p)
    (horizontalFirstPageLowerIndex p) (horizontalFirstPageUpperIndex p)
    (horizontalSpectralPageUpperIndex r p) rfl rfl rfl rfl
    n₀ n₁ n₂ (by
      change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
      push_cast
      omega)
  let eL := (horizontalCompleteFiltrationSpectralObject L).spectralSequencePageXIso
    data r hr (p, q) (horizontalSpectralPageLowerIndex r p)
    (horizontalFirstPageLowerIndex p) (horizontalFirstPageUpperIndex p)
    (horizontalSpectralPageUpperIndex r p) rfl rfl rfl rfl
    n₀ n₁ n₂ (by
      change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
      push_cast
      omega)
  let m := CategoryTheory.Abelian.SpectralObject.Hom.EMap
    (horizontalCompleteFiltrationSpectralObjectMap f)
    (homOfLE (data.le₀₁ r (p, q)))
    (homOfLE (data.le₁₂ (p, q)))
    (homOfLE (data.le₂₃ r (p, q))) n₀ n₁ n₂
  exact eK.hom ≫ m ≫ eL.inv

/-- For a map f : K → L of nonnegative homological bicomplexes
in an abelian category and n=p+q, the induced canonical abutment
map acts on the spectral E-term at stages
−∞, p−1, p, n+1 and degrees −n−1,−n,−n+1.
It is the map of those relative connecting-map short complexes. -/
noncomputable def horizontalCanonicalAbutmentMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    horizontalFirstQuadrantCanonicalAbutmentTerm K p q ⟶
      horizontalFirstQuadrantCanonicalAbutmentTerm L p q :=
  CategoryTheory.Abelian.SpectralObject.Hom.EMap
    (horizontalCompleteFiltrationSpectralObjectMap f)
    (horizontalCanonicalAbutmentLowerMap p)
    (horizontalCanonicalAbutmentMiddleMap p)
    (horizontalCanonicalAbutmentUpperMap p q)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
    (-((p + q : ℕ) : ℤ) + 1)

@[simp]
theorem horizontalCanonicalAbutmentMapOfBicomplex_eq
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentMapOfBicomplex f p q =
      CategoryTheory.Abelian.SpectralObject.Hom.EMap
        (horizontalCompleteFiltrationSpectralObjectMap f)
        (horizontalCanonicalAbutmentLowerMap p)
        (horizontalCanonicalAbutmentMiddleMap p)
        (horizontalCanonicalAbutmentUpperMap p q)
        (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
        (-((p + q : ℕ) : ℤ) + 1) :=
  rfl

/-- For a bicomplex map f : K → L in an abelian category,
p,q∈ℕ and r∈ℤ with r≥1, r≥p+1 and r≥q+2, the comparisons
χ_K : E^r_K(p,q) ≅ B_K(p,q) and χ_L satisfy
χ_L ∘ m_r(f) = B_(p,q)(f) ∘ χ_K.
The page map m_r(f) is transported through the four-stage
page presentation, and B uses bottom −∞ and upper stage p+q+1. -/
theorem horizontalStablePageCanonicalAbutmentIso_naturality
    (f : K ⟶ L) (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    (let data :=
        CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
      let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
      let n₁ : ℤ := -((p + q : ℕ) : ℤ)
      let n₂ : ℤ := -((p + q : ℕ) : ℤ) + 1
      let eK :=
        (horizontalCompleteFiltrationSpectralObject K).spectralSequencePageXIso
          data r hr (p, q) (horizontalSpectralPageLowerIndex r p)
          (horizontalFirstPageLowerIndex p) (horizontalFirstPageUpperIndex p)
          (horizontalSpectralPageUpperIndex r p) rfl rfl rfl rfl
          n₀ n₁ n₂ (by
            change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
            push_cast
            omega)
      let eL :=
        (horizontalCompleteFiltrationSpectralObject L).spectralSequencePageXIso
          data r hr (p, q) (horizontalSpectralPageLowerIndex r p)
          (horizontalFirstPageLowerIndex p) (horizontalFirstPageUpperIndex p)
          (horizontalSpectralPageUpperIndex r p) rfl rfl rfl rfl
          n₀ n₁ n₂ (by
            change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
            push_cast
            omega)
      let m := CategoryTheory.Abelian.SpectralObject.Hom.EMap
        (horizontalCompleteFiltrationSpectralObjectMap f)
        (homOfLE (data.le₀₁ r (p, q)))
        (homOfLE (data.le₁₂ (p, q)))
        (homOfLE (data.le₂₃ r (p, q))) n₀ n₁ n₂
      eK.hom ≫ m ≫ eL.inv) ≫
      (horizontalStablePageCanonicalAbutmentIso
        L r hr p q hlower hupper).hom =
    (horizontalStablePageCanonicalAbutmentIso
        K r hr p q hlower hupper).hom ≫
      horizontalCanonicalAbutmentMapOfBicomplex f p q := by
  let XK := horizontalCompleteFiltrationSpectralObject K
  let XL := horizontalCompleteFiltrationSpectralObject L
  let φ := horizontalCompleteFiltrationSpectralObjectMap f
  let data :=
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
  let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -((p + q : ℕ) : ℤ)
  let n₂ : ℤ := -((p + q : ℕ) : ℤ) + 1
  let pageLower : EInt := horizontalSpectralPageLowerIndex r p
  let lower : EInt := horizontalAbutmentLowerIndex
  let firstLower : EInt := horizontalFirstPageLowerIndex p
  let firstUpper : EInt := horizontalFirstPageUpperIndex p
  let upper : EInt := horizontalAbutmentUpperIndex p q
  let pageUpper : EInt := horizontalSpectralPageUpperIndex r p
  let aPageLower : pageLower ⟶ firstLower :=
    homOfLE (data.le₀₁ r (p, q))
  let aLower : lower ⟶ firstLower :=
    homOfLE (horizontalAbutmentIndices_le p q).1
  let aBottom : (⊥ : EInt) ⟶ firstLower := homOfLE bot_le
  let aMiddle : firstLower ⟶ firstUpper :=
    homOfLE (horizontalFirstPageIndex_le p)
  let aUpper : firstUpper ⟶ upper :=
    homOfLE (horizontalAbutmentIndices_le p q).2
  let aPageUpper : firstUpper ⟶ pageUpper :=
    homOfLE (horizontalFirstPageUpperIndex_le_spectralPageUpper r p hr)
  let mPage := CategoryTheory.Abelian.SpectralObject.Hom.EMap φ
    aPageLower aMiddle aPageUpper n₀ n₁ n₂
  let mLower := CategoryTheory.Abelian.SpectralObject.Hom.EMap φ
    aLower aMiddle aPageUpper n₀ n₁ n₂
  let mUpper := CategoryTheory.Abelian.SpectralObject.Hom.EMap φ
    aLower aMiddle aUpper n₀ n₁ n₂
  let mCanonical := CategoryTheory.Abelian.SpectralObject.Hom.EMap φ
    aBottom aMiddle aUpper n₀ n₁ n₂
  let ePageK := XK.spectralSequencePageXIso data r hr (p, q)
    pageLower firstLower firstUpper pageUpper rfl rfl rfl rfl
    n₀ n₁ n₂ (by
      change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
      push_cast
      omega)
  let ePageL := XL.spectralSequencePageXIso data r hr (p, q)
    pageLower firstLower firstUpper pageUpper rfl rfl rfl rfl
    n₀ n₁ n₂ (by
      change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
      push_cast
      omega)
  let eLowerK := XK.isoMapFourδ₁Toδ₀'
    pageLower lower firstLower firstUpper pageUpper
    (horizontalStablePageLowerIndex_le r p hlower)
    (horizontalAbutmentIndices_le p q).1
    (horizontalFirstPageIndex_le p)
    (horizontalFirstPageUpperIndex_le_spectralPageUpper r p hr)
    n₀ n₁ n₂
    (horizontalStableLowerRelativeHomologyIsZero K r p q hlower)
  let eLowerL := XL.isoMapFourδ₁Toδ₀'
    pageLower lower firstLower firstUpper pageUpper
    (horizontalStablePageLowerIndex_le r p hlower)
    (horizontalAbutmentIndices_le p q).1
    (horizontalFirstPageIndex_le p)
    (horizontalFirstPageUpperIndex_le_spectralPageUpper r p hr)
    n₀ n₁ n₂
    (horizontalStableLowerRelativeHomologyIsZero L r p q hlower)
  let eUpperK := XK.isoMapFourδ₄Toδ₃'
    lower firstLower firstUpper upper pageUpper
    (horizontalAbutmentIndices_le p q).1
    (horizontalFirstPageIndex_le p)
    (horizontalAbutmentIndices_le p q).2
    (horizontalStablePageUpperIndex_le r p q hupper)
    n₀ n₁ n₂
    (horizontalStableUpperRelativeHomologyIsZero K r p q hupper)
  let eUpperL := XL.isoMapFourδ₄Toδ₃'
    lower firstLower firstUpper upper pageUpper
    (horizontalAbutmentIndices_le p q).1
    (horizontalFirstPageIndex_le p)
    (horizontalAbutmentIndices_le p q).2
    (horizontalStablePageUpperIndex_le r p q hupper)
    n₀ n₁ n₂
    (horizontalStableUpperRelativeHomologyIsZero L r p q hupper)
  let eBottomK := XK.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) lower firstLower firstUpper upper bot_le
    (horizontalAbutmentIndices_le p q).1
    (horizontalFirstPageIndex_le p)
    (horizontalAbutmentIndices_le p q).2
    n₀ n₁ n₂
    (horizontalBottomToNegativeRelativeHomologyIsZero K p q)
  let eBottomL := XL.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) lower firstLower firstUpper upper bot_le
    (horizontalAbutmentIndices_le p q).1
    (horizontalFirstPageIndex_le p)
    (horizontalAbutmentIndices_le p q).2
    n₀ n₁ n₂
    (horizontalBottomToNegativeRelativeHomologyIsZero L p q)
  have hLower : eLowerK.hom ≫ mLower =
      mPage ≫ eLowerL.hom := by
    simpa [XK, XL, φ, n₀, n₁, n₂, pageLower, lower, firstLower,
      firstUpper, pageUpper, aPageLower, aLower, aMiddle, aPageUpper,
      eLowerK, eLowerL, mPage, mLower] using
      CategoryTheory.Abelian.SpectralObject.Hom.map_EMap φ
        aPageLower aMiddle aPageUpper aLower aMiddle aPageUpper
        (fourδ₁Toδ₀' pageLower lower firstLower firstUpper pageUpper
          (horizontalStablePageLowerIndex_le r p hlower)
          (horizontalAbutmentIndices_le p q).1
          (horizontalFirstPageIndex_le p)
          (horizontalFirstPageUpperIndex_le_spectralPageUpper r p hr))
        n₀ n₁ n₂
  have hUpperForward : eUpperK.hom ≫ mLower =
      mUpper ≫ eUpperL.hom := by
    simpa [XK, XL, φ, n₀, n₁, n₂, lower, firstLower, firstUpper,
      upper, pageUpper, aLower, aMiddle, aUpper, aPageUpper,
      eUpperK, eUpperL, mLower, mUpper] using
      CategoryTheory.Abelian.SpectralObject.Hom.map_EMap φ
        aLower aMiddle aUpper aLower aMiddle aPageUpper
        (fourδ₄Toδ₃' lower firstLower firstUpper upper pageUpper
          (horizontalAbutmentIndices_le p q).1
          (horizontalFirstPageIndex_le p)
          (horizontalAbutmentIndices_le p q).2
          (horizontalStablePageUpperIndex_le r p q hupper))
        n₀ n₁ n₂
  have hUpper : mLower ≫ eUpperL.inv =
      eUpperK.inv ≫ mUpper := by
    apply (cancel_epi eUpperK.hom).1
    simp only [eUpperK.hom_inv_id_assoc]
    rw [← Category.assoc, hUpperForward]
    simp
  have hBottomForward : eBottomK.hom ≫ mUpper =
      mCanonical ≫ eBottomL.hom := by
    simpa [XK, XL, φ, n₀, n₁, n₂, lower, firstLower, firstUpper,
      upper, aLower, aBottom, aMiddle, aUpper, eBottomK, eBottomL,
      mUpper, mCanonical] using
      CategoryTheory.Abelian.SpectralObject.Hom.map_EMap φ
        aBottom aMiddle aUpper aLower aMiddle aUpper
        (fourδ₁Toδ₀' (⊥ : EInt) lower firstLower firstUpper upper
          bot_le (horizontalAbutmentIndices_le p q).1
          (horizontalFirstPageIndex_le p)
          (horizontalAbutmentIndices_le p q).2)
        n₀ n₁ n₂
  have hBottom : mUpper ≫ eBottomL.inv =
      eBottomK.inv ≫ mCanonical := by
    apply (cancel_epi eBottomK.hom).1
    simp only [eBottomK.hom_inv_id_assoc]
    rw [← Category.assoc, hBottomForward]
    simp
  dsimp only [horizontalStablePageCanonicalAbutmentIso,
    horizontalStablePageAbutmentIso, horizontalFiniteToCanonicalAbutmentIso,
    horizontalCanonicalAbutmentMapOfBicomplex]
  have hFinal :
      (ePageK.hom ≫ mPage ≫ ePageL.inv) ≫
          (ePageL.hom ≫ eLowerL.hom ≫ eUpperL.inv ≫ eBottomL.inv) =
        (ePageK.hom ≫ eLowerK.hom ≫ eUpperK.inv ≫ eBottomK.inv) ≫
          mCanonical := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← reassoc_of% hLower, reassoc_of% hUpper, hBottom]
  simpa [XK, XL, φ, data, n₀, n₁, n₂, pageLower, lower, firstLower,
    firstUpper, upper, pageUpper, aPageLower, aLower, aBottom, aMiddle,
    aUpper, aPageUpper, mPage, mLower, mUpper, mCanonical, ePageK, ePageL,
    eLowerK, eLowerL, eUpperK, eUpperL, eBottomK, eBottomL] using hFinal

end HomologicalComplex₂

end
