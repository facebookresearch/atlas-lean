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

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Restriction of a spectral sequence to a later starting page

For r₀≤r₁, retain all pages r≥r₁, their differentials and successor homology comparisons from
a sequence starting at r₀. Page morphisms restrict in the same way.

Truncation preserves identity and composition, agrees with the original sequence at an
unchanged starting page, and two successive truncations equal the direct truncation.
Evaluation at a retained page commutes with this functor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
  {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ r₁ r₂ : ℤ}

/-- The spectral sequence beginning at a retained later page.

For r₀≤r₁, keep the original page complexes and successor comparisons for r≥r₁. -/
def truncate (S : SpectralSequence C c r₀) (r₁ : ℤ) (h : r₀ ≤ r₁) : SpectralSequence C c r₁ where
  page r hr := S.page r (h.trans hr)
  iso r r' x hrr' hr := S.iso r r' x hrr' (h.trans hr)

/-- The retained page complex is unchanged.

The page of the truncated sequence is the corresponding original page. -/
theorem truncate_page (S : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (r : ℤ) (hr : r₁ ≤ r) :
    (S.truncate r₁ h).page r hr = S.page r (h.trans hr) := rfl

/-- The retained page object is unchanged.

At every index, truncation keeps the original page object. -/
theorem truncate_page_X (S : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (r : ℤ) (hr : r₁ ≤ r) (x : κ) :
    ((S.truncate r₁ h).page r hr).X x = (S.page r (h.trans hr)).X x := rfl

/-- The retained page differential is unchanged.

Truncation keeps the original differential between every pair of indices. -/
theorem truncate_page_d (S : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (r : ℤ) (hr : r₁ ≤ r) (x y : κ) :
    ((S.truncate r₁ h).page r hr).d x y = (S.page r (h.trans hr)).d x y := rfl

/-- The retained successor homology comparison is unchanged.

For r+1=r′, use the original successor isomorphism. -/
theorem truncate_iso (S : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (r r' : ℤ) (x : κ)
    (hrr' : r + 1 = r') (hr : r₁ ≤ r) :
    (S.truncate r₁ h).iso r r' x hrr' hr = S.iso r r' x hrr' (h.trans hr) := rfl

/-- The restriction of a spectral-sequence morphism.

Keep its maps and successor compatibility at every retained page. -/
def truncateMap {S T : SpectralSequence C c r₀} (α : S ⟶ T) (r₁ : ℤ) (h : r₀ ≤ r₁) :
    S.truncate r₁ h ⟶ T.truncate r₁ h where
  hom r hr := α.hom r (h.trans hr)
  comm r r' x hrr' hr := α.comm r r' x hrr' (h.trans hr)

/-- The retained page map is unchanged.

The map at r of truncateMap is the original page map at r. -/
theorem truncateMap_hom {S T : SpectralSequence C c r₀} (α : S ⟶ T) (h : r₀ ≤ r₁)
    (r : ℤ) (hr : r₁ ≤ r) :
    (truncateMap α r₁ h).hom r hr = α.hom r (h.trans hr) := rfl

/-- The retained component map is unchanged.

Every component of a truncated page map is the original component. -/
theorem truncateMap_hom_f {S T : SpectralSequence C c r₀} (α : S ⟶ T) (h : r₀ ≤ r₁)
    (r : ℤ) (hr : r₁ ≤ r) (x : κ) :
    ((truncateMap α r₁ h).hom r hr).f x = (α.hom r (h.trans hr)).f x := rfl

/-- Truncation preserves identity morphisms.

The restricted identity is the identity of the truncated sequence. -/
theorem truncateMap_id (S : SpectralSequence C c r₀) (h : r₀ ≤ r₁) :
    truncateMap (𝟙 S) r₁ h = 𝟙 (S.truncate r₁ h) := by
  apply hom_ext
  intro r hr
  rfl

/-- Truncation preserves composition of morphisms.

Restricting a composite gives the composite of its restrictions. -/
theorem truncateMap_comp {S T U : SpectralSequence C c r₀} (α : S ⟶ T) (β : T ⟶ U) (h : r₀ ≤ r₁) :
    truncateMap (α ≫ β) r₁ h = truncateMap α r₁ h ≫ truncateMap β r₁ h := by
  apply hom_ext
  intro r hr
  rfl

/-- Truncation at the starting page gives the same sequence.

Retaining pages from r₀ leaves a sequence starting at r₀ unchanged. -/
theorem truncate_refl (S : SpectralSequence C c r₀) : S.truncate r₀ (le_refl r₀) = S := rfl

/-- Successive truncations equal direct truncation.

For r₀≤r₁≤r₂, truncate first at r₁ then r₂ to obtain the direct truncation at r₂. -/
theorem truncate_trans (S : SpectralSequence C c r₀) (h₀₁ : r₀ ≤ r₁) (h₁₂ : r₁ ≤ r₂) :
    (S.truncate r₁ h₀₁).truncate r₂ h₁₂ = S.truncate r₂ (h₀₁.trans h₁₂) := rfl

/-- Successive restrictions of morphisms equal direct restriction.

The two-step truncated morphism equals the restriction to r₂. -/
theorem truncateMap_trans {S T : SpectralSequence C c r₀} (α : S ⟶ T)
    (h₀₁ : r₀ ≤ r₁) (h₁₂ : r₁ ≤ r₂) :
    truncateMap (truncateMap α r₁ h₀₁) r₂ h₁₂ = truncateMap α r₂ (h₀₁.trans h₁₂) := by
  apply hom_ext
  intro r hr
  rfl

/-- Equality on retained pages gives equality of truncated morphisms.

If α and β agree at every r≥r₁, their truncations at r₁ are equal. -/
theorem truncateMap_eq {S T : SpectralSequence C c r₀} (α β : S ⟶ T) (h : r₀ ≤ r₁)
    (heq : ∀ (r : ℤ) (hr : r₁ ≤ r), α.hom r (h.trans hr) = β.hom r (h.trans hr)) :
    truncateMap α r₁ h = truncateMap β r₁ h := by
  apply hom_ext
  intro r hr
  exact heq r hr

variable (C c)

/-- The functor retaining a later page range.

For r₀≤r₁, truncate sequences and morphisms to the starting page r₁. -/
def truncationFunctor (r₀ r₁ : ℤ) (h : r₀ ≤ r₁) :
    SpectralSequence C c r₀ ⥤ SpectralSequence C c r₁ where
  obj S := S.truncate r₁ h
  map α := truncateMap α r₁ h
  map_id S := truncateMap_id S h
  map_comp α β := truncateMap_comp α β h

/-- Objects of the truncation functor.

Its value at S is S.truncate r₁. -/
theorem truncationFunctor_obj (h : r₀ ≤ r₁) (S : SpectralSequence C c r₀) :
    (truncationFunctor C c r₀ r₁ h).obj S = S.truncate r₁ h := rfl

/-- Page maps of the truncation functor.

On a morphism, its page-r map is the original page-r map. -/
theorem truncationFunctor_map_hom (h : r₀ ≤ r₁) {S T : SpectralSequence C c r₀} (α : S ⟶ T)
    (r : ℤ) (hr : r₁ ≤ r) :
    ((truncationFunctor C c r₀ r₁ h).map α).hom r hr = α.hom r (h.trans hr) := rfl

/-- Page evaluation commutes with truncation.

For retained r, truncation followed by page evaluation equals the original page functor. -/
theorem truncationFunctor_pageFunctor (h : r₀ ≤ r₁) (r : ℤ) (hr : r₁ ≤ r) :
    truncationFunctor C c r₀ r₁ h ⋙ pageFunctor C c r₁ r hr = pageFunctor C c r₀ r (h.trans hr) := rfl

/-- The unchanged-start truncation functor is the identity.

At r₀=r₁, the truncation functor is the identity. -/
theorem truncationFunctor_refl (r₀ : ℤ) : truncationFunctor C c r₀ r₀ (le_refl r₀) = 𝟭 _ := rfl

/-- Composition of truncation functors.

The functors for r₀→r₁ and r₁→r₂ compose to the functor for r₀→r₂. -/
theorem truncationFunctor_trans (h₀₁ : r₀ ≤ r₁) (h₁₂ : r₁ ≤ r₂) :
    truncationFunctor C c r₀ r₁ h₀₁ ⋙ truncationFunctor C c r₁ r₂ h₁₂ =
      truncationFunctor C c r₀ r₂ (h₀₁.trans h₁₂) := rfl

end CategoryTheory.SpectralSequence

end
