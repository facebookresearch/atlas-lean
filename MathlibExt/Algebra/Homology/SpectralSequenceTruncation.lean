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
# Restricting a native spectral sequence to later pages

The restricted sequence uses the original page complexes, differentials,
and successor homology isomorphisms. Restriction of the native morphisms
is functorial and commutes with evaluating any retained page.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
  {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ r₁ r₂ : ℤ}

/-- Restrict the actual native sequence to an original later starting page. -/
def truncate (S : SpectralSequence C c r₀) (r₁ : ℤ) (h : r₀ ≤ r₁) : SpectralSequence C c r₁ where
  page r hr := S.page r (h.trans hr)
  iso r r' x hrr' hr := S.iso r r' x hrr' (h.trans hr)

/-- Every retained page is literally the original page complex. -/
theorem truncate_page (S : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (r : ℤ) (hr : r₁ ≤ r) :
    (S.truncate r₁ h).page r hr = S.page r (h.trans hr) := rfl

/-- Every retained page object is the original degree object. -/
theorem truncate_page_X (S : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (r : ℤ) (hr : r₁ ≤ r) (x : κ) :
    ((S.truncate r₁ h).page r hr).X x = (S.page r (h.trans hr)).X x := rfl

/-- Every retained differential is exactly the original differential. -/
theorem truncate_page_d (S : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (r : ℤ) (hr : r₁ ≤ r) (x y : κ) :
    ((S.truncate r₁ h).page r hr).d x y = (S.page r (h.trans hr)).d x y := rfl

/-- Successor homology identifications are the original native isomorphisms. -/
theorem truncate_iso (S : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (r r' : ℤ) (x : κ)
    (hrr' : r + 1 = r') (hr : r₁ ≤ r) :
    (S.truncate r₁ h).iso r r' x hrr' hr = S.iso r r' x hrr' (h.trans hr) := rfl

/-- Restrict an actual native morphism to the retained pages and successor squares. -/
def truncateMap {S T : SpectralSequence C c r₀} (α : S ⟶ T) (r₁ : ℤ) (h : r₀ ≤ r₁) :
    S.truncate r₁ h ⟶ T.truncate r₁ h where
  hom r hr := α.hom r (h.trans hr)
  comm r r' x hrr' hr := α.comm r r' x hrr' (h.trans hr)

/-- The restricted native morphism has the original complex map at every retained page. -/
theorem truncateMap_hom {S T : SpectralSequence C c r₀} (α : S ⟶ T) (h : r₀ ≤ r₁)
    (r : ℤ) (hr : r₁ ≤ r) :
    (truncateMap α r₁ h).hom r hr = α.hom r (h.trans hr) := rfl

/-- Retained degree components are the actual original native components. -/
theorem truncateMap_hom_f {S T : SpectralSequence C c r₀} (α : S ⟶ T) (h : r₀ ≤ r₁)
    (r : ℤ) (hr : r₁ ≤ r) (x : κ) :
    ((truncateMap α r₁ h).hom r hr).f x = (α.hom r (h.trans hr)).f x := rfl

/-- Restriction preserves native identities. -/
theorem truncateMap_id (S : SpectralSequence C c r₀) (h : r₀ ≤ r₁) :
    truncateMap (𝟙 S) r₁ h = 𝟙 (S.truncate r₁ h) := by
  apply hom_ext
  intro r hr
  rfl

/-- Restriction preserves native composition. -/
theorem truncateMap_comp {S T U : SpectralSequence C c r₀} (α : S ⟶ T) (β : T ⟶ U) (h : r₀ ≤ r₁) :
    truncateMap (α ≫ β) r₁ h = truncateMap α r₁ h ≫ truncateMap β r₁ h := by
  apply hom_ext
  intro r hr
  rfl

/-- Restricting to the original starting page retains the complete original sequence. -/
theorem truncate_refl (S : SpectralSequence C c r₀) : S.truncate r₀ (le_refl r₀) = S := rfl

/-- Successive restrictions retain the same original pages and successor isomorphisms. -/
theorem truncate_trans (S : SpectralSequence C c r₀) (h₀₁ : r₀ ≤ r₁) (h₁₂ : r₁ ≤ r₂) :
    (S.truncate r₁ h₀₁).truncate r₂ h₁₂ = S.truncate r₂ (h₀₁.trans h₁₂) := rfl

/-- Successively restricted maps retain exactly the original native morphism. -/
theorem truncateMap_trans {S T : SpectralSequence C c r₀} (α : S ⟶ T)
    (h₀₁ : r₀ ≤ r₁) (h₁₂ : r₁ ≤ r₂) :
    truncateMap (truncateMap α r₁ h₀₁) r₂ h₁₂ = truncateMap α r₂ (h₀₁.trans h₁₂) := by
  apply hom_ext
  intro r hr
  rfl

/-- Two restricted maps agree when their original native maps agree at every retained page. -/
theorem truncateMap_eq {S T : SpectralSequence C c r₀} (α β : S ⟶ T) (h : r₀ ≤ r₁)
    (heq : ∀ (r : ℤ) (hr : r₁ ≤ r), α.hom r (h.trans hr) = β.hom r (h.trans hr)) :
    truncateMap α r₁ h = truncateMap β r₁ h := by
  apply hom_ext
  intro r hr
  exact heq r hr

variable (C c)

/-- The genuine restriction functor on the native spectral sequence categories. -/
def truncationFunctor (r₀ r₁ : ℤ) (h : r₀ ≤ r₁) :
    SpectralSequence C c r₀ ⥤ SpectralSequence C c r₁ where
  obj S := S.truncate r₁ h
  map α := truncateMap α r₁ h
  map_id S := truncateMap_id S h
  map_comp α β := truncateMap_comp α β h

/-- The functor retains the actual restricted sequence as its object. -/
theorem truncationFunctor_obj (h : r₀ ≤ r₁) (S : SpectralSequence C c r₀) :
    (truncationFunctor C c r₀ r₁ h).obj S = S.truncate r₁ h := rfl

/-- The functor's retained page map is the original native morphism. -/
theorem truncationFunctor_map_hom (h : r₀ ≤ r₁) {S T : SpectralSequence C c r₀} (α : S ⟶ T)
    (r : ℤ) (hr : r₁ ≤ r) :
    ((truncationFunctor C c r₀ r₁ h).map α).hom r hr = α.hom r (h.trans hr) := rfl

/-- Restriction commutes strictly with evaluating any retained actual page. -/
theorem truncationFunctor_pageFunctor (h : r₀ ≤ r₁) (r : ℤ) (hr : r₁ ≤ r) :
    truncationFunctor C c r₀ r₁ h ⋙ pageFunctor C c r₁ r hr = pageFunctor C c r₀ r (h.trans hr) := rfl

/-- Restriction to the same starting page is the native identity functor. -/
theorem truncationFunctor_refl (r₀ : ℤ) : truncationFunctor C c r₀ r₀ (le_refl r₀) = 𝟭 _ := rfl

/-- Successive restriction functors compose to the actual direct restriction. -/
theorem truncationFunctor_trans (h₀₁ : r₀ ≤ r₁) (h₁₂ : r₁ ≤ r₂) :
    truncationFunctor C c r₀ r₁ h₀₁ ⋙ truncationFunctor C c r₁ r₂ h₁₂ =
      truncationFunctor C c r₀ r₂ (h₀₁.trans h₁₂) := rfl

end CategoryTheory.SpectralSequence

end
