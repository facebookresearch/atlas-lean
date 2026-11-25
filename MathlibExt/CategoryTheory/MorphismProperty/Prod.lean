/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Generic product closure for morphism properties

For independent categories, `MorphismProperty.prod W₁ W₂` is multiplicative when both
components are, and respects isomorphisms when both components do. Component isomorphism
evidence reuses the canonical `CategoryTheory.isIso_prod_iff` from the already imported
`Products.Basic`.

This file provides no Waldhausen structure, stage, nerve, realization, or K-theory claim.
-/

@[expose] public section

namespace CategoryTheory
namespace MorphismProperty

universe v₁ v₂ u₁ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]

/-- Product of multiplicative morphism properties is multiplicative. -/
instance Prod.isMultiplicative (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [W₁.IsMultiplicative] [W₂.IsMultiplicative] :
    (prod W₁ W₂).IsMultiplicative where
  id_mem _ := ⟨id_mem _ _, id_mem _ _⟩
  comp_mem _ _ hf hg :=
    ⟨comp_mem _ _ _ hf.1 hg.1, comp_mem _ _ _ hf.2 hg.2⟩

/-- Product of iso-respecting morphism properties respects isomorphisms. -/
instance Prod.respectsIso (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [W₁.RespectsIso] [W₂.RespectsIso] : (prod W₁ W₂).RespectsIso :=
  RespectsIso.mk _
    (fun {X Y Z} e f hf => by
      have h1 : IsIso e.hom.1 := ((isIso_prod_iff (f := e.hom)).mp inferInstance).1
      have h2 : IsIso e.hom.2 := ((isIso_prod_iff (f := e.hom)).mp inferInstance).2
      exact ⟨RespectsIso.precomp _ e.hom.1 f.1 hf.1,
        RespectsIso.precomp _ e.hom.2 f.2 hf.2⟩)
    (fun {X Y Z} e f hf => by
      have h1 : IsIso e.hom.1 := ((isIso_prod_iff (f := e.hom)).mp inferInstance).1
      have h2 : IsIso e.hom.2 := ((isIso_prod_iff (f := e.hom)).mp inferInstance).2
      exact ⟨RespectsIso.postcomp _ e.hom.1 f.1 hf.1,
        RespectsIso.postcomp _ e.hom.2 f.2 hf.2⟩)

end MorphismProperty
end CategoryTheory
