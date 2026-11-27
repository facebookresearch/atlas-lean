/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimOneExact

/-!
# Exactness of inverse-limit rows

A short exact row of inverse sequences gives a short exact row of its chosen
limits when the product of the final map is epimorphic and the first concrete
sequential lim¹ object vanishes. The limit-row maps are the induced limit maps.
Countable exact products supply the product epimorphism in the uniform form.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite

universe u v

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section Row

variable [HasZeroMorphisms C]

/-- The short complex formed by the chosen limits of a row of towers. -/
abbrev sequentialLimitRow (S : ShortComplex (ℕᵒᵖ ⥤ C))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] : ShortComplex C where
  X₁ := limit S.X₁
  X₂ := limit S.X₂
  X₃ := limit S.X₃
  f := limMap S.f
  g := limMap S.g
  zero := by
    apply limit.hom_ext
    intro j
    rw [Category.assoc, limMap_π, ← Category.assoc, limMap_π, Category.assoc]
    have h := NatTrans.congr_app S.zero j
    change S.f.app j ≫ S.g.app j = 0 at h
    rw [h, comp_zero, zero_comp]

/-- The first map of the chosen-limit row is the limit map. -/
@[simp]
theorem sequentialLimitRow_f (S : ShortComplex (ℕᵒᵖ ⥤ C))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (sequentialLimitRow S).f = limMap S.f := rfl

/-- The last map of the chosen-limit row is the limit map. -/
@[simp]
theorem sequentialLimitRow_g (S : ShortComplex (ℕᵒᵖ ⥤ C))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (sequentialLimitRow S).g = limMap S.g := rfl

end Row

section Abelian

variable [Abelian C] [HasCountableProducts C]

/-- Vanishing of the first concrete sequential `lim¹` makes the limit row short exact under the
minimal explicit product-epi hypothesis. -/
theorem sequentialLimitRow_shortExact_of_product_epi_of_isZero
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃]
    (h₁ : IsZero (sequentialLimOne S.X₁)) :
    (sequentialLimitRow S).ShortExact := by
  let E := sequentialLimOneExactSequenceOfProductEpi S hS hPg
  have hE : E.Exact := sequentialLimOneExactSequenceOfProductEpi_exact S hS hPg
  have hExact : (sequentialLimitRow S).Exact := by
    have h := hE.exact' 0 1 2
    change (sequentialLimitRow S).Exact at h
    exact h
  have hepi : Epi (limMap S.g) := by
    let T := E.sc' hE.toIsComplex 1 2 3
    have hT : T.Exact := hE.exact' 1 2 3
    have hz : T.g = 0 := by
      change sequentialLimOneConnectingOfProductEpi S hS hPg = 0
      exact h₁.eq_of_tgt _ _
    have h := (T.exact_iff_epi hz).mp hT
    change Epi (limMap S.g) at h
    exact h
  exact ShortComplex.ShortExact.mk' hExact
    (mono_limMap_f_of_product_epi S hS hPg) hepi

/-- Under countable AB4-star, vanishing of the first concrete sequential `lim¹` makes the
chosen-limit row short exact. -/
theorem sequentialLimitRow_shortExact_of_isZero [CountableAB4Star C]
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃]
    (h₁ : IsZero (sequentialLimOne S.X₁)) :
    (sequentialLimitRow S).ShortExact := by
  have : Epi S.g := hS.epi_g
  exact sequentialLimitRow_shortExact_of_product_epi_of_isZero S hS
    (epi_sequentialProductMap_of_countableAB4Star S.g) h₁

end Abelian

end CategoryTheory.Limits
