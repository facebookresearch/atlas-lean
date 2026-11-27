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

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimitExactness

/-!
# Exact inverse-limit row clients

These clients retain the chosen-limit hypotheses and induced limit maps in
conditional exactness of short exact inverse-sequence rows.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Row

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D]

-- Forming the row itself needs neither an abelian category nor products.
example (S : ShortComplex (ℕᵒᵖ ⥤ D))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (sequentialLimitRow S).g = limMap S.g := rfl

end Row

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCountableProducts C]
  (S : ShortComplex (ℕᵒᵖ ⥤ C))
  [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃]

-- This does not require a global HasLimitsOfShape instance or AB4-star.
example (hS : S.ShortExact) (hPg : Epi (sequentialProductMap S.g))
    (h₁ : IsZero (sequentialLimOne S.X₁)) : Epi (limMap S.g) :=
  (sequentialLimitRow_shortExact_of_product_epi_of_isZero S hS hPg h₁).epi_g

example (hS : S.ShortExact) (hPg : Epi (sequentialProductMap S.g))
    (h₁ : IsZero (sequentialLimOne S.X₁)) : Mono (limMap S.f) :=
  (sequentialLimitRow_shortExact_of_product_epi_of_isZero S hS hPg h₁).mono_f

example (n : ℕ) :
    (sequentialLimitRow S).f ≫ limit.π S.X₂ (op n) =
      limit.π S.X₁ (op n) ≫ S.f.app (op n) := by
  simp

example (n : ℕ) :
    (sequentialLimitRow S).g ≫ limit.π S.X₃ (op n) =
      limit.π S.X₂ (op n) ≫ S.g.app (op n) := by
  simp

example [CountableAB4Star C] (hS : S.ShortExact)
    (h₁ : IsZero (sequentialLimOne S.X₁)) : (sequentialLimitRow S).ShortExact :=
  sequentialLimitRow_shortExact_of_isZero S hS h₁
