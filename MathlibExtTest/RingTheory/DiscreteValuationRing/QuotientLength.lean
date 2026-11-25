/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.QuotientLength

@[expose] public section

-- exactSource consumer, with the original binders.
example {D L : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [CommRing L] [IsDomain L] [IsLocalRing L]
    (φ : D →+* L) (hφ0 : Function.Injective φ) (f : D) (hf : f ≠ 0) :
    Module.length L (L ⧸ Ideal.span {φ f}) =
      Module.length D (D ⧸ Ideal.span {f}) *
        Module.length L (L ⧸ Ideal.map φ (IsLocalRing.maximalIdeal D)) :=
  IsDiscreteValuationRing.length_quotient_map_span_eq_length_mul_length φ hφ0 f hf

example :
    ∀ {D L : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
      [CommRing L] [IsDomain L] [IsLocalRing L]
      (φ : D →+* L), Function.Injective φ → ∀ (f : D), f ≠ 0 →
      Module.length L (L ⧸ Ideal.span {φ f}) =
        Module.length D (D ⧸ Ideal.span {f}) *
          Module.length L (L ⧸ Ideal.map φ (IsLocalRing.maximalIdeal D)) :=
  fun φ hφ f hf =>
    IsDiscreteValuationRing.length_quotient_map_span_eq_length_mul_length φ hφ f hf

-- Boundary: a unit `f` makes both quotient lengths vanish, so the
-- factorisation gives `0` regardless of the ramification factor.
example {D L : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [CommRing L] [IsDomain L] [IsLocalRing L]
    (φ : D →+* L) (hφ0 : Function.Injective φ) (f : D) (hf : f ≠ 0)
    (hu : IsUnit f) :
    Module.length L (L ⧸ Ideal.span {φ f}) = 0 := by
  rw [IsDiscreteValuationRing.length_quotient_map_span_eq_length_mul_length
    φ hφ0 f hf]
  have h0 : Module.length D (D ⧸ Ideal.span {f}) = 0 := by
    rw [Ideal.span_singleton_eq_top.mpr hu]
    simp
  rw [h0, zero_mul]
