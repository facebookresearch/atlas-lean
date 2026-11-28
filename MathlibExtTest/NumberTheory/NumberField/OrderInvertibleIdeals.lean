/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.OrderInvertibleIdeals

@[expose] public section

open scoped nonZeroDivisors

/-! Tests for `MathlibExt.NumberTheory.NumberField.OrderInvertibleIdeals`. -/

-- The colon lemma in a Noetherian domain of dimension one: for `2ℤ ⊆ ℤ` some `x ∈ (2ℤ)⁻¹`
-- lies outside `ℤ`.
example : ∃ x ∈ ((Ideal.span {(2 : ℤ)} : Ideal ℤ) : FractionalIdeal ℤ⁰ ℚ)⁻¹,
    x ∉ (1 : FractionalIdeal ℤ⁰ ℚ) :=
  FractionalIdeal.exists_notMem_one_of_ne_bot_of_dimensionLEOne (by simp)
    (by rw [Ne, Ideal.span_singleton_eq_top]; decide)

-- In the order `ℤ` of `ℚ`, the proper ideal `2ℤ` has an element of `ℚ ∖ ℤ` multiplying it
-- into `ℤ`.
example : ∃ x : ℚ, x ∉ integralClosure ℤ ℚ ∧
    ∀ y ∈ Ideal.span {(2 : integralClosure ℤ ℚ)}, x * (y : ℚ) ∈ integralClosure ℤ ℚ := by
  refine (NumberField.isOrder_integralClosure ℚ).exists_notMem_mul_mem ?_ ?_
  · rw [Ne, Ideal.span_singleton_eq_bot]
    intro h
    have := congrArg Subtype.val h
    norm_num at this
  · rw [Ne, Ideal.span_singleton_eq_top]
    rintro ⟨u, hu⟩
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      ((u⁻¹ : (integralClosure ℤ ℚ)ˣ) : integralClosure ℤ ℚ).2
    have h1 : (2 : ℚ) * ((u⁻¹ : (integralClosure ℤ ℚ)ˣ) : integralClosure ℤ ℚ) = 1 := by
      have := congrArg Subtype.val (Units.mul_inv u)
      rw [hu] at this
      exact this
    rw [← hn, eq_intCast] at h1
    have h2 : (2 : ℤ) * n = 1 := by exact_mod_cast h1
    omega

-- Every nonzero prime of the maximal order `𝒪_K` is invertible, since its multiplier ring is
-- `𝒪_K` (the conductor of `𝒪_K` is the unit ideal).
example (K : Type*) [Field K] [NumberField K] (p : Ideal (integralClosure ℤ K)) [p.IsPrime]
    (hp : p ≠ ⊥) : IsUnit (p : FractionalIdeal (integralClosure ℤ K)⁰ K) := by
  have hO := NumberField.isOrder_integralClosure K
  have htop : (integralClosure ℤ K).comap (integralClosure ℤ K).val = ⊤ :=
    eq_top_iff.mpr fun t _ => t.2
  refine (hO.isUnit_coeIdeal_iff_setOf_mul_mem_eq hp).mpr (hO.setOf_mul_mem_eq hp ?_)
  rw [htop, Subalgebra.conductorIdeal_top, Ideal.comap_top, sup_top_eq]

-- Every nonzero ideal of `𝒪_K` is a product of invertible primes, and is invertible.
example (K : Type*) [Field K] [NumberField K] (b : Ideal (integralClosure ℤ K)) (hb : b ≠ ⊥) :
    IsUnit (b : FractionalIdeal (integralClosure ℤ K)⁰ K) := by
  have hO := NumberField.isOrder_integralClosure K
  have htop : (integralClosure ℤ K).comap (integralClosure ℤ K).val = ⊤ :=
    eq_top_iff.mpr fun t _ => t.2
  refine (hO.prod_and_isUnit_of_sup_conductor_eq_top hb ?_).2
  rw [htop, Subalgebra.conductorIdeal_top, Ideal.comap_top, sup_top_eq]

-- An order is a Noetherian ring of dimension at most one.
example (K : Type*) [Field K] [NumberField K] :
    IsNoetherianRing (integralClosure ℤ K) ∧ Ring.DimensionLEOne (integralClosure ℤ K) :=
  ⟨(NumberField.isOrder_integralClosure K).isNoetherianRing,
    (NumberField.isOrder_integralClosure K).dimensionLEOne⟩

end
