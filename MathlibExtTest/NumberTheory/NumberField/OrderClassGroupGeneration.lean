/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.OrderClassGroupGeneration

@[expose] public section

/-! Tests for `MathlibExt.NumberTheory.NumberField.OrderClassGroupGeneration`. -/

open scoped nonZeroDivisors

#check @NumberField.IsOrder.exists_eq_spanSingleton_mul_of_ne_bot
#check @NumberField.IsOrder.natCard_quotient_eq_or_eq_span_of_finrank_eq_two
#check @NumberField.IsOrder.exists_eq_spanSingleton_mul_prod_of_finrank_eq_two
#check @NumberField.IsOrder.closure_classGroup_mk_eq_top

-- Every class of an order is the class of an invertible integral ideal coprime to `n`.
example {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K} [IsFractionRing O K]
    (hO : NumberField.IsOrder K O) {n : Ideal O} (hn : n ≠ ⊥) (C : ClassGroup O) :
    ∃ b : Ideal O, b ⊔ n = ⊤ ∧
      ∃ hb : IsUnit (b : FractionalIdeal O⁰ K), ClassGroup.mk K hb.unit = C := by
  refine ClassGroup.induction K (fun u => ?_) C
  obtain ⟨b, x, hx, hbn, hu⟩ := hO.exists_eq_spanSingleton_mul_of_ne_bot u hn
  have hxu : IsUnit (FractionalIdeal.spanSingleton O⁰ x) :=
    IsUnit.of_mul_eq_one (FractionalIdeal.spanSingleton O⁰ x⁻¹)
      (by rw [← map_mul, mul_inv_cancel₀ hx, map_one])
  have hbu : IsUnit (b : FractionalIdeal O⁰ K) := by
    have := u.isUnit
    rw [hu] at this
    exact isUnit_of_mul_isUnit_right this
  refine ⟨b, hbn, hbu, ?_⟩
  have hux : u = hxu.unit * hbu.unit := Units.ext (by
    rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hu])
  have hx1 : ClassGroup.mk K hxu.unit = 1 := by
    rw [ClassGroup.mk_eq_one_iff, IsUnit.unit_spec,
      FractionalIdeal.coeToSubmodule_spanSingleton]
    exact ⟨x, rfl⟩
  rw [hux, map_mul, hx1, one_mul]

-- If every invertible prime of prime norm of a quadratic order is principal, its class group
-- is trivial.
example {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K} [IsFractionRing O K]
    (hO : NumberField.IsOrder K O) (hK : Module.finrank ℚ K = 2)
    (h : ∀ (u : (FractionalIdeal O⁰ K)ˣ) (p : Ideal O), p.IsPrime →
      (u : FractionalIdeal O⁰ K) = p → (Nat.card (O ⧸ p)).Prime → ClassGroup.mk K u = 1)
    (C : ClassGroup O) : C = 1 := by
  have h1 := (hO.closure_classGroup_mk_eq_top hK (M := 1) one_pos).1
  have hC : C ∈ Submonoid.closure {C : ClassGroup O | ∃ (p : Ideal O)
      (u : (FractionalIdeal O⁰ K)ˣ), p.IsPrime ∧ (u : FractionalIdeal O⁰ K) = p ∧
        (Nat.card (O ⧸ p)).Prime ∧ ¬ Nat.card (O ⧸ p) ∣ 1 ∧ ClassGroup.mk K u = C} := by
    rw [h1]
    exact Submonoid.mem_top C
  have hle : Submonoid.closure {C : ClassGroup O | ∃ (p : Ideal O)
      (u : (FractionalIdeal O⁰ K)ˣ), p.IsPrime ∧ (u : FractionalIdeal O⁰ K) = p ∧
        (Nat.card (O ⧸ p)).Prime ∧ ¬ Nat.card (O ⧸ p) ∣ 1 ∧ ClassGroup.mk K u = C} ≤ ⊥ := by
    rw [Submonoid.closure_le]
    rintro _ ⟨p, u, hp, hu, hpr, -, rfl⟩
    exact h u p hp hu hpr
  exact hle hC

end
