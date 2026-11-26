/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LaurentSeriesBoundedPartialQuotientsFrobenius

open MetaMathlibExt

-- In odd characteristic, the index-zero convergent still has dummy values 1 and 0.
example (α : LaurentSeries (ZMod 3)) :
    laurentPartialQuotient (α ^ 3) 0 = laurentPartialQuotient α 0 ^ 3 ∧
      laurentConvNum (α ^ 3) 0 = 1 ∧ laurentConvDen (α ^ 3) 0 = 0 := by
  simpa [ZMod.card, laurentConvNum, laurentConvDen] using laurentPartialQuotient_pow_card α 0

-- The finite expansion [x; x] becomes [x²; x²], and the next partial quotient is zero.
example :
    let x := laurentInvVar (ZMod 2)
    let t := HahnSeries.single (1 : ℤ) (1 : ZMod 2)
    laurentPartialQuotient ((x + t) ^ 2) 2 = 0 ∧
      laurentConvNum ((x + t) ^ 2) 2 = (x * x + 1) ^ 2 ∧
      laurentConvDen ((x + t) ^ 2) 2 = x ^ 2 := by
  let x := laurentInvVar (ZMod 2)
  let t := HahnSeries.single (1 : ℤ) (1 : ZMod 2)
  obtain ⟨hx, ht⟩ := laurentPolyPart_laurentInvVar (K := ZMod 2)
  have hpart : laurentPolyPart (x + t) = x := by
    calc
      laurentPolyPart (x + t) = laurentPolyPart x + laurentPolyPart t := by
        ext i
        by_cases hi : i ≤ 0 <;> simp [laurentPolyPart_coeff, HahnSeries.coeff_add, hi]
      _ = x := by rw [hx, ht, add_zero]
  have h₁ : laurentCompleteQuotient (x + t) 1 = x := by
    change ((x + t) - laurentPolyPart (x + t))⁻¹ = x
    rw [hpart, add_sub_cancel_left]
    exact inv_eq_of_mul_eq_one_left (laurentInvVar_mul_single_one (K := ZMod 2))
  have h₂ : laurentPartialQuotient (x + t) 2 = 0 := by
    have h : laurentCompleteQuotient (x + t) 2 = 0 := by
      rw [laurentCompleteQuotient, h₁, hx, sub_self, inv_zero]
    rw [laurentPartialQuotient, h]
    ext i
    simp [laurentPolyPart_coeff]
  have hpart₀ : laurentPartialQuotient (x + t) 0 = x := hpart
  have hpart₁ : laurentPartialQuotient (x + t) 1 = x := by
    rw [laurentPartialQuotient, h₁, hx]
  obtain ⟨hnum, hden⟩ := laurentConv_two (x + t)
  simpa only [ZMod.card, h₂, hnum, hden, hpart₀, hpart₁, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    using laurentPartialQuotient_pow_card (x + t) 2
