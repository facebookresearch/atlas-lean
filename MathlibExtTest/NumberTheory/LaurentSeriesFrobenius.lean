/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LaurentSeriesFrobenius

open MetaMathlibExt

variable {K : Type*} [Field K] [Fintype K]

-- The reciprocal variable `x⁻¹` has expansion `[0; x]`, so `x^(-q)` has expansion `[0; x^q]`:
-- its first partial quotient vanishes and its first nontrivial convergent is `1 / x^q`.
example :
    let t := HahnSeries.single (1 : ℤ) (1 : K)
    laurentPartialQuotient (t ^ Fintype.card K) 0 = 0 ∧
      laurentConvNum (t ^ Fintype.card K) 2 = 1 ∧
      laurentConvDen (t ^ Fintype.card K) 2 = laurentInvVar K ^ Fintype.card K := by
  intro t
  have ⟨hx, ht⟩ := laurentPolyPart_laurentInvVar (K := K)
  have hinv := inv_eq_of_mul_eq_one_left (laurentInvVar_mul_single_one (K := K))
  have hb : laurentPartialQuotient t 0 = 0 ∧ laurentPartialQuotient t 1 = laurentInvVar K := by
    simp [t, laurentPartialQuotient, laurentCompleteQuotient, ht, hinv, hx]
  refine ⟨?_, ?_, ?_⟩
  · rw [(laurentPartialQuotient_pow_card t 0).1, hb.1, zero_pow Fintype.card_ne_zero]
  · rw [(laurentPartialQuotient_pow_card t 2).2.1, (laurentConv_two t).1, hb.1, mul_zero,
      zero_add, one_pow]
  · rw [(laurentPartialQuotient_pow_card t 2).2.2, (laurentConv_two t).2, hb.2]

-- Applying the theorem twice gives the partial quotients of `α ^ (q ^ 2)`.
example (α : LaurentSeries K) (n : ℕ) :
    laurentPartialQuotient (α ^ (Fintype.card K ^ 2)) n =
      laurentPartialQuotient α n ^ (Fintype.card K ^ 2) := by
  rw [sq, pow_mul, pow_mul, (laurentPartialQuotient_pow_card _ n).1,
    (laurentPartialQuotient_pow_card α n).1]

-- Over `𝔽₂` the theorem is about squaring.
example (α : LaurentSeries (ZMod 2)) (n : ℕ) :
    laurentPartialQuotient (α ^ 2) n = laurentPartialQuotient α n ^ 2 ∧
      laurentConvNum (α ^ 2) n = laurentConvNum α n ^ 2 ∧
      laurentConvDen (α ^ 2) n = laurentConvDen α n ^ 2 := by
  simpa only [ZMod.card] using laurentPartialQuotient_pow_card α n
