/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LaurentSeriesBoundedPartialQuotients

open MetaMathlibExt Polynomial

variable {K : Type*} [Field K]

-- The finite continued fraction of the reciprocal variable is [0; x].
example :
    let t := HahnSeries.single (1 : ℤ) (1 : K)
    laurentPartialQuotient t 0 = 0 ∧ laurentConvNum t 2 = 1 ∧
      laurentConvDen t 2 = laurentInvVar K ∧ laurentCompleteQuotient t 2 = 0 := by
  have ⟨hx, ht⟩ := laurentPolyPart_laurentInvVar (K := K)
  have hinv := inv_eq_of_mul_eq_one_left (laurentInvVar_mul_single_one (K := K))
  simp [laurentPartialQuotient, laurentCompleteQuotient, laurentConvNum, laurentConvDen,
    ht, hinv, hx]

-- The affine case C = 0 allows P/Q = 0/1. The two differences are translations by 1/x.
example [Fintype K] (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (laurentInvVar K * α ^ Fintype.card K + 1) / laurentInvVar K) :
    α ^ Fintype.card K + (laurentInvVar K)⁻¹ = α ∧
      α - (laurentInvVar K)⁻¹ = α ^ Fintype.card K := by
  have hx : laurentInvVar K ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  have h := laurentMobius_sub_identities X 1 0 X (by simp) α hα
    (by simpa [polyToLaurentInv] using hfix) 0 1 one_ne_zero (by simp) (by simp)
  simpa [polyToLaurentInv, Fintype.card_ne_zero, hx, mul_comm, neg_div] using h
