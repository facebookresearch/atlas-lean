/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HigherANumbersPeriodicSum
import Mathlib.Tactic.Ring

open Finset MetaMathlibExt

-- Whole periods have no remainder, including the empty sum when q = 0.
example {K : Type*} [Field K] [CharZero K] (f : ℕ → K) {L : ℕ}
    (hL : 0 < L) (hf : ∀ i, 1 ≤ i → f (i + L) = f i) (q : ℕ) :
    ∑ i ∈ Icc 1 (q * L), f i = q * ∑ k ∈ Icc 1 L, f k := by
  have hL' : (L : K) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  rw [sum_Icc_of_periodic f hL hf]
  simp [Nat.cast_mul, mul_assoc, mul_div_cancel₀ _ hL']

-- Two full periods and a final copy of the first term, with no condition on f 0.
example (f : ℕ → ℚ) (hf : ∀ i, 1 ≤ i → f (i + 2) = f i) :
    ∑ i ∈ Icc 1 5, f i = 3 * f 1 + 2 * f 2 := by
  rw [sum_Icc_of_periodic f (by decide : 0 < 2) hf,
    show Icc 1 2 = {1, 2} from by decide, show 5 % 2 = 1 from rfl]
  simp
  ring
