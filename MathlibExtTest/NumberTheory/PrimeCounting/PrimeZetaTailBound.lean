/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.PrimeZetaTailBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Tests for the uniform tail bound for the prime zeta series
-/

open Real

namespace MetaMathlibExt

-- At the endpoint `α = 1` the threshold is `e`, so the bound is about `∑ p⁻²` over the primes
-- `p ≥ 3`.
example : ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ 0.9235 := by
  have hiff (p : ℕ) : (p.Prime ∧ exp (1 / 1) < p) ↔ (p.Prime ∧ 3 ≤ p) := by
    rw [div_one]
    refine and_congr_right fun _ => ⟨fun hp => ?_, fun hp => ?_⟩
    · by_contra h3
      have : (p : ℝ) ≤ 2 := by exact_mod_cast (by omega : p ≤ 2)
      linarith [exp_one_gt_d9]
    · have : (3 : ℝ) ≤ p := by exact_mod_cast hp
      linarith [exp_one_lt_d9]
  rw [← (Equiv.subtypeEquivRight hiff).tsum_eq]
  convert tsum_rpow_neg_primes_gt_exp_inv_le (α := 1) one_pos le_rfl using 3
  norm_num

-- An interior exponent: for `α = 1 / 2` the threshold is `e ^ 2`.
example : ∑' p : {p : ℕ // p.Prime ∧ exp 2 < p}, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) ≤ 0.9235 := by
  have h := tsum_rpow_neg_primes_gt_exp_inv_le (α := 1 / 2) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num, show -(1 + 1 / 2 : ℝ) = -(3 / 2) by norm_num] at h
  exact h

-- The bound controls the finite sums too: at `α = 1`, `3⁻² + 5⁻² ≤ 0.9235`.
example : (3 : ℝ) ^ (-(1 + 1) : ℝ) + 5 ^ (-(1 + 1) : ℝ) ≤ 0.9235 := by
  have hs : Summable fun p : {p : ℕ // p.Prime ∧ exp (1 / 1) < p} =>
      ((p : ℕ) : ℝ) ^ (-(1 + 1) : ℝ) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).comp_injective Subtype.val_injective
  have he : exp 1 < 3 := by linarith [exp_one_lt_d9]
  let p₃ : {p : ℕ // p.Prime ∧ exp (1 / 1) < p} :=
    ⟨3, Nat.prime_three, by rw [div_one, Nat.cast_ofNat]; exact he⟩
  let p₅ : {p : ℕ // p.Prime ∧ exp (1 / 1) < p} :=
    ⟨5, Nat.prime_five, by rw [div_one, Nat.cast_ofNat]; linarith⟩
  have hne : p₃ ∉ ({p₅} : Finset _) := by simp [p₃, p₅]
  have h := hs.sum_le_tsum {p₃, p₅} (fun _ _ => rpow_nonneg (Nat.cast_nonneg _) _)
  rw [Finset.sum_insert hne, Finset.sum_singleton] at h
  exact h.trans (tsum_rpow_neg_primes_gt_exp_inv_le one_pos le_rfl)

end MetaMathlibExt
