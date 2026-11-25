/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TotientWeightedDivisorSum

/-! # Tests for the totient-weighted divisor sum identity -/

open MetaMathlibExt

-- With `f` the indicator of `1`, `g` is `1` on positive integers (its value `37` at `0` plays no
-- role), and the identity becomes Gauss's `∑ d ∣ k, φ (k / d) = k`.
example (k : ℕ) (hk : 0 < k) : (k : ℚ) = ∑ d ∈ k.divisors, (Nat.totient (k / d) : ℚ) := by
  have h := sum_div_mul_eq_sum_totient_mul (fun d => if d = 1 then 1 else 0)
    (fun n => if n = 0 then 37 else 1) (fun n hn => by simp [hn.ne']) k hk
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Nat.one_mem_divisors, ne_eq,
    hk.ne', not_false_eq_true, ite_true, Nat.div_one] at h
  rw [h]
  exact Finset.sum_congr rfl fun d hd => by simp [(Nat.pos_of_mem_divisors hd).ne']

-- With `f d = d`, `g` is the sum of divisors `σ`, and the identity reads
-- `τ(k) k = ∑ d ∣ k, φ (k / d) σ(d)`, where `τ(k)` is the number of divisors of `k`.
example (k : ℕ) (hk : 0 < k) :
    (k.divisors.card * k : ℚ) =
      ∑ d ∈ k.divisors, (Nat.totient (k / d) : ℚ) * ∑ e ∈ d.divisors, (e : ℚ) := by
  rw [← sum_div_mul_eq_sum_totient_mul (fun d => (d : ℚ)) (fun n => ∑ e ∈ n.divisors, (e : ℚ))
    (fun _ _ => rfl) k hk, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.cast_one, one_mul, ← Nat.cast_mul, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]

-- The previous identity at `k = 6`: `4 * 6 = 2 * 1 + 2 * 3 + 1 * 4 + 1 * 12`.
example : ∑ d ∈ (6 : ℕ).divisors, (Nat.totient (6 / d) : ℚ) * ∑ e ∈ d.divisors, (e : ℚ) = 24 := by
  rw [← sum_div_mul_eq_sum_totient_mul (fun d => (d : ℚ)) (fun n => ∑ e ∈ n.divisors, (e : ℚ))
    (fun _ _ => rfl) 6 (by norm_num)]
  exact_mod_cast (by decide : ∑ d ∈ (6 : ℕ).divisors, 6 / d * d = 24)
