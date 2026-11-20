/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Mathlib

open Real

namespace StatMech

namespace RSW

namespace Renorm







theorem rrn_renorm_iterate (b : ℕ → ℝ) (hnn : ∀ k, 0 ≤ b k)
    (hsq : ∀ k, b (k + 1) ≤ (b k) ^ 2) :
    ∀ k, b k ≤ (b 0) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc b (k + 1) ≤ (b k) ^ 2 := hsq k
      _ ≤ ((b 0) ^ (2 ^ k)) ^ 2 := pow_le_pow_left₀ (hnn k) ih 2
      _ = (b 0) ^ (2 ^ (k + 1)) := by rw [← pow_mul]; ring_nf








theorem rrn_super_exp_decay (b : ℕ → ℝ) {b₀ : ℝ} (hb0pos : 0 < b₀) (hb0 : b₀ < 1)
    (hgeom : ∀ k, b k ≤ b₀ ^ (2 ^ k)) :
    ∃ c : ℝ, 0 < c ∧ ∀ k, b k ≤ Real.exp (-c * (2 ^ k : ℕ)) := by
  have hcpos : 0 < -Real.log b₀ := by
    have := Real.log_neg hb0pos hb0; linarith
  refine ⟨-Real.log b₀, hcpos, fun k => ?_⟩
  refine (hgeom k).trans ?_
  rw [show b₀ ^ (2 ^ k) = Real.exp (Real.log (b₀ ^ (2 ^ k))) from
        (Real.exp_log (by positivity)).symm]
  apply Real.exp_le_exp.2
  rw [Real.log_pow]
  push_cast
  ring_nf
  rw [mul_comm]














theorem rrn_renorm_super_exp (b : ℕ → ℝ) (hnn : ∀ k, 0 ≤ b k)
    (hb0pos : 0 < b 0) (hb0 : b 0 < 1)
    (hsq : ∀ k, b (k + 1) ≤ (b k) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ k, b k ≤ Real.exp (-c * (2 ^ k : ℕ)) :=
  rrn_super_exp_decay b hb0pos hb0 (rrn_renorm_iterate b hnn hsq)














theorem rrn_subunit_seed_of_not_bddBelow {u : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hnn : ∀ n, 0 ≤ u n) {n₀ : ℕ} (hsmall : u n₀ < 1 / C) :
    0 ≤ C * u n₀ ∧ C * u n₀ < 1 := by
  refine ⟨mul_nonneg hC.le (hnn n₀), ?_⟩
  have : C * u n₀ < C * (1 / C) := mul_lt_mul_of_pos_left hsmall hC
  rwa [mul_one_div, div_self hC.ne'] at this

end Renorm

end RSW

end StatMech
