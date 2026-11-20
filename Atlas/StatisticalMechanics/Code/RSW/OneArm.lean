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

namespace OneArm











noncomputable def roa_eps (c : ℝ) : ℝ := -Real.log (1 - c) / Real.log 2



theorem roa_eps_pos {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : 0 < roa_eps c := by
  unfold roa_eps
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have h1c1 : 1 - c < 1 := by linarith
  exact div_pos (by linarith [Real.log_neg h1c h1c1]) h2


theorem roa_one_sub_c_eq {c : ℝ} (_hc0 : 0 < c) (hc1 : c < 1) :
    (1 - c) = (2 : ℝ) ^ (-(roa_eps c)) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1c : (0 : ℝ) < 1 - c := by linarith
  rw [show (-(roa_eps c) : ℝ) = Real.log (1 - c) / Real.log 2 by
        unfold roa_eps; ring]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [show Real.log 2 * (Real.log (1 - c) / Real.log 2) = Real.log (1 - c) by
        field_simp]
  exact (Real.exp_log h1c).symm








theorem roa_geometricLog_polynomial (a : ℕ → ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hann : ∀ n, 1 ≤ n → a n ≤ (1 - c) ^ (Nat.log 2 n)) :
    ∀ n, 1 ≤ n → a n ≤ (2 : ℝ) ^ (roa_eps c) * (n : ℝ) ^ (-(roa_eps c)) := by
  set ε : ℝ := roa_eps c with hε
  have hεpos : 0 < ε := roa_eps_pos hc0 hc1
  have hbase : (1 - c) = (2 : ℝ) ^ (-ε) := roa_one_sub_c_eq hc0 hc1
  intro n hn
  set m := Nat.log 2 n with hm
  
  have hstep1 : a n ≤ (1 - c) ^ m := hann n hn
  
  have hpoweq : (1 - c) ^ m = ((2 : ℝ) ^ m) ^ (-ε) := by
    rw [hbase, ← Real.rpow_natCast ((2 : ℝ) ^ (-ε)) m,
        ← Real.rpow_natCast (2 : ℝ) m,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  
  have hlt : (n : ℝ) < 2 * (2 : ℝ) ^ m := by
    have hN := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    rw [← hm] at hN
    have hNr : (n : ℝ) < (2 : ℝ) ^ (m + 1) := by exact_mod_cast hN
    calc (n : ℝ) < (2 : ℝ) ^ (m + 1) := hNr
      _ = 2 * (2 : ℝ) ^ m := by ring
  have hnhalf : (n : ℝ) / 2 < (2 : ℝ) ^ m := by linarith
  have hnhalf_pos : (0 : ℝ) < (n : ℝ) / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  
  have hmono : ((2 : ℝ) ^ m) ^ (-ε) ≤ ((n : ℝ) / 2) ^ (-ε) :=
    Real.rpow_le_rpow_of_nonpos hnhalf_pos hnhalf.le (by linarith)
  
  have hrw : ((n : ℝ) / 2) ^ (-ε) = (2 : ℝ) ^ ε * (n : ℝ) ^ (-ε) := by
    rw [Real.div_rpow (by positivity) (by norm_num),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_eq_mul_inv, inv_inv]
    ring
  calc a n ≤ (1 - c) ^ m := hstep1
    _ = ((2 : ℝ) ^ m) ^ (-ε) := hpoweq
    _ ≤ ((n : ℝ) / 2) ^ (-ε) := hmono
    _ = (2 : ℝ) ^ ε * (n : ℝ) ^ (-ε) := hrw















theorem roa_one_arm_polynomial (a : ℕ → ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hann : ∀ n, 1 ≤ n → a n ≤ (1 - c) ^ (Nat.log 2 n)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ n, 1 ≤ n → a n ≤ C * (n : ℝ) ^ (-ε) :=
  ⟨roa_eps c, roa_eps_pos hc0 hc1, (2 : ℝ) ^ (roa_eps c), by positivity,
    roa_geometricLog_polynomial a hc0 hc1 hann⟩











theorem roa_polynomial_tendsto_zero {ε C : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-ε)) Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-ε)) Filter.atTop (nhds 0) := by
    have := tendsto_rpow_neg_atTop hε
    exact this.comp tendsto_natCast_atTop_atTop
  have := hbase.const_mul C
  simpa using this






theorem roa_one_arm_tendsto_zero (a : ℕ → ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hnn : ∀ n, 0 ≤ a n)
    (hann : ∀ n, 1 ≤ n → a n ≤ (1 - c) ^ (Nat.log 2 n)) :
    Filter.Tendsto a Filter.atTop (nhds 0) := by
  obtain ⟨ε, hε, C, _hC, hbound⟩ := roa_one_arm_polynomial a hc0 hc1 hann
  
  refine squeeze_zero' (Filter.Eventually.of_forall hnn) ?_
    (roa_polynomial_tendsto_zero (C := C) hε)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact hbound n hn

end OneArm

end RSW

end StatMech
