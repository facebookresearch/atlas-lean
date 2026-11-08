/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.FasterAPSP.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Theta

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Selected-event complexity of FASTER-APSP

This theorem bounds the actual returned three-coordinate count. It does not
include a machine, bit, representation or allocation cost model.
-/

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.Matrix

private lemma clog_log_bounds {n : Nat} (hn : 4 ≤ n) :
    Real.log (n : ℝ) ≤ 2 * (Nat.clog 2 (n - 1) : ℝ) * Real.log 2 ∧
      (Nat.clog 2 (n - 1) : ℝ) * Real.log 2 ≤ 2 * Real.log (n : ℝ) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hcast : ((n - 1 : Nat) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hpred : 0 < ((n - 1 : Nat) : ℝ) := by rw [hcast]; linarith
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogPred : 0 ≤ Real.log ((n - 1 : Nat) : ℝ) :=
    Real.log_nonneg (by rw [hcast]; linarith)
  have hceilEq : ⌈Real.logb 2 ((n - 1 : Nat) : ℝ)⌉₊ = Nat.clog 2 (n - 1) := by
    simpa using Real.natCeil_logb_natCast 2 (n - 1)
  have hceil := Nat.le_ceil (Real.logb 2 ((n - 1 : Nat) : ℝ))
  rw [hceilEq] at hceil
  change Real.log ((n - 1 : Nat) : ℝ) / Real.log 2 ≤
    (Nat.clog 2 (n - 1) : ℝ) at hceil
  have hqLower := (div_le_iff₀ htwo).mp hceil
  have hceilUpper := Nat.ceil_lt_add_one
    (div_nonneg hlogPred htwo.le)
  change ((⌈Real.logb 2 ((n - 1 : Nat) : ℝ)⌉₊ : Nat) : ℝ) <
    Real.logb 2 ((n - 1 : Nat) : ℝ) + 1 at hceilUpper
  rw [hceilEq] at hceilUpper
  change (Nat.clog 2 (n - 1) : ℝ) <
    Real.log ((n - 1 : Nat) : ℝ) / Real.log 2 + 1 at hceilUpper
  have hqUpper := mul_le_mul_of_nonneg_right hceilUpper.le htwo.le
  rw [add_mul, div_mul_cancel₀ _ htwo.ne', one_mul] at hqUpper
  have htwoPred : Real.log 2 ≤ Real.log ((n - 1 : Nat) : ℝ) :=
    Real.log_le_log (by norm_num) (by rw [hcast]; linarith)
  have hpredN : Real.log ((n - 1 : Nat) : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hpred (by rw [hcast]; linarith)
  have hnDouble : (n : ℝ) ≤ 2 * ((n - 1 : Nat) : ℝ) := by
    rw [hcast]
    linarith
  have hlogDouble := Real.log_le_log (by linarith : (0 : ℝ) < n) hnDouble
  rw [Real.log_mul (by norm_num) hpred.ne'] at hlogDouble
  constructor
  · nlinarith
  · nlinarith

private lemma polynomial_log_bounds {n : Nat} (hn : 4 ≤ n) :
    (n : ℝ) ^ 3 * Real.log (n : ℝ) ≤ Real.log 2 *
      ((n : ℝ) ^ 2 + 2 * (Nat.clog 2 (n - 1) : ℝ) * (n : ℝ) ^ 2 +
        2 * (Nat.clog 2 (n - 1) : ℝ) * (n : ℝ) ^ 3) ∧
    Real.log 2 *
      ((n : ℝ) ^ 2 + 2 * (Nat.clog 2 (n - 1) : ℝ) * (n : ℝ) ^ 2 +
        2 * (Nat.clog 2 (n - 1) : ℝ) * (n : ℝ) ^ 3) ≤
      10 * (n : ℝ) ^ 3 * Real.log (n : ℝ) := by
  let N : ℝ := n
  let q : ℝ := Nat.clog 2 (n - 1)
  have hN : (4 : ℝ) ≤ N := by
    change (4 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hqNat : 1 ≤ Nat.clog 2 (n - 1) := by
    have hqPos : 0 < Nat.clog 2 (n - 1) :=
      (Nat.lt_clog_iff_pow_lt (by decide)).2 (by simp; omega)
    omega
  have hq : (1 : ℝ) ≤ q := by
    change (1 : ℝ) ≤ (Nat.clog 2 (n - 1) : ℝ)
    exact_mod_cast hqNat
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hN2 : (0 : ℝ) ≤ N ^ 2 := sq_nonneg N
  have hN3 : (0 : ℝ) ≤ N ^ 3 := pow_nonneg hN0 3
  have h23 : N ^ 2 ≤ N ^ 3 := by
    nlinarith [mul_nonneg hN2 (show (0 : ℝ) ≤ N - 1 by linarith)]
  have hq23 := mul_le_mul_of_nonneg_right h23 hq0
  have h3q := mul_le_mul_of_nonneg_right hq hN3
  have hLow : 2 * q * N ^ 3 ≤ N ^ 2 + 2 * q * N ^ 2 + 2 * q * N ^ 3 := by
    nlinarith [mul_nonneg hq0 hN2]
  have hHigh : N ^ 2 + 2 * q * N ^ 2 + 2 * q * N ^ 3 ≤ 5 * q * N ^ 3 := by
    nlinarith
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hbounds := clog_log_bounds hn
  change Real.log N ≤ 2 * q * Real.log 2 ∧ q * Real.log 2 ≤ 2 * Real.log N
    at hbounds
  have hlogLow := mul_le_mul_of_nonneg_right hbounds.1 hN3
  have hlogHigh := mul_le_mul_of_nonneg_right hbounds.2 hN3
  have hcountLow := mul_le_mul_of_nonneg_right hLow htwo.le
  have hcountHigh := mul_le_mul_of_nonneg_right hHigh htwo.le
  change N ^ 3 * Real.log N ≤ Real.log 2 * (N ^ 2 + 2 * q * N ^ 2 + 2 * q * N ^ 3) ∧
    Real.log 2 * (N ^ 2 + 2 * q * N ^ 2 + 2 * q * N ^ 3) ≤ 10 * N ^ 3 * Real.log N
  constructor
  · nlinarith
  · nlinarith

private lemma polynomial_nonneg (n : Nat) :
    0 ≤ (n : ℝ) ^ 2 + 2 * (Nat.clog 2 (n - 1) : ℝ) * (n : ℝ) ^ 2 +
      2 * (Nat.clog 2 (n - 1) : ℝ) * (n : ℝ) ^ 3 := by
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hq : (0 : ℝ) ≤ Nat.clog 2 (n - 1) := by
    exact_mod_cast Nat.zero_le (Nat.clog 2 (n - 1))
  have h2 := pow_nonneg hn 2
  have h3 := pow_nonneg hn 3
  nlinarith [mul_nonneg hq h2, mul_nonneg hq h3]

private lemma polynomial_isTheta : Asymptotics.IsTheta Filter.atTop
    (fun n : Nat => (n : ℝ) ^ 2 + 2 * (Nat.clog 2 (n - 1) : ℝ) * (n : ℝ) ^ 2 +
      2 * (Nat.clog 2 (n - 1) : ℝ) * (n : ℝ) ^ 3)
    (fun n : Nat => (n : ℝ) ^ 3 * Real.log (n : ℝ)) := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  apply Asymptotics.IsBigO.antisymm
  · refine Asymptotics.isBigO_iff.mpr ⟨10 / Real.log 2, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := by linarith
    have hg : 0 ≤ (n : ℝ) ^ 3 * Real.log (n : ℝ) :=
      mul_nonneg (pow_nonneg hn0 3) (Real.log_nonneg (by linarith))
    rw [Real.norm_of_nonneg (polynomial_nonneg n), Real.norm_of_nonneg hg,
      div_mul_eq_mul_div]
    apply (le_div_iff₀ htwo).mpr
    nlinarith [(polynomial_log_bounds hn).2]
  · refine Asymptotics.isBigO_iff.mpr ⟨Real.log 2, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := by linarith
    have hg : 0 ≤ (n : ℝ) ^ 3 * Real.log (n : ℝ) :=
      mul_nonneg (pow_nonneg hn0 3) (Real.log_nonneg (by linarith))
    rw [Real.norm_of_nonneg hg, Real.norm_of_nonneg (polynomial_nonneg n)]
    exact (polynomial_log_bounds hn).1

/-- The total selected event count of this execution family is Θ(n³ log n). -/
public theorem fasterAPSP_time_isTheta {α : Type u} [Add α] [Mul α] [Zero α]
    (W : (n : Nat) → Vector (Vector α n) n) :
    Asymptotics.IsTheta Filter.atTop
      (fun n => ((fasterAPSP (W n)).time.1 +
        (fasterAPSP (W n)).time.2.1 + (fasterAPSP (W n)).time.2.2 : ℝ))
      (fun n => (n : ℝ) ^ 3 * Real.log (n : ℝ)) := by
  have htime : (fun n => ((fasterAPSP (W n)).time.1 +
      (fasterAPSP (W n)).time.2.1 + (fasterAPSP (W n)).time.2.2 : ℝ)) =
      (fun n : Nat => (n : ℝ) ^ 2 + 2 * (Nat.clog 2 (n - 1) : ℝ) * (n : ℝ) ^ 2 +
        2 * (Nat.clog 2 (n - 1) : ℝ) * (n : ℝ) ^ 3) := by
    funext n
    simp only [fasterAPSP_time, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [htime]
  exact polynomial_isTheta

end Cslib.Algorithms.Lean.Matrix
