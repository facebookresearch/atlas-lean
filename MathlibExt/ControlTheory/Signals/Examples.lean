/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.ControlTheory.Signals.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Signal-system counterexamples

Three classical witnesses, each on integer-time and real-time real signals:
squaring is not additive (with `x = y = 1`, `(x t + y t)^2 = 4` against
`x t^2 + y t^2 = 2`); multiplication by time (`timeMul x t = t * x t`,
`timeMulInt x n = n * x n`) is linear but not time invariant (on the constant
signal `1`, shift-then-multiply gives `t`, multiply-then-shift `t - 1`); the
one-step advance `shiftₗ ℝ ℝ (-1)` is not causal (an impulse at time `1` is
visible at time `0`). These are the standard counterexamples accompanying the definitions in
`Signals.Basic`.
-/

@[expose] public section

namespace ControlTheory

/-- Multiplication by time on real-time real signals, as a linear map:
`timeMul x t = t * x t`. -/
def timeMul : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun x t := t * x t
  map_add' x y := by
    funext t
    simp [mul_add]
  map_smul' c x := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact mul_left_comm _ _ _

/-- Multiplication by time on integer-time real signals, as a linear
map: `timeMulInt x n = n * x n` (with `n` cast to `ℝ`). -/
def timeMulInt : (ℤ → ℝ) →ₗ[ℝ] (ℤ → ℝ) where
  toFun x n := (n : ℝ) * x n
  map_add' x y := by
    funext n
    simp [mul_add]
  map_smul' c x := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact mul_left_comm _ _ _

@[simp]
theorem timeMul_apply (x : ℝ → ℝ) (t : ℝ) : timeMul x t = t * x t := by
  rfl

@[simp]
theorem timeMulInt_apply (x : ℤ → ℝ) (n : ℤ) :
    timeMulInt x n = (n : ℝ) * x n := by
  rfl

/-- Squaring is not additive on integer-time real signals: the system
`x ↦ (t ↦ (x t)^2)` does not preserve addition (witness `x = y = 1`
at `t = 0`: `4 ≠ 2`). -/
theorem sq_not_additive_int :
    ¬ ∀ x y : ℤ → ℝ, (fun t => ((x + y) t) ^ 2)
      = (fun t => (x t) ^ 2) + (fun t => (y t) ^ 2) := by
  intro h
  have h0 := congrFun (h 1 1) 0
  simp only [Pi.add_apply, Pi.one_apply] at h0
  simp only [one_add_one_eq_two, pow_two, two_mul, one_mul] at h0
  have h3 : (2 : ℝ) + 2 = (2 : ℝ) + 0 := by rw [add_zero]; exact h0
  exact two_ne_zero (add_left_cancel h3)

/-- Squaring is not additive on real-time real signals: the system
`x ↦ (t ↦ (x t)^2)` does not preserve addition (witness `x = y = 1`
at `t = 0`: `4 ≠ 2`). -/
theorem sq_not_additive_real :
    ¬ ∀ x y : ℝ → ℝ, (fun t => ((x + y) t) ^ 2)
      = (fun t => (x t) ^ 2) + (fun t => (y t) ^ 2) := by
  intro h
  have h0 := congrFun (h 1 1) 0
  simp only [Pi.add_apply, Pi.one_apply] at h0
  simp only [one_add_one_eq_two, pow_two, two_mul, one_mul] at h0
  have h3 : (2 : ℝ) + 2 = (2 : ℝ) + 0 := by rw [add_zero]; exact h0
  exact two_ne_zero (add_left_cancel h3)

/-- Multiplication by time is not time invariant on real-time signals:
shifting by `1` and then multiplying by `t` differs from multiplying by
`t` and then shifting (witness the constant signal `1`: one composition
gives `t` and the other `t - 1`, so they differ at every `t`, for
instance `1 ≠ 0` at `t = 1` and `0 ≠ -1` at `t = 0`). -/
theorem not_isTimeInvariant_timeMul : ¬ IsTimeInvariant timeMul := by
  intro h
  have h1 := h (1 : ℝ)
  have h2 := LinearMap.congr_fun h1 (1 : ℝ → ℝ)
  have h3 := congrFun h2 (1 : ℝ)
  simp only [LinearMap.comp_apply, shiftₗ_apply, timeMul_apply, Pi.one_apply] at h3
  norm_num at h3

/-- Multiplication by time is not time invariant on integer-time
signals (same witnesses as the real-time case). -/
theorem not_isTimeInvariant_timeMulInt : ¬ IsTimeInvariant timeMulInt := by
  intro h
  have h1 := h (1 : ℤ)
  have h2 := LinearMap.congr_fun h1 (1 : ℤ → ℝ)
  have h3 := congrFun h2 (1 : ℤ)
  simp only [LinearMap.comp_apply, shiftₗ_apply, timeMulInt_apply, Pi.one_apply] at h3
  norm_num at h3

/-- The one-step advance `shiftₗ ℝ ℝ (-1)` is not causal on
integer-time signals: an impulse at time `1` is already visible at
time `0`, while the zero signal agrees with it at all times `≤ 0`. -/
theorem not_isCausal_shift_neg_one_int :
    ¬ IsCausal (shiftₗ ℝ ℝ (-1 : ℤ)) := by
  intro h
  have hpre : ∀ s ≤ (0 : ℤ), (fun n => if n = 1 then (1 : ℝ) else 0) s
      = (0 : ℤ → ℝ) s := by
    intro s hs
    have hne : s ≠ 1 := by omega
    simp [hne]
  have h0 := h (0 : ℤ) (fun n => if n = 1 then (1 : ℝ) else 0) 0 hpre
  have e : (0 : ℤ) - -1 = 1 := by norm_num
  simp only [shiftₗ_apply, Pi.zero_apply, e] at h0
  simp at h0

/-- The one-step advance `shiftₗ ℝ ℝ (-1)` is not causal on real-time
signals (same witnesses as the integer-time case). -/
theorem not_isCausal_shift_neg_one_real :
    ¬ IsCausal (shiftₗ ℝ ℝ (-1 : ℝ)) := by
  intro h
  have hpre : ∀ s ≤ (0 : ℝ), (fun t => if t = 1 then (1 : ℝ) else 0) s
      = (0 : ℝ → ℝ) s := by
    intro s hs
    have hne : s ≠ 1 := ne_of_lt (lt_of_le_of_lt hs zero_lt_one)
    simp [hne]
  have h0 := h (0 : ℝ) (fun t => if t = 1 then (1 : ℝ) else 0) 0 hpre
  have e : (0 : ℝ) - -1 = 1 := by norm_num
  simp only [shiftₗ_apply, Pi.zero_apply, e] at h0
  simp at h0

end ControlTheory
