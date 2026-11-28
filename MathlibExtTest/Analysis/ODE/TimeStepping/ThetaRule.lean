/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
import MathlibExt.Analysis.ODE.TimeStepping.EulerStability
import MathlibExt.Analysis.ODE.TimeStepping.ThetaRule
import MathlibExt.Analysis.ODE.TimeStepping

/-! # Tests for `MathlibExt.Analysis.ODE.TimeStepping.ThetaRule` -/

namespace MathlibExtTest.Analysis.ODE.TimeStepping.ThetaRule

open MathlibExt.Analysis.ODE.TimeStepping.ThetaRule Filter Topology

/-! ### The three schemes -/

-- Forward Euler, Backward Euler and Crank–Nicolson factors.
example (a Δt : ℝ) : amplificationFactor 0 a Δt = 1 - a * Δt := by
  simp [amplificationFactor]

example (a Δt : ℝ) : amplificationFactor 1 a Δt = 1 / (1 + a * Δt) := by
  simp [amplificationFactor]

example (a Δt : ℝ) :
    amplificationFactor (1 / 2) a Δt = (1 - a * Δt / 2) / (1 + a * Δt / 2) := by
  unfold amplificationFactor
  ring

-- `I A^n` solves the scheme.
example (θ a Δt I : ℝ) (hΔt : Δt ≠ 0) (hden : 1 + θ * a * Δt ≠ 0) :
    IsSolution θ a Δt (fun n ↦ I * amplificationFactor θ a Δt ^ n) :=
  (isSolution_iff hΔt hden).mpr fun n ↦ by simp

-- The difference equation with the step written out, for Backward Euler with `a = 1`, `Δt = 1`:
-- `u^n = 2^{-n}`.
example : IsSolution 1 1 1 (fun n ↦ (1 / 2 : ℝ) ^ n) := by
  intro n
  simp only [pow_succ]
  ring

/-! ### Examples of Section 2.2.1 (`a = 2`, `I = 1`) -/

-- Forward Euler, `Δt = 1.25`: `A = -1.5`; the solution oscillates and grows.
example : amplificationFactor 0 2 (5 / 4) = -3 / 2 := by
  norm_num [amplificationFactor]

example {u : ℕ → ℝ} (hu : IsSolution 0 2 (5 / 4) u) (hu0 : u 0 = 1) (k : ℕ) :
    0 < u (2 * k) ∧ u (2 * k + 1) < 0 :=
  hu.sign_of_one_lt le_rfl (by norm_num) (by norm_num) (by norm_num) (by rw [hu0]; norm_num) k

example {u : ℕ → ℝ} (hu : IsSolution 0 2 (5 / 4) u) (hu0 : u 0 = 1) :
    Tendsto (fun n ↦ |u n|) atTop atTop :=
  hu.tendsto_abs_atTop le_rfl (by norm_num) (by norm_num) (by norm_num) (by rw [hu0]; norm_num)

-- Forward Euler, `Δt = 0.75`: `A = -0.5`; the solution oscillates and decays.
example : amplificationFactor 0 2 (3 / 4) = -1 / 2 := by
  norm_num [amplificationFactor]

example {u : ℕ → ℝ} (hu : IsSolution 0 2 (3 / 4) u) (hu0 : u 0 = 1) (k : ℕ) :
    0 < u (2 * k) ∧ u (2 * k + 1) < 0 :=
  hu.sign_of_one_lt le_rfl (by norm_num) (by norm_num) (by norm_num) (by rw [hu0]; norm_num) k

example {u : ℕ → ℝ} (hu : IsSolution 0 2 (3 / 4) u) (hu0 : u 0 = 1) :
    Tendsto u atTop (𝓝 0) :=
  (hu.tendsto_zero_iff le_rfl (by norm_num) (by norm_num) (by rw [hu0]; norm_num)).mpr
    (by norm_num)

-- Forward Euler, `Δt = 0.5`: `A = 0`, so `u^n = 0` for `n ≥ 1`.
example {u : ℕ → ℝ} (hu : IsSolution 0 2 (1 / 2) u) (n : ℕ) : u (n + 1) = 0 := by
  rw [(isSolution_iff (by norm_num) (by norm_num)).mp hu (n + 1)]
  norm_num [amplificationFactor]

-- Crank–Nicolson, `Δt = 1.25`: `A = -1/9 ≈ -0.11`; decaying oscillations.
example : amplificationFactor (1 / 2) 2 (5 / 4) = -1 / 9 := by
  norm_num [amplificationFactor]

example {u : ℕ → ℝ} (hu : IsSolution (1 / 2) 2 (5 / 4) u) (hu0 : u 0 = 1) (k : ℕ) :
    0 < u (2 * k) ∧ u (2 * k + 1) < 0 :=
  hu.sign_of_one_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [hu0]; norm_num)
    k

example {u : ℕ → ℝ} (hu : IsSolution (1 / 2) 2 (5 / 4) u) (hu0 : u 0 = 1) :
    Tendsto u atTop (𝓝 0) :=
  (hu.tendsto_zero_iff (by norm_num) (by norm_num) (by norm_num) (by rw [hu0]; norm_num)).mpr
    (by norm_num)

/-! ### The stability summary of Section 2.2.2 -/

-- Forward Euler: no growth iff `a Δt ≤ 2`, no sign change iff `a Δt ≤ 1`.
example {a Δt : ℝ} (ha : 0 ≤ a) (hΔt : 0 ≤ Δt) :
    |amplificationFactor 0 a Δt| ≤ 1 ↔ a * Δt ≤ 2 := by
  rw [abs_amplificationFactor_le_one_iff le_rfl ha hΔt]
  ring_nf

example {a Δt : ℝ} (ha : 0 ≤ a) (hΔt : 0 ≤ Δt) :
    amplificationFactor 0 a Δt < 0 ↔ 1 < a * Δt := by
  rw [amplificationFactor_neg_iff le_rfl ha hΔt]
  ring_nf

-- Crank–Nicolson and Backward Euler never grow, for every `Δt`.
example {u : ℕ → ℝ} {a Δt : ℝ} (hu : IsSolution (1 / 2) a Δt u) (ha : 0 ≤ a) (hΔt : 0 < Δt)
    (n : ℕ) : |u n| ≤ |u 0| := by
  by_cases hu0 : u 0 = 0
  · rw [(isSolution_iff hΔt.ne' (by positivity)).mp hu n, hu0, zero_mul]
  · exact (hu.abs_le_iff (by norm_num) ha hΔt hu0).mpr (by norm_num) n

example {u : ℕ → ℝ} {a Δt : ℝ} (hu : IsSolution 1 a Δt u) (ha : 0 ≤ a) (hΔt : 0 < Δt)
    (n : ℕ) : |u n| ≤ |u 0| := by
  by_cases hu0 : u 0 = 0
  · rw [(isSolution_iff hΔt.ne' (by positivity)).mp hu n, hu0, zero_mul]
  · exact (hu.abs_le_iff zero_le_one ha hΔt hu0).mpr (by nlinarith [mul_nonneg ha hΔt.le]) n

-- A Forward Euler solution that never grows has `a Δt ≤ 2`.
example {u : ℕ → ℝ} {a Δt : ℝ} (hu : IsSolution 0 a Δt u) (ha : 0 ≤ a) (hΔt : 0 < Δt)
    (hu0 : u 0 ≠ 0) (h : ∀ n, |u n| ≤ |u 0|) : a * Δt ≤ 2 := by
  have := (hu.abs_le_iff le_rfl ha hΔt hu0).mp h
  linarith

-- Backward Euler is nonnegative and nonincreasing for every `Δt`, and positive and strictly
-- decreasing when `a > 0` and `u^0 > 0`.
example {u : ℕ → ℝ} {a Δt : ℝ} (hu : IsSolution 1 a Δt u) (ha : 0 ≤ a) (hΔt : 0 < Δt)
    (hu0 : 0 ≤ u 0) : Antitone u :=
  (hu.antitone_of_le_one zero_le_one ha hΔt (by simp) hu0).2

example {u : ℕ → ℝ} {a Δt : ℝ} (hu : IsSolution 1 a Δt u) (ha : 0 < a) (hΔt : 0 < Δt)
    (hu0 : 0 < u 0) : StrictAnti u :=
  ((hu.strictAnti_iff_lt_one zero_le_one ha hΔt hu0).mpr (by simp)).2

-- Forward Euler at `a Δt = 1`: `A = 0`, so the solution is nonincreasing but not strictly
-- decreasing.
example {u : ℕ → ℝ} (hu : IsSolution 0 1 1 u) (hu0 : 0 < u 0) :
    Antitone u ∧ ¬ ((∀ n, 0 < u n) ∧ StrictAnti u) := by
  refine ⟨(hu.antitone_of_le_one le_rfl zero_le_one one_pos (by norm_num) hu0.le).2, fun h ↦ ?_⟩
  have := (hu.strictAnti_iff_lt_one le_rfl one_pos one_pos hu0).mp h
  norm_num at this

-- Crank–Nicolson at `a Δt = 2`: `A = 0`, no sign change. The book's strict `Δt < 2/a`
-- for avoiding oscillations is not needed at the boundary.
example {u : ℕ → ℝ} (hu : IsSolution (1 / 2) 1 2 u) (hu0 : 0 ≤ u 0) : ∀ n, 0 ≤ u n :=
  (hu.antitone_of_le_one (by norm_num) zero_le_one (by norm_num) (by norm_num) hu0).1

-- Forward Euler at `a Δt = 2`: `A = -1`; no growth, but no decay either.
example {u : ℕ → ℝ} (hu : IsSolution 0 1 2 u) (hu0 : u 0 ≠ 0) :
    (∀ n, |u n| ≤ |u 0|) ∧ ¬ Tendsto u atTop (𝓝 0) := by
  refine ⟨(hu.abs_le_iff le_rfl zero_le_one two_pos hu0).mpr (by norm_num), fun h ↦ ?_⟩
  have := (hu.tendsto_zero_iff le_rfl one_pos two_pos hu0).mp h
  norm_num at this

-- Wrong variant: Forward Euler is not unconditionally stable (`a Δt = 3`, `A = -2`).
example : ¬ ∀ u : ℕ → ℝ, IsSolution 0 1 3 u → ∀ n, |u n| ≤ |u 0| := by
  intro h
  have hu : IsSolution 0 1 3 (fun n ↦ amplificationFactor 0 1 3 ^ n) :=
    (isSolution_iff (by norm_num) (by norm_num)).mpr fun n ↦ by simp
  have := h _ hu 1
  norm_num [amplificationFactor] at this

-- The Forward Euler case agrees with the existing scalar Euler stability theorem.
example {a Δt : ℝ} (ha : 0 < a) (hΔt : 0 < Δt) :
    (∀ x0 : ℝ, Tendsto (fun n : ℕ ↦ (1 + Δt * -a) ^ n * x0) atTop (𝓝 0)) ↔
      |amplificationFactor 0 a Δt| < 1 := by
  rw [MathlibExt.Analysis.ODE.TimeStepping.scalarEuler_real_tendsto_zero_iff (neg_lt_zero.mpr ha)
    hΔt, abs_amplificationFactor_lt_one_iff le_rfl ha hΔt, abs_neg, abs_of_pos ha, lt_div_iff₀ ha]
  constructor <;> intro h <;> linarith

-- With `a = 0` the strict inequality `(1 - 2θ) a Δt < 2` holds, but a nonzero constant
-- solution does not decay.
example : IsSolution 0 0 1 (fun _ ↦ 1) ∧ ¬ Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 0) := by
  refine ⟨fun n ↦ by norm_num, ?_⟩
  rw [tendsto_const_nhds_iff]
  norm_num

-- Zero initial data do decay to zero, even outside the stability range.
example : IsSolution 0 1 3 (fun _ ↦ 0) ∧ Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) :=
  ⟨fun n ↦ by norm_num, tendsto_const_nhds⟩

-- The exact formula still applies outside `[0, 1]` when the denominator is nonzero.
example : IsSolution (-1 / 2) 1 1 (fun n ↦ (-1 : ℝ) ^ n) :=
  (isSolution_iff (by norm_num) (by norm_num)).mpr fun n ↦ by norm_num [amplificationFactor]

example {a Δt : ℝ} (ha : 0 < a) (hΔt : 0 < Δt) : |amplificationFactor 2 a Δt| < 1 :=
  (abs_amplificationFactor_lt_one_iff (by norm_num) ha hΔt).mpr
    (by nlinarith [mul_pos ha hΔt])

/-! ### The hypotheses are needed -/

-- `u^0 > 0` in `sign_of_one_lt`: with `u^0 = -1` the signs are swapped.
example : IsSolution 0 2 (5 / 4) (fun n ↦ -(-3 / 2 : ℝ) ^ n) ∧
    ¬ (fun n ↦ -(-3 / 2 : ℝ) ^ n) 1 < 0 :=
  ⟨(isSolution_iff (by norm_num) (by norm_num)).mpr fun n ↦ by norm_num [amplificationFactor],
    by norm_num⟩

-- `1 + θ a Δt ≠ 0` in `isSolution_iff`: for `θ = -1`, `a = Δt = 1`, the value `A = 0` of the
-- division by zero gives the sequence `1, 0, 0, ...`, which does not solve the scheme.
example : (∀ n, (fun n ↦ (0 : ℝ) ^ n) n = (fun n ↦ (0 : ℝ) ^ n) 0 *
      amplificationFactor (-1) 1 1 ^ n) ∧ ¬ IsSolution (-1) 1 1 (fun n ↦ (0 : ℝ) ^ n) := by
  refine ⟨fun n ↦ by norm_num [amplificationFactor], fun h ↦ ?_⟩
  have := h 0
  norm_num at this

-- `θ ≥ 0` in `amplificationFactor_neg_iff`: for `θ = -1`, `a = 1`, `Δt = 2`, `A = 3`.
example : ¬ (amplificationFactor (-1) 1 2 < 0 ↔ 1 < (1 - (-1 : ℝ)) * 1 * 2) := by
  norm_num [amplificationFactor]

-- The stability condition in `abs_sub_exp_le`: Forward Euler with `a = 1`, `Δt = 3`, `u^n = (-2)^n`
-- has error above `32` after five steps, while the bound would be `1/2 * 15 * 3`.
example : ¬ ∀ u : ℕ → ℝ, IsSolution 0 1 3 u → |u 5 - u 0 * Real.exp (-1 * ((5 : ℕ) * 3))| ≤
    max (0 - 1 / 2) (1 / 2) * |u 0| * 1 ^ 2 * ((5 : ℕ) * 3) * 3 := by
  intro h
  have hu : IsSolution 0 1 3 (fun n ↦ (-2 : ℝ) ^ n) :=
    (isSolution_iff (by norm_num) (by norm_num)).mpr fun n ↦ by norm_num [amplificationFactor]
  have := h _ hu
  have hexp := Real.exp_pos (-15)
  norm_num at this
  rw [abs_of_neg (by linarith)] at this
  linarith

/-! ### Accuracy (Sections 2.3.2 and 2.3.4) -/

-- One step of Backward Euler and of Crank–Nicolson at `a Δt = 1`: `A = 1/2` and `A = 1/3`.
example : |1 / 2 - Real.exp (-1)| ≤ 1 / 2 := by
  have h := abs_amplificationFactor_sub_exp_le (θ := 1) zero_le_one zero_le_one zero_le_one
  norm_num [amplificationFactor] at h
  exact h

example : |1 / 3 - Real.exp (-1)| ≤ 1 / 12 := by
  have h := abs_amplificationFactor_half_sub_exp_le zero_le_one zero_le_one
  norm_num [amplificationFactor] at h
  exact h

-- Wrong variant: the third-order bound of Crank–Nicolson fails for Forward Euler at `a Δt = 1`,
-- where `A = 0` and `e^{-1} > 1/4`.
example : ¬ |amplificationFactor 0 1 1 - Real.exp (-(1 * 1))| ≤ (1 * 1) ^ 3 / 4 := by
  have := Real.exp_neg_one_gt_d9
  norm_num [amplificationFactor] at this ⊢
  linarith

-- Forward Euler for `u' = -u`, `Δt = 1/10`, ten steps to `t = 1`: `|(9/10)^10 - e^{-1}| ≤ 1/20`,
-- sharper than `decay_euler_numeric_bound` in `TimeStepping`.
example : |(9 / 10 : ℝ) ^ 10 - Real.exp (-1)| ≤ 1 / 20 := by
  have hu : IsSolution 0 1 (1 / 10) (fun n ↦ (9 / 10 : ℝ) ^ n) :=
    (isSolution_iff (by norm_num) (by norm_num)).mpr fun n ↦ by norm_num [amplificationFactor]
  have := hu.abs_sub_exp_le le_rfl zero_le_one (by norm_num) (by norm_num) 10
  norm_num at this ⊢
  exact this

example : |(9 / 10 : ℝ) ^ 10 - Real.exp (-1)| ≤ 1 * (1 / 10) :=
  MathlibExt.Analysis.ODE.TimeStepping.decay_euler_numeric_bound

-- Backward Euler for `u' = -u`, `Δt = 1/10`, ten steps: the error is at most `1/20`.
example : |(10 / 11 : ℝ) ^ 10 - Real.exp (-1)| ≤ 1 / 20 := by
  have hu : IsSolution 1 1 (1 / 10) (fun n ↦ (10 / 11 : ℝ) ^ n) :=
    (isSolution_iff (by norm_num) (by norm_num)).mpr fun n ↦ by norm_num [amplificationFactor]
  have := hu.abs_sub_exp_le zero_le_one zero_le_one (by norm_num) (by norm_num) 10
  norm_num at this ⊢
  exact this

-- Crank–Nicolson for `u' = -u`, `Δt = 1/10`, ten steps: the error is at most `1/1200`.
example {u : ℕ → ℝ} (hu : IsSolution (1 / 2) 1 (1 / 10) u) (hu0 : u 0 = 1) :
    |u 10 - Real.exp (-1)| ≤ 1 / 1200 := by
  have := hu.abs_sub_exp_le_of_half zero_le_one (by norm_num) 10
  rw [hu0] at this
  norm_num at this
  exact this

-- Convergence at any time `t > 0` and from any initial value `I`, negative ones included; the
-- row for zero steps need not start at `I`.
example {θ a t I : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a) (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦ if n = 0 then 0 else I * amplificationFactor θ a (t / n) ^ n) atTop
      (𝓝 (I * Real.exp (-a * t))) := by
  have h := tendsto_of_isSolution (I := I)
    (u := fun n m ↦ if n = 0 then 0 else I * amplificationFactor θ a (t / n) ^ m) hθ ha ht
    (fun n hn ↦ by
      simp only [ite_eq_right hn.ne']
      exact (isSolution_iff (by positivity) (by positivity)).mpr fun m ↦ by simp)
    (fun n hn ↦ by simp [hn.ne'])
  simpa using h

end MathlibExtTest.Analysis.ODE.TimeStepping.ThetaRule
