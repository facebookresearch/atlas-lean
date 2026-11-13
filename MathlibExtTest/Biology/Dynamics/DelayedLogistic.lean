/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.DelayedLogistic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tests for the Hutchinson delayed logistic equation

Concrete parameters `r = 1`, `K = 1`: the critical delay is `π / 2`, the positive equilibrium
is `1`; characteristic roots computed from the definition on either side of and at `τ_c`
(`-1` at `τ = 0`, `-2` at `τ = log 2 / 2`, `i` at `τ = π / 2`, and an explicit root with
positive real part at `τ = (3π/4) √2 e^{3π/4}`); stability for `τ = 1`, instability and a
growing linearized oscillation for `τ = 2`; the zero-delay reduction to the logistic ODE;
global existence for a constant history, with the first step of the method of steps computed
explicitly.
-/

@[expose] public section

open Real Set
open MathlibExt.Biology.Dynamics.DelayedLogistic MathlibExt.Biology.Dynamics

namespace MathlibExtTest.Biology.Dynamics.DelayedLogistic

/-! ### Parameters `r = 1`, `K = 1` -/

/-- The critical delay for `r = 1` is `π / 2`. -/
example : criticalDelay 1 = π / 2 := by norm_num [criticalDelay]

/-- The positive equilibrium `1` is a constant solution, checked from the definition. -/
example (τ : ℝ) : IsSolution 1 1 τ (fun _ => 1) (fun _ => 1) :=
  ⟨fun _ _ => rfl, continuousOn_const,
    fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) (1 : ℝ)⟩

/-- The constant solutions for `r = K = 1` are exactly `0` and `1`; `2` is not one. -/
example (τ : ℝ) : ¬ IsSolution 1 1 τ (fun _ => 2) (fun _ => 2) := by
  rw [const_isSolution_iff one_ne_zero one_ne_zero]
  norm_num

/-! ### The characteristic equation computed from the definition -/

/-- `τ = 0`: the characteristic equation is `z + 1 = 0`, the logistic ODE's linear rate. -/
example (z : ℂ) : charFun 1 0 z = 0 ↔ z = -1 := by
  simp only [charFun, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    Complex.ofReal_one, mul_one]
  constructor <;> intro h <;> linear_combination h

/-- Below `τ_c`: `z = -2` is a root at `τ = log 2 / 2` (computed directly), so the stability
statement concerns a nonempty root set. -/
example : charFun 1 (Real.log 2 / 2) (-2) = 0 := by
  have h : -((-2 : ℂ) * ((Real.log 2 / 2 : ℝ) : ℂ)) = ((Real.log 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [charFun, h, ← Complex.ofReal_exp, Real.exp_log (by norm_num)]
  push_cast; ring

/-- The delay `log 2 / 2` is below the critical delay `π / 2`. -/
example : Real.log 2 / 2 < criticalDelay 1 := by
  have h1 : Real.log 2 < 2 - 1 := Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
  rw [criticalDelay]
  linarith [pi_gt_three]

/-- At `τ_c = π / 2`: `z = i` is a root (computed directly), with real part `0`, so the strict
inequality `τ < τ_c` in the stability theorem cannot be dropped. -/
example : charFun 1 (π / 2) Complex.I = 0 := by
  have h : -(Complex.I * ((π / 2 : ℝ) : ℂ)) = ((-(π / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [charFun, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, cos_neg,
    sin_neg, cos_pi_div_two, sin_pi_div_two]
  push_cast; ring

/-- Above `τ_c`: an explicit root with positive real part, computed from the definition. With
`θ = 3π/4` and `τ = θ √2 e^{θ}`, the number `z = (θ / τ)(1 + i)` solves `z + e^{-z τ} = 0`. -/
example : charFun 1 (3 * π / 4 * √2 * exp (3 * π / 4))
    ⟨3 * π / 4 / (3 * π / 4 * √2 * exp (3 * π / 4)),
      3 * π / 4 / (3 * π / 4 * √2 * exp (3 * π / 4))⟩ = 0 := by
  set θ : ℝ := 3 * π / 4 with hθ
  set τ : ℝ := θ * √2 * exp θ with hτ
  have hθpos : 0 < θ := by positivity
  have hs : (0 : ℝ) < √2 := by positivity
  have hτpos : 0 < τ := by positivity
  have hcτ : θ / τ * τ = θ := by field_simp
  have hcos : cos θ = -(√2 / 2) := by
    rw [hθ, show 3 * π / 4 = π - π / 4 by ring, cos_pi_sub, cos_pi_div_four]
  have hsin : sin θ = √2 / 2 := by
    rw [hθ, show 3 * π / 4 = π - π / 4 by ring, sin_pi_sub, sin_pi_div_four]
  have hE : exp (-θ) * exp θ = 1 := by rw [← exp_add]; simp
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have key : θ / τ = exp (-θ) * (√2 / 2) := by
    rw [hτ, div_eq_iff (by positivity)]
    calc θ = θ * (exp (-θ) * exp θ) * ((√2 * √2) / 2) := by rw [hE, hsq]; ring
      _ = exp (-θ) * (√2 / 2) * (θ * √2 * exp θ) := by ring
  rw [charFun_eq_zero_iff]
  simp only [hcτ, hcos, hsin]
  constructor <;> rw [key] <;> ring

/-- The explicit unstable delay `(3π/4) √2 e^{3π/4}` is above the critical delay `π / 2`. -/
example : criticalDelay 1 < 3 * π / 4 * √2 * exp (3 * π / 4) := by
  have h2 : (1 : ℝ) ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
  have he : 1 ≤ exp (3 * π / 4) := one_le_exp (by positivity)
  rw [criticalDelay]
  have hπ := pi_pos
  calc π / (2 * 1) < 3 * π / 4 * 1 * 1 := by linarith
    _ ≤ 3 * π / 4 * √2 * exp (3 * π / 4) := by gcongr

/-! ### Stability and instability on either side of `τ_c = π / 2` -/

/-- `τ = 1 < π / 2`: every characteristic root has negative real part. -/
example (z : ℂ) (hz : charFun 1 1 z = 0) : z.re < 0 :=
  re_neg_of_charFun_eq_zero one_pos zero_le_one
    (by rw [criticalDelay]; linarith [pi_gt_three]) hz

/-- At `τ = τ_c` every root has nonpositive real part. -/
example (z : ℂ) (hz : charFun 1 (π / 2) z = 0) : z.re ≤ 0 :=
  re_nonpos_of_charFun_eq_zero one_pos (by positivity) (by norm_num [criticalDelay]) hz

/-- `τ = 2 > π / 2`: a characteristic root with positive real part exists. -/
example : ∃ z : ℂ, charFun 1 2 z = 0 ∧ 0 < z.re :=
  let ⟨z, hz, hre, _⟩ := exists_charFun_eq_zero_re_pos one_pos
    (by rw [criticalDelay]; linarith [pi_lt_d2])
  ⟨z, hz, hre⟩

/-- Large delay `τ = 2`: the linearized equation `u'(t) = -u(t - 2)` has a real solution that
oscillates about `0` with unbounded amplitude. -/
example : ∃ u : ℝ → ℝ, (∀ t, HasDerivAt u (-(1 * u (t - 2))) t) ∧
    ∀ M T : ℝ, (∃ t ≥ T, M ≤ u t) ∧ ∃ t ≥ T, u t ≤ -M :=
  exists_linearized_oscillation one_pos (by rw [criticalDelay]; linarith [pi_lt_d2])

/-! ### Zero delay: the logistic ODE -/

/-- For `τ = 0` the right-hand side reads `r x(t) (1 - x(t) / K)`, the logistic ODE. -/
example (x : ℝ → ℝ) (t : ℝ) : 1 * x t * (1 - x (t - 0) / 1) = 1 * x t * (1 - x t / 1) := by
  rw [sub_zero]

/-- The logistic solution solves the zero-delay equation. -/
example : IsSolution 1 1 0 (fun _ => 1 / 2) (Logistic.logistic 1 1 (1 / 2)) :=
  isSolution_logistic zero_le_one one_pos (by norm_num)

/-- Every zero-delay solution is the logistic solution on `[0, ∞)`. -/
example {x : ℝ → ℝ} (hx : IsSolution 1 1 0 (fun _ => 1 / 2) x) :
    EqOn x (Logistic.logistic 1 1 (1 / 2)) (Ici 0) :=
  hx.eqOn_logistic zero_le_one one_pos (by norm_num)

/-! ### Global existence for a positive delay -/

/-- Global existence for `τ = 2` with constant history `1 / 2`, via the method of steps. -/
example : IsSolution 1 1 2 (fun _ => 1 / 2) (solution 1 1 2 fun _ => 1 / 2) :=
  isSolution_solution two_pos continuousOn_const

/-- A positive global solution exists for `τ = 2`. -/
example : ∃ x, IsSolution 1 1 2 (fun _ => 1 / 2) x ∧ ∀ t, 0 ≤ t → 0 < x t :=
  exists_isSolution_pos zero_le_two zero_le_one one_pos continuousOn_const (by norm_num)

/-- First step of the method of steps: on `[0, 2]` the solution with constant history `1 / 2`
only sees the history, so `x(t) = e^{t / 2} / 2`. -/
example {x : ℝ → ℝ} (hx : IsSolution 1 1 2 (fun _ => 1 / 2) x) {t : ℝ} (ht : t ∈ Icc 0 2) :
    x t = 1 / 2 * exp (t / 2) := by
  rw [hx.eq_mul_exp_integral zero_le_two ht.1, hx.eqOn_history ⟨by norm_num, le_rfl⟩]
  have hint : ∫ s in (0 : ℝ)..t, (1 - x (s - 2) / 1) = ∫ _ in (0 : ℝ)..t, (1 / 2 : ℝ) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    rw [hx.eqOn_history ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩]
    norm_num
  rw [hint, intervalIntegral.integral_const, smul_eq_mul]
  ring_nf

/-- Two solutions with the same history agree on `[-τ, ∞)`. -/
example {x : ℝ → ℝ} (hx : IsSolution 1 1 2 (fun _ => 1 / 2) x) :
    EqOn x (solution 1 1 2 fun _ => 1 / 2) (Ici (-2)) :=
  hx.eqOn two_pos (isSolution_solution two_pos continuousOn_const)

end MathlibExtTest.Biology.Dynamics.DelayedLogistic
