/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import MathlibExt.Algebra.AffineRecurrence
import Mathlib.Tactic

/-!
# Single-cue error-correction convergence

Closed form and convergence for the deterministic scalar update
`v (n + 1) = v n + alpha * (lambda - v n)`, the one-component specialization
of the Rescorla--Wagner update (Sutton and Barto, *Reinforcement Learning:
An Introduction*, second edition, §14.2.2). It is the affine recurrence
with slope `1 - alpha` and intercept `alpha * lambda`; see
`isAffineRecurrence_iff_errorCorrection` below. No stochastic model
or empirical claim about learning is made.
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.AffineRecurrence

/-- **Closed form for the single-cue error-correction update.** If
`v (n + 1) = v n + alpha * (lambda - v n)` for every `n`, then
`v n = lambda + (1 - alpha) ^ n * (v 0 - lambda)`, for every value of
`alpha`, including the unit-root case `alpha = 0`.

The update is the one-component specialization of the Rescorla--Wagner
update in Sutton and Barto, *Reinforcement Learning: An Introduction*,
second edition, §14.2.2 (eqs. (14.2)--(14.3)): the aggregate associative
strength is the strength `v n` of the single present component, the
prediction error is `lambda - v n`, and the source step-size product is
written as the single gain `alpha`. No empirical claim about learning is
made; every result in this file is about the deterministic scalar recurrence
alone. -/
theorem errorCorrection_eq (alpha lambda : ℝ) {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + alpha * (lambda - v n)) (n : ℕ) :
    v n = lambda + (1 - alpha) ^ n * (v 0 - lambda) := by
  induction n with
  | zero => simp
  | succ n ih => rw [hv n, ih, pow_succ]; ring

/-- The error-correction update is the affine recurrence with slope
`1 - alpha` and intercept `alpha * lambda`, stated here with both sides
unfolded into update equations. -/
theorem errorCorrection_affine_iff (alpha lambda : ℝ) {v : ℕ → ℝ} :
    (∀ n, v (n + 1) = (1 - alpha) * v n + alpha * lambda) ↔
      (∀ n, v (n + 1) = v n + alpha * (lambda - v n)) := by
  constructor <;> intro h n <;> rw [h n] <;> ring

/-- The error-correction update as the canonical affine recurrence with
slope `1 - alpha` and intercept `alpha * lambda`. This restates
`errorCorrection_affine_iff` with the left side folded into
`IsAffineRecurrence`, whose defining equation is the same update. -/
theorem isAffineRecurrence_iff_errorCorrection (alpha lambda : ℝ) {v : ℕ → ℝ} :
    IsAffineRecurrence (1 - alpha) (alpha * lambda) v ↔
      (∀ n, v (n + 1) = v n + alpha * (lambda - v n)) :=
  errorCorrection_affine_iff alpha lambda

/-- **Generic affine-recurrence convergence.** If
`x (n + 1) = a * x n + b` for every `n` and `|a| < 1`, then `x` converges to
the fixed point `b / (1 - a)`. This is the shared convergence result used by
both the error-correction specialization below and the existing
government-debt specialization. -/
theorem affine_tendsto_fixedPoint {a b : ℝ} {x : ℕ → ℝ}
    (hx : ∀ n, x (n + 1) = a * x n + b) (ha : |a| < 1) :
    Tendsto x atTop (𝓝 (b / (1 - a))) := by
  have ha1 : (1 : ℝ) - a ≠ 0 := by
    have h := (abs_lt.mp ha).2
    have hpos : (0 : ℝ) < 1 - a := by linarith
    exact ne_of_gt hpos
  have hfix : a * (b / (1 - a)) + b = b / (1 - a) := by
    field_simp
    ring
  have hcf : ∀ n, x n = b / (1 - a) + a ^ n * (x 0 - b / (1 - a)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hx n, ih, pow_succ]; linear_combination hfix
  have hpow : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one ha
  have hmul : Tendsto (fun n : ℕ => a ^ n * (x 0 - b / (1 - a))) atTop (𝓝 0) := by
    have h := hpow.mul_const (x 0 - b / (1 - a))
    simpa using h
  have hconst : Tendsto (fun _ : ℕ => b / (1 - a)) atTop (𝓝 (b / (1 - a))) :=
    tendsto_const_nhds
  have hadd : Tendsto (fun n : ℕ => b / (1 - a) + a ^ n * (x 0 - b / (1 - a)))
      atTop (𝓝 (b / (1 - a))) := by
    have h := hconst.add hmul
    simpa using h
  have heq : x = (fun n : ℕ => b / (1 - a) + a ^ n * (x 0 - b / (1 - a))) := by
    funext n
    exact hcf n
  rw [heq]
  exact hadd

/-- **Convergence to the target.** When `0 < alpha < 2`, every solution of
the single-cue error-correction update converges to `lambda`. -/
theorem errorCorrection_tendsto (alpha lambda : ℝ) {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + alpha * (lambda - v n))
    (h0 : 0 < alpha) (h2 : alpha < 2) :
    Tendsto v atTop (𝓝 lambda) := by
  have haffine : ∀ n, v (n + 1) = (1 - alpha) * v n + alpha * lambda := by
    intro n
    rw [hv n]
    ring
  have habs : |(1 - alpha)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hlim := affine_tendsto_fixedPoint haffine habs
  have heq : (alpha * lambda) / (1 - (1 - alpha)) = lambda := by
    rw [show (1 : ℝ) - (1 - alpha) = alpha by ring]
    exact mul_div_cancel_left₀ lambda (ne_of_gt h0)
  rw [heq] at hlim
  exact hlim

/-- **Exact convergence range.** When the initial error `v 0 - lambda` is
nonzero, a solution of the single-cue error-correction update converges to
`lambda` if and only if `0 < alpha < 2`. -/
theorem errorCorrection_tendsto_iff_of_ne (alpha lambda : ℝ) {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + alpha * (lambda - v n)) (hne : v 0 ≠ lambda) :
    Tendsto v atTop (𝓝 lambda) ↔ 0 < alpha ∧ alpha < 2 := by
  constructor
  · intro hlim
    have hc : v 0 - lambda ≠ 0 := sub_ne_zero.mpr hne
    have hcf : ∀ n, v n = lambda + (1 - alpha) ^ n * (v 0 - lambda) :=
      fun n => errorCorrection_eq alpha lambda hv n
    have heq : v = (fun n : ℕ => lambda + (1 - alpha) ^ n * (v 0 - lambda)) := by
      funext n
      exact hcf n
    rw [heq] at hlim
    have h2 : Tendsto (fun n : ℕ => (1 - alpha) ^ n * (v 0 - lambda)) atTop (𝓝 0) := by
      have h := hlim.sub_const lambda
      rw [sub_self] at h
      exact Tendsto.congr (fun n => by ring) h
    have h3 : Tendsto (fun n : ℕ => (1 - alpha) ^ n) atTop (𝓝 0) := by
      have h := h2.mul_const (v 0 - lambda)⁻¹
      rw [zero_mul] at h
      exact Tendsto.congr (fun n => by rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]) h
    have habs : |(1 - alpha)| < 1 := tendsto_pow_atTop_nhds_zero_iff.mp h3
    rw [abs_lt] at habs
    constructor <;> linarith
  · intro h
    exact errorCorrection_tendsto alpha lambda hv h.1 h.2

/-- **No sign change of the error at or below unit gain.** When `alpha ≤ 1`,
the error `v n - lambda` never has the opposite sign to the initial error
`v 0 - lambda`: their product is nonnegative for every `n`. Within the
convergence range this is the nonoscillatory regime `0 < alpha ≤ 1`. -/
theorem errorCorrection_mul_nonneg_of_le_one (alpha lambda : ℝ) {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + alpha * (lambda - v n)) (h1 : alpha ≤ 1)
    (n : ℕ) :
    0 ≤ (v 0 - lambda) * (v n - lambda) := by
  have hcf := errorCorrection_eq alpha lambda hv n
  have hnonneg : 0 ≤ (1 - alpha) ^ n := pow_nonneg (by linarith) n
  have hsq : 0 ≤ (v 0 - lambda) ^ 2 := sq_nonneg _
  have heq : (v 0 - lambda) * (v n - lambda)
      = (1 - alpha) ^ n * (v 0 - lambda) ^ 2 := by
    rw [hcf]
    ring
  rw [heq]
  exact mul_nonneg hnonneg hsq

/-- The closed-form sequence itself satisfies the update: the hypothesis of
the theorems above is satisfiable for every initial value `c`. -/
theorem errorCorrection_closedForm_update (alpha lambda c : ℝ) (n : ℕ) :
    (lambda + (1 - alpha) ^ (n + 1) * (c - lambda)) =
      (lambda + (1 - alpha) ^ n * (c - lambda)) +
        alpha * (lambda - (lambda + (1 - alpha) ^ n * (c - lambda))) := by
  rw [pow_succ]
  ring

end MathlibExt.AffineRecurrence
