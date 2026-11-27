/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Scalar linear relaxation

The variation-of-constants formula for `z' = P(t) - α z` with initial value `z₀`.
The forcing need only be interval integrable; the derivative formula holds at its
points of continuity.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral

namespace MathlibExt.Biology.Dynamics.FeedForwardLoop

/-- The variation-of-constants solution of `z' = P(t) - α z`, `z(0) = z₀`:
`z(t) = z₀ e^{-α t} + ∫₀ᵗ e^{-α (t - s)} P(s) ds`. Used for `t ≥ 0`. -/
noncomputable def relaxation (α : ℝ) (P : ℝ → ℝ) (z₀ t : ℝ) : ℝ :=
  z₀ * exp (-α * t) + ∫ s in (0)..t, exp (-α * (t - s)) * P s

/-- The relaxation solves `z' = P - α z` at every time where the (locally integrable) forcing
term `P` is continuous. -/
theorem hasDerivAt_relaxation {α : ℝ} {P : ℝ → ℝ} (z₀ : ℝ)
    (hP : ∀ a b, IntervalIntegrable P volume a b) {t : ℝ} (ht : ContinuousAt P t) :
    HasDerivAt (relaxation α P z₀) (P t - α * relaxation α P z₀ t) t := by
  have hExp : Continuous (fun s : ℝ ↦ exp (α * s)) := by fun_prop
  have hInt (a b : ℝ) :
      IntervalIntegrable (fun s ↦ exp (α * s) * P s) volume a b :=
    (hP a b).continuousOn_mul hExp.continuousOn
  have hMeas : StronglyMeasurableAtFilter (fun s ↦ exp (α * s) * P s) (nhds t) volume := by
    refine ⟨Ioc (t - 1) (t + 1), Ioc_mem_nhds (by linarith) (by linarith), ?_⟩
    have hi := (hInt (t - 1) (t + 1)).def'
    rw [uIoc_of_le (by linarith : t - 1 ≤ t + 1)] at hi
    exact hi.aestronglyMeasurable
  have hFTC := integral_hasDerivAt_right (hInt 0 t) hMeas (hExp.continuousAt.mul ht)
  have hFactor (u : ℝ) : relaxation α P z₀ u =
      exp (-α * u) * (z₀ + ∫ s in (0)..u, exp (α * s) * P s) := by
    unfold relaxation
    rw [mul_add, ← intervalIntegral.integral_const_mul]
    congr 1
    · ring
    · apply integral_congr
      intro s hs
      dsimp
      rw [← mul_assoc, ← exp_add]
      congr 2
      ring
  have h := (((hasDerivAt_id' t).const_mul (-α)).exp).mul (hFTC.const_add z₀)
  convert h using 1
  · funext u
    exact hFactor u
  · rw [hFactor t]
    have he : exp (-α * t) * exp (α * t) = 1 := by
      rw [← exp_add]
      simp
    linear_combination -P t * he

end MathlibExt.Biology.Dynamics.FeedForwardLoop
