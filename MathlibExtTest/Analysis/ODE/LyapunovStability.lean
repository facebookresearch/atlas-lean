/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.LyapunovStability
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Tests for Lyapunov's direct method on the scalar equation `x' = -x` with `V x = x²`:
`x(t) = e^{-t} x₀` is a forward solution (non-vacuity witness for the solution hypothesis), and
the decay, attraction, sublevel and stability statements apply to it. -/

open Set Filter Real
open scoped Topology

namespace MathlibExtTest.Analysis.ODE.LyapunovStability

/-- `x(t) = e^{-t} x₀` solves `x' = -x` (two-sided derivative at every `t`). -/
theorem hasDerivAt_exp_neg_mul (x₀ t : ℝ) :
    HasDerivAt (fun τ => exp (-τ) * x₀) (-(exp (-t) * x₀)) t := by
  have h := ((hasDerivAt_neg t).exp).mul_const x₀
  convert h using 1
  ring

/-- `x(t) = e^{-t} x₀` is an integral curve of `x ↦ -1 * x` on `[0, ∞)`. -/
theorem isIntegralCurveOn_exp_neg (x₀ : ℝ) :
    IsIntegralCurveOn (fun τ => exp (-τ) * x₀) (fun _ y => -1 * y) (Ici 0) := fun t _ => by
  simpa using (hasDerivAt_exp_neg_mul x₀ t).hasDerivWithinAt

/-- The derivative of `V x = x²`. -/
theorem hasFDerivAt_sq (y : ℝ) :
    HasFDerivAt (fun z : ℝ => z ^ 2) (ContinuousLinearMap.toSpanSingleton ℝ (2 * y)) y := by
  simpa using (hasDerivAt_pow 2 y).hasFDerivAt

/-- Orbital derivative of `V x = x²` along `x' = -x`: `2 x (-x) = -2 x²`. -/
theorem orbital_sq (t : ℝ) (_ht : 0 ≤ t) (y : ℝ) (_hy : y ∈ (univ : Set ℝ)) :
    ContinuousLinearMap.toSpanSingleton ℝ (2 * y) ((fun _ z => -1 * z) t y) ≤ -2 * y ^ 2 := by
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  nlinarith

/-- Scalar Grönwall core: `u = e^{-t}` with `u' = -u` gives `u t ≤ e^{-t} u 0`. -/
example (t : ℝ) (ht : 0 ≤ t) : exp (-t) ≤ exp (-1 * t) * exp (-0) :=
  le_exp_mul_of_hasDerivWithinAt_Ici (u := fun τ => exp (-τ)) (u' := fun τ => -exp (-τ))
    (fun τ _ => by simpa using ((hasDerivAt_neg τ).exp).hasDerivWithinAt)
    (fun τ _ => by simp) ht

/-- Decay of `V` along the solution: `(e^{-t} x₀)² ≤ e^{-2t} x₀²`. -/
example (x₀ t : ℝ) (ht : 0 ≤ t) :
    (exp (-t) * x₀) ^ 2 ≤ exp (-2 * t) * (exp (-0) * x₀) ^ 2 :=
  (isIntegralCurveOn_exp_neg x₀).lyapunov_le_exp (s := univ) (V := fun z => z ^ 2)
    (fun _ _ => mem_univ _) (fun y _ => hasFDerivAt_sq y) orbital_sq ht

/-- The general criterion with `c₁ = c₂ = 1`, `a = 2`, `x₀ = 0` gives
`|e^{-t} x₀| ≤ √1 · e^{-t} · |x₀|`. -/
example (x₀ t : ℝ) (ht : 0 ≤ t) :
    ‖exp (-t) * x₀ - 0‖ ≤ √(1 / 1) * exp (-(2 / 2) * t) * ‖exp (-0) * x₀ - 0‖ :=
  (isIntegralCurveOn_exp_neg x₀).norm_sub_le_of_lyapunov (s := univ) (V := fun z => z ^ 2)
    (fun _ _ => mem_univ _) (fun y _ => hasFDerivAt_sq y) orbital_sq one_pos
    (fun y _ => by simp) (fun y _ => by simp) ht

/-- The packaged scalar application, instantiated at `k = 1`. -/
example (x₀ t : ℝ) (ht : 0 ≤ t) : |exp (-t) * x₀| ≤ exp (-1 * t) * |exp (-0) * x₀| :=
  (isIntegralCurveOn_exp_neg x₀).abs_le_exp_neg_mul ht

/-- The packaged scalar application recovers the exact solution's size: the bound is attained,
`|e^{-t} x₀| = e^{-t} |x₀|`. -/
example (x₀ t : ℝ) : |exp (-t) * x₀| = exp (-1 * t) * |exp (-0) * x₀| := by
  simp [abs_mul, abs_of_pos (exp_pos _)]

/-- Attraction: `e^{-t} x₀ → 0`. -/
example (x₀ : ℝ) : Tendsto (fun τ => exp (-τ) * x₀) atTop (𝓝 0) :=
  (isIntegralCurveOn_exp_neg x₀).tendsto_of_lyapunov (s := univ) (V := fun z => z ^ 2)
    (fun _ _ => mem_univ _) (fun y _ => hasFDerivAt_sq y) orbital_sq two_pos one_pos
    (c₂ := 1) (fun y _ => by simp) (fun y _ => by simp)

/-- Sublevel invariance: the solution started at `x₀ = 3` stays in `{x | x² ≤ 9}`. -/
example : MapsTo (fun τ => exp (-τ) * 3) (Ici 0) {x : ℝ | x ^ 2 ≤ 9} :=
  (isIntegralCurveOn_exp_neg 3).mapsTo_sublevel_of_lyapunov (s := univ)
    (fun _ _ => mem_univ _) (fun y _ => hasFDerivAt_sq y)
    (fun t ht y hy => (orbital_sq t ht y hy).trans (by nlinarith [sq_nonneg y])) (by norm_num)

/-- `ε`-`δ` stability and attraction of `0` for `x' = -x`. -/
example : (∀ ε > 0, ∃ δ > 0, ∀ γ : ℝ → ℝ, IsIntegralCurveOn γ (fun _ y => -1 * y) (Ici 0) →
      (∀ t, 0 ≤ t → γ t ∈ (univ : Set ℝ)) → ‖γ 0 - 0‖ < δ → ∀ t, 0 ≤ t → ‖γ t - 0‖ < ε) ∧
    ∀ γ : ℝ → ℝ, IsIntegralCurveOn γ (fun _ y => -1 * y) (Ici 0) →
      (∀ t, 0 ≤ t → γ t ∈ (univ : Set ℝ)) → Tendsto γ atTop (𝓝 0) :=
  lyapunov_asymptotically_stable (V := fun z => z ^ 2) (fun y _ => hasFDerivAt_sq y) orbital_sq
    two_pos one_pos (c₂ := 1) (fun y _ => by simp) (fun y _ => by simp)

/-- The non-asymptotic stability theorem with a conserved quantity: for `x' = 0`, `V x = x²` has
orbital derivative `0`, so the stability bound holds with `√(c₂/c₁) = 1`. -/
example (x₀ t : ℝ) (ht : 0 ≤ t) :
    ‖(fun _ : ℝ => x₀) t - 0‖ ≤ √(1 / 1) * ‖(fun _ : ℝ => x₀) 0 - 0‖ :=
  IsIntegralCurveOn.norm_sub_le_of_lyapunov_nonpos (f := fun _ _ => 0) (s := univ) (x₀ := 0)
    (c₂ := 1)
    (V := fun z => z ^ 2) (fun t _ => by simpa using (hasDerivAt_const t x₀).hasDerivWithinAt)
    (fun _ _ => mem_univ _) (fun y _ => hasFDerivAt_sq y) (fun _ _ y _ => by simp) one_pos
    (fun y _ => by simp) (fun y _ => by simp) ht

end MathlibExtTest.Analysis.ODE.LyapunovStability
