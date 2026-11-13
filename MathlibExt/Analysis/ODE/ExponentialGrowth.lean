/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential growth path

The exponential path `x(t) = x₀ * exp (r * t)` satisfies the linear growth ODE
`x' = r * x` at every `t` and the initial condition `x(0) = x₀` (Atlas
roadmap M12.T01). No sign hypothesis on `x₀` or `r` is needed.

## Main results

* `MathlibExt.Analysis.ODE.ExponentialGrowth.expGrowthPath`
* `MathlibExt.Analysis.ODE.ExponentialGrowth.expGrowthPath_hasDerivAt`
* `MathlibExt.Analysis.ODE.ExponentialGrowth.expGrowthPath_zero`
-/

@[expose] public section

namespace MathlibExt.Analysis.ODE.ExponentialGrowth

/-- Exponential growth path with initial value `x₀` and rate `r`
(source clause: "exponential path `x₀ e^{rt}`"). -/
noncomputable def expGrowthPath (x₀ r : ℝ) (t : ℝ) : ℝ :=
  x₀ * Real.exp (r * t)

/-- The exponential path satisfies the linear growth ODE `x' = r * x` at every `t`
(Atlas roadmap M12.T01). No sign hypothesis on `x₀` or `r` is needed. -/
theorem expGrowthPath_hasDerivAt (x₀ r : ℝ) (t : ℝ) :
    HasDerivAt (expGrowthPath x₀ r) (r * expGrowthPath x₀ r t) t := by
  unfold expGrowthPath
  have h1 : HasDerivAt (fun t => r * t) r t := hasDerivAt_const_mul r
  have h2 : HasDerivAt (fun t => Real.exp (r * t)) (Real.exp (r * t) * r) t :=
    h1.exp
  have h3 : HasDerivAt (fun t => x₀ * Real.exp (r * t))
      (x₀ * (Real.exp (r * t) * r)) t :=
    h2.const_mul x₀
  have heq : x₀ * (Real.exp (r * t) * r) = r * (x₀ * Real.exp (r * t)) := by
    ring
  rw [heq] at h3
  exact h3

/-- The exponential path satisfies the initial condition `x(0) = x₀`
(Atlas roadmap M12.T01). -/
theorem expGrowthPath_zero (x₀ r : ℝ) : expGrowthPath x₀ r 0 = x₀ := by
  simp [expGrowthPath, Real.exp_zero]

end MathlibExt.Analysis.ODE.ExponentialGrowth
