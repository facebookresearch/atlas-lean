/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.Analysis.ODE.ExistUnique

/-!
# Exponential growth path

The exponential path `x(t) = x₀ * exp (r * t)` satisfies the linear growth ODE
`x' = r * x` at every `t` and the initial condition `x(0) = x₀` (Atlas
roadmap M12.T01). Conversely, every function satisfying `x' = r * x` at every
`t` is the exponential path through its own initial value `x 0`. No sign
hypothesis on `x₀` or `r` is needed: the path decays for `r < 0`, is constant
for `r = 0`, and grows for `r > 0`.

## Main results

* `MathlibExt.Analysis.ODE.ExponentialGrowth.expGrowthPath`
* `MathlibExt.Analysis.ODE.ExponentialGrowth.expGrowthPath_hasDerivAt`
* `MathlibExt.Analysis.ODE.ExponentialGrowth.expGrowthPath_zero`
* `MathlibExt.Analysis.ODE.ExponentialGrowth.eq_expGrowthPath_of_hasDerivAt`
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

/-- Uniqueness for the linear growth ODE: a function satisfying `x' = r * x` at every
`t` is the exponential path through its initial value, `x t = x 0 * exp (r * t)`.
No sign hypothesis on `r` is needed, so this covers decay (`r < 0`) and growth
(`r > 0`) alike. The proof applies Mathlib's `ODE_solution_unique_univ` to the
`‖r‖₊`-Lipschitz field `y ↦ r * y`, comparing `x` with `expGrowthPath (x 0) r`. -/
theorem eq_expGrowthPath_of_hasDerivAt {x : ℝ → ℝ} {r : ℝ}
    (hx : ∀ t, HasDerivAt x (r * x t) t) (t : ℝ) :
    x t = expGrowthPath (x 0) r t := by
  have hlip : LipschitzWith ‖r‖₊ (fun y : ℝ => r * y) := lipschitzWith_smul r
  have h : x = expGrowthPath (x 0) r :=
    ODE_solution_unique_univ (v := fun _ y => r * y) (s := fun _ => Set.univ) (t₀ := 0)
      (fun _ => hlip.lipschitzOnWith) (fun s => ⟨hx s, Set.mem_univ _⟩)
      (fun s => ⟨expGrowthPath_hasDerivAt (x 0) r s, Set.mem_univ _⟩)
      (expGrowthPath_zero (x 0) r).symm
  exact congrFun h t

end MathlibExt.Analysis.ODE.ExponentialGrowth
