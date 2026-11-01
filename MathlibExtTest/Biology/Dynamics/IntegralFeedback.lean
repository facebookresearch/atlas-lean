/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.IntegralFeedback

/-! Tests for integral feedback: a two-state system whose second state integrates the output
(non-vacuity witness of `HasIntegralFeedback`), and a one-state system without adaptation. -/

open Matrix

namespace MathlibExtTest.Biology.Dynamics.IntegralFeedback

open MathlibExt.Biology.Dynamics.IntegralFeedback

/-- `ẋ₀ = -x₀ - x₁ + u`, `ẋ₁ = x₀`, output `y = x₀`: the state `x₁` is the integral of `y`. -/
def integrator : LinearSystem (Fin 2) where
  A := !![-1, -1; 1, 0]
  b := ![1, 0]
  c := ![1, 0]
  d := 0

/-- **Non-vacuity witness.** `k = (0, 1)` integrates the output. -/
example : integrator.HasIntegralFeedback :=
  ⟨![0, 1], fun x u ↦ by
    simp [integrator, LinearSystem.field, LinearSystem.output, dotProduct,
      Fin.sum_univ_two]⟩

example : integrator.HasPerfectAdaptation :=
  integrator.hasPerfectAdaptation_of_hasIntegralFeedback
    ⟨![0, 1], fun x u ↦ by
      simp [integrator, LinearSystem.field, LinearSystem.output, dotProduct,
        Fin.sum_univ_two]⟩

/-- `ẋ = -x + u`, `y = x`: the output settles at `u`, so there is no perfect adaptation. -/
def leaky : LinearSystem (Fin 1) where
  A := !![-1]
  b := ![1]
  c := ![1]
  d := 0

example : ¬ leaky.HasPerfectAdaptation := by
  intro h
  have := h 1 ![1] (by
    ext i; fin_cases i; simp [leaky, LinearSystem.field])
  simp [leaky, LinearSystem.output, dotProduct] at this

/-- Hence (`A` is nonsingular) `leaky` has no integral-feedback functional. -/
example : ¬ leaky.HasIntegralFeedback := fun h ↦ by
  have := leaky.hasPerfectAdaptation_of_hasIntegralFeedback h
  have h1 := this 1 ![1] (by
    ext i; fin_cases i; simp [leaky, LinearSystem.field])
  simp [leaky, LinearSystem.output, dotProduct] at h1

example : IsUnit leaky.A.det := by simp [leaky]

/-- The nonlinear theorem applies with a genuine differentiable `z`: the zero
field has every point as an equilibrium and the zero output. -/
example (p : Unit) (x : ℝ) (hx : (fun _ _ : ℝ => (0 : ℝ)) p x = 0) : (0 : ℝ) = 0 :=
  output_eq_zero_of_integral_feedback (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
    (fun _ => (0 : ℝ)) (fun _ => 0) (fun _ _ => rfl) (fun _ => hasFDerivAt_const _ _) hx

end MathlibExtTest.Biology.Dynamics.IntegralFeedback
