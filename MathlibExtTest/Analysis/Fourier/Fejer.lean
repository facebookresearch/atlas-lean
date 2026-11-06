/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.Fejer

set_option autoImplicit false

open Filter Topology MathlibExt.Analysis.Fourier

-- `σ_0 = S_0` is the constant term `f̂_0`.
example (f : ℝ → ℂ) (x : ℝ) :
    fourierCesaroMean f 0 x = fourierCoeffOn Real.two_pi_pos f 0 := by
  simp [fourierCesaroMean, fourierPartialSum]

-- Fejér's theorem for the character `x ↦ e^{ix}`.
example :
    TendstoUniformly (fun N : ℕ => fourierCesaroMean (fun x : ℝ => Complex.exp (x * Complex.I)) N)
      (fun x : ℝ => Complex.exp (x * Complex.I)) atTop :=
  tendstoUniformly_fourierCesaroMean
    (fun x => by
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one])
    (by fun_prop)

-- Uniform convergence gives convergence at every point.
example {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi)) (hcont : Continuous f) (x : ℝ) :
    Tendsto (fun N : ℕ => fourierCesaroMean f N x) atTop (𝓝 (f x)) :=
  (tendstoUniformly_fourierCesaroMean hper hcont).tendsto_at x

#print axioms tendstoUniformly_fourierCesaroMean
