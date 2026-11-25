/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.DedekindEtaExpLog

@[expose] public section

-- Consumer with the original binders.
example (z : UpperHalfPlane) :
    Complex.exp (Real.pi * Complex.I * (z : ℂ) / 12 +
      ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z : ℂ))) =
      ModularForm.eta z :=
  ModularForm.exp_logEta z

-- The upper half-plane hypothesis matters: at `z = 0`, outside the upper
-- half-plane, the factor `η_q 0 0` has norm `1`, so the logarithm series
-- is not controlled by the geometric bound used on the half-plane.
example : ¬ ‖ModularForm.eta_q 0 (0 : ℂ)‖ < 1 := by
  rw [ModularForm.eta_q_eq_cexp]
  simp
