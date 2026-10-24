/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import MathlibExt.Analysis.Complex.HarmonicAnnulusMean

set_option autoImplicit false

-- `log ‖z‖` is harmonic away from `0`, so it qualifies on every annulus around `0`.
example {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) :
    ∃ α β : ℝ, ∀ r ∈ Set.Icc r₁ r₂,
      Real.circleAverage (fun z : ℂ => Real.log ‖z‖) 0 r = α * Real.log r + β :=
  InnerProductSpace.HarmonicOnNhd.exists_circleAverage_eq_mul_log_add
    (fun z hz => analyticAt_id.harmonicAt_log_norm
      (by
        intro h
        have hz1 := hz.1
        rw [show z = 0 from h, sub_zero, norm_zero] at hz1
        linarith)) hr₁

-- An entire real part is harmonic everywhere.
example (z₀ : ℂ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) :
    ∃ α β : ℝ, ∀ r ∈ Set.Icc r₁ r₂,
      Real.circleAverage (fun z : ℂ => z.re) z₀ r = α * Real.log r + β :=
  InnerProductSpace.HarmonicOnNhd.exists_circleAverage_eq_mul_log_add
    (fun _ _ => analyticAt_id.harmonicAt_re) hr₁

#print axioms InnerProductSpace.HarmonicOnNhd.exists_circleAverage_eq_mul_log_add
