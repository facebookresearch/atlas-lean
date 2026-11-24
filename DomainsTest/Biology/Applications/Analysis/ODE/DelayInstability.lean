/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.DelayInstability
import Domains.Biology.Dynamics.DelayedLogistic

/-! The characteristic root beyond the Hutchinson critical delay. -/

namespace MathlibExtTest.Analysis.ODE.DelayInstability

open Set MathlibExt.Analysis.ODE.DelayInstability

open MathlibExt.Biology.Dynamics.DelayedLogistic in
/-- Hutchinson's linearization `u'(t) = -r u(t - τ)` with `τ > π / (2r)`: a root of
`DelayedLogistic.charFun` with positive real part is a characteristic root of
`pointDelay hτ 0 (-r)`, i.e. it supplies the spectral hypothesis of
`exists_escape_of_charRoot`. -/
theorem hutchinson_unstable_charRoot {r τ : ℝ} (hr : 0 < r) (hτc : criticalDelay r < τ)
    (hτ : 0 ≤ τ) : ∃ κ : ℂ, 0 < κ.re ∧
      pointDelay hτ (0 : ℂ →L[ℂ] ℂ) (-(r : ℂ) • ContinuousLinearMap.id ℂ ℂ)
        (expSegment τ κ 1) = κ • (1 : ℂ) := by
  obtain ⟨z, hz, hre, -⟩ := exists_charFun_eq_zero_re_pos hr hτc
  refine ⟨z, hre, ?_⟩
  rw [pointDelay_expSegment, show -(τ : ℂ) * z = -(z * τ) by ring]
  simp only [charFun] at hz
  simp only [zero_apply, zero_add, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    mul_one]
  linear_combination -hz

end MathlibExtTest.Analysis.ODE.DelayInstability
