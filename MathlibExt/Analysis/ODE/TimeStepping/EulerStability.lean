/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic

/-!
# Scalar explicit-Euler stability threshold

For the scalar test equation `x' = lam * x`, one explicit Euler step with step
size `h` multiplies the state by the amplification factor `1 + h * lam`, so the
iterates are `(1 + h * lam) ^ n * x0`. This module records the sharp
absolute-stability threshold: the iterates tend to `0` for every initial value
`x0` if and only if `‖1 + h * lam‖ < 1` (complex `lam`, positive real step `h`),
and in the real decay case `lam < 0` if and only if `h < 2 / |lam|`, with the
boundary `h = 2 / |lam|` (amplification factor `-1`) excluded.

This complements the positivity results in
`MathlibExt.Analysis.ODE.TimeStepping` (`scalarEuler_nonneg`,
`scalarEuler_neg_of_large_step`), which use the factor `1 - lam * h` with
`lam > 0` for the decay equation `x' = -lam * x` and the positivity threshold
`h ≤ 1 / lam`; here the factor is written `1 + h * lam`, so decay is `lam < 0`
and the stability threshold is `2 / |lam|`, distinct from the positivity
threshold. No consistency or matrix/Runge-Kutta stability claim is made.

Roadmap leaf `SSC-U23.T01`, clause `SSC-U23.c02`.
-/

open Filter Topology

@[expose] public section

namespace MathlibExt.Analysis.ODE.TimeStepping

set_option linter.unusedVariables false in
/-- Scalar explicit-Euler stability threshold, complex test equation (roadmap leaf
`SSC-U23.T01`, clause `SSC-U23.c02`): for `lam : ℂ` and a positive real step `h`,
the Euler iterates `(1 + h * lam) ^ n * x0` tend to `0` for every initial value
`x0` if and only if the amplification factor satisfies `‖1 + h * lam‖ < 1`. -/
theorem scalarEuler_complex_tendsto_zero_iff {lam : ℂ} {h : ℝ} (hh : 0 < h) :
    (∀ x0 : ℂ, Tendsto (fun n : ℕ => (1 + (h : ℂ) * lam) ^ n * x0) atTop (𝓝 0)) ↔
      ‖(1 : ℂ) + (h : ℂ) * lam‖ < 1 := by
  constructor
  · intro hall
    have h1 := hall 1
    simp only [mul_one] at h1
    exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp h1
  · intro hnorm x0
    have hpow := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hnorm
    simpa using hpow.mul_const x0

/-- Scalar explicit-Euler stability threshold, real decay case (roadmap leaf
`SSC-U23.T01`, clause `SSC-U23.c02`): for real `lam < 0` and a positive step
`h`, the Euler iterates `(1 + h * lam) ^ n * x0` tend to `0` for every initial
value `x0` if and only if `h < 2 / |lam|`. The boundary `h = 2 / |lam|` (where
the amplification factor is `-1`) is excluded. -/
theorem scalarEuler_real_tendsto_zero_iff {lam h : ℝ} (hlam : lam < 0) (hh : 0 < h) :
    (∀ x0 : ℝ, Tendsto (fun n : ℕ => (1 + h * lam) ^ n * x0) atTop (𝓝 0)) ↔
      h < 2 / |lam| := by
  have hnorm : (∀ x0 : ℝ, Tendsto (fun n : ℕ => (1 + h * lam) ^ n * x0) atTop (𝓝 0)) ↔
      ‖(1 : ℝ) + h * lam‖ < 1 := by
    constructor
    · intro hall
      have h1 := hall 1
      simp only [mul_one] at h1
      exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp h1
    · intro hn x0
      have hpow := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hn
      simpa using hpow.mul_const x0
  rw [hnorm, Real.norm_eq_abs, abs_lt]
  have habs : |lam| = -lam := abs_of_neg hlam
  have habs_pos : 0 < |lam| := abs_pos.mpr (ne_of_lt hlam)
  have hmul_neg : h * lam < 0 := mul_neg_of_pos_of_neg hh hlam
  have hlt1 : 1 + h * lam < 1 := by linarith
  have hmul_abs : h * |lam| = -(h * lam) := by rw [habs]; ring
  constructor
  · intro hcon
    have hl := hcon.1
    rw [lt_div_iff₀ habs_pos, hmul_abs]
    linarith
  · intro hb
    refine ⟨?_, hlt1⟩
    have h2 : h * |lam| < 2 := (lt_div_iff₀ habs_pos).mp hb
    rw [hmul_abs] at h2
    linarith

end MathlibExt.Analysis.ODE.TimeStepping
