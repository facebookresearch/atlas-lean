/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Sinc kernel of a frequency band

The integral of `e^{2πiνs}` over the symmetric frequency band
`[-1/(2T), 1/(2T)]` is `T⁻¹ * Real.sinc (π s / T)`, the shared kernel behind
bandlimited reconstruction: it is `1 / T` at `s = 0` and vanishes at
`s = n * T` for nonzero integers `n`. `Real.sinc` is unnormalized
(`sin x / x`, value `1` at `0`), so the factor `π` is explicit. Mathlib also
has the equivalent unparametrized form `integral_exp_mul_I_eq_sinc`
(`∫ t in -r..r, Complex.exp (t * Complex.I) = 2 * r * sinc r`); the statement
here is the band/sample-period form consumers use.

Roadmap leaf `SSC-U11.T07`, clauses `SSC-U11.c03`, `SSC-U11.c04`.
-/

open MeasureTheory intervalIntegral

@[expose] public section

namespace ControlTheory

/-- Shared sinc-kernel identity (roadmap leaf `SSC-U11.T07`, clauses
`SSC-U11.c03`, `SSC-U11.c04`): for `T > 0` and real `s`, the integral of the
complex exponential `e^{2πiνs}` over the band `[-1/(2T), 1/(2T)]` equals
`T⁻¹ * Real.sinc (π s / T)`, where `Real.sinc x = sin x / x` (value `1` at
`0`) has no factor of `π`, so the `π` here is explicit. -/
theorem integral_cexp_band_eq_sinc {T s : ℝ} (hT : 0 < T) :
    (∫ ν in (-(1 / (2 * T)))..(1 / (2 * T)),
      Complex.exp (2 * Real.pi * Complex.I * ν * s)) =
      ((T⁻¹ * Real.sinc (Real.pi * s / T) : ℝ) : ℂ) := by
  have hT' : T ≠ 0 := ne_of_gt hT
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  by_cases hs : s = 0
  · subst hs
    have harg : ∀ ν : ℝ, (2 * Real.pi * Complex.I * (ν : ℂ) * ((0 : ℝ) : ℂ)) = 0 := by
      intro ν
      simp
    simp_rw [harg]
    simp only [Complex.exp_zero]
    rw [intervalIntegral.integral_const, Complex.real_smul, mul_one,
      Complex.ofReal_inj]
    have h0 : Real.pi * (0 : ℝ) / T = 0 := by simp
    rw [h0, Real.sinc_zero, mul_one]
    field_simp
    ring
  · set c : ℂ := 2 * Real.pi * Complex.I * s with hc_def
    have hc : c ≠ 0 := by
      rw [hc_def]
      simp [hpi, hs]
    have hfun : (fun ν : ℝ => Complex.exp (2 * Real.pi * Complex.I * ν * s))
        = (fun ν : ℝ => Complex.exp (c * ν)) := by
      funext ν
      congr 1
      rw [hc_def]
      ring
    rw [hfun, integral_exp_mul_complex hc]
    set θ : ℝ := Real.pi * s / T with hθ_def
    have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT'
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    have hpic : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi
    have hb : c * ((1 / (2 * T) : ℝ) : ℂ) = θ * Complex.I := by
      rw [hc_def, hθ_def]
      push_cast
      field_simp
    have ha : c * (((-(1 / (2 * T))) : ℝ) : ℂ) = -θ * Complex.I := by
      rw [hc_def, hθ_def]
      push_cast
      field_simp
    rw [hb, ha]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have h2 := Complex.two_sin ((θ : ℝ) : ℂ)
    have hN : Complex.exp (θ * Complex.I) - Complex.exp (-θ * Complex.I)
        = 2 * Complex.sin θ * Complex.I := by
      calc Complex.exp (↑θ * Complex.I) - Complex.exp (-↑θ * Complex.I)
          = (Complex.exp (-↑θ * Complex.I) - Complex.exp (↑θ * Complex.I))
            * (Complex.I * Complex.I) := by rw [hI]; ring
        _ = ((Complex.exp (-↑θ * Complex.I) - Complex.exp (↑θ * Complex.I))
            * Complex.I) * Complex.I := by ring
        _ = (2 * Complex.sin ↑θ) * Complex.I := by rw [← h2]
        _ = 2 * Complex.sin ↑θ * Complex.I := by ring
    rw [hN]
    have hθ : θ ≠ 0 := by
      rw [hθ_def]
      exact div_ne_zero (mul_ne_zero hpi hs) hT'
    have hLHS : 2 * Complex.sin ↑θ * Complex.I / c
        = ((Real.sin θ / (Real.pi * s) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sin, hc_def]
      push_cast
      field_simp
    rw [hLHS, Complex.ofReal_inj, Real.sinc_of_ne_zero hθ, hθ_def]
    field_simp

end ControlTheory
