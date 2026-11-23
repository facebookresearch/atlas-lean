/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.GilPelaez

/-! # Tests for `MathlibExt.Analysis.GilPelaez`

Gil-Pelaez on a point mass `δ_a`, with the three limits computed from the measure: `1` left of the
atom, `0` right of it, and the mid-p value `½` at the atom (so the formula does not return
`μ(x, ∞)` at an atom). Helpers checked on the same law and at `t = 0`. -/

open MeasureTheory MathlibExt.Analysis.GilPelaez Set Filter Topology

namespace MathlibExtTest.GilPelaez

/-- The Gil-Pelaez partial integral `½ + π⁻¹ ∫₀^T Im(e^{-i t x} φ_μ(t)) / t dt`. -/
noncomputable abbrev gp (μ : Measure ℝ) (x T : ℝ) : ℝ :=
  1 / 2 + Real.pi⁻¹ * ∫ t in (0 : ℝ)..T, (Complex.exp (-(t * x) * Complex.I) * charFun μ t).im / t

/-- At the atom: the limit is the mid-p value `½`, not `δ₀(0, ∞) = 0`. -/
example : Tendsto (gp (Measure.dirac (0 : ℝ)) 0) atTop (𝓝 (1 / 2)) := by
  have h := tendsto_gilPelaez (μ := Measure.dirac (0 : ℝ)) (integrable_dirac (by simp)) 0
  have hv : ((Measure.dirac (0 : ℝ)).real (Ioi 0) + (Measure.dirac (0 : ℝ)).real (Ici 0)) / 2 =
      1 / 2 := by
    simp
  rw [hv] at h
  exact h

/-- Left of the atom (`x < a`) the limit is `1`. -/
example {a x : ℝ} (hx : x < a) : Tendsto (gp (Measure.dirac a) x) atTop (𝓝 1) := by
  have h := tendsto_gilPelaez (μ := Measure.dirac a) (integrable_dirac (by simp)) x
  have hv : ((Measure.dirac a).real (Ioi x) + (Measure.dirac a).real (Ici x)) / 2 = 1 := by
    simp [hx, hx.le]
  rw [hv] at h
  exact h

/-- Right of the atom (`a < x`) the limit is `0`. -/
example {a x : ℝ} (hx : a < x) : Tendsto (gp (Measure.dirac a) x) atTop (𝓝 0) := by
  have h := tendsto_gilPelaez (μ := Measure.dirac a) (integrable_dirac (by simp)) x
  have hv : ((Measure.dirac a).real (Ioi x) + (Measure.dirac a).real (Ici x)) / 2 = 0 := by
    simp [not_lt.2 hx.le, hx]
  rw [hv] at h
  exact h

/-- `∫ sign(y - x) dδ₀(y) = sign(-x)` at `x = 0`: `0 + 1 - 1 = 0`. -/
example : ∫ y, Real.sign (y - 0) ∂(Measure.dirac (0 : ℝ)) = 0 := by
  rw [integral_sign_sub]
  simp

/-- At `t = 0` the imaginary part vanishes on both sides. -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    (Complex.exp (-(0 * x) * Complex.I) * charFun μ 0).im = ∫ y, Real.sin (0 * (y - x)) ∂μ :=
  im_cexp_mul_charFun μ 0 x

example (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ∫ y, Real.sin (0 * (y - x)) ∂μ = 0 := by simp

end MathlibExtTest.GilPelaez
