/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# First-moment comparison from cross products

Integrating a pointwise cross-product inequality twice orders the products of
first and zeroth moments. The proof requires only integrability of each density
and its first moment; no positivity or probability normalization is assumed.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.MeasureTheory

/-- A cross-product order implies the corresponding first-moment order. -/
theorem firstMoment_mul_integral_le {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hyf : Integrable (fun y => y * f y) μ) (hyg : Integrable (fun y => y * g y) μ)
    (h : ∀ y z, 0 ≤ (y - z) * (f y * g z - f z * g y)) :
    (∫ y, f y ∂μ) * (∫ y, y * g y ∂μ) ≤ (∫ y, y * f y ∂μ) * (∫ y, g y ∂μ) := by
  have linearity {a b c d : ℝ → ℝ} (ha : Integrable a μ) (hb : Integrable b μ)
      (hc : Integrable c μ) (hd : Integrable d μ) :
      (∫ y, a y - b y + c y - d y ∂μ) =
        (∫ y, a y ∂μ) - (∫ y, b y ∂μ) + (∫ y, c y ∂μ) - (∫ y, d y ∂μ) := by
    have hab : Integrable (fun y => a y - b y) μ := by
      simpa only [Pi.sub_apply] using! ha.sub hb
    have habc : Integrable (fun y => a y - b y + c y) μ := by
      simpa only [Pi.add_apply] using! hab.add hc
    rw [integral_sub habc hd, integral_add hab hc, integral_sub ha hb]
  have hi (y : ℝ) : 0 ≤ y * f y * (∫ z, g z ∂μ) - f y * (∫ z, z * g z ∂μ) +
      g y * (∫ z, z * f z ∂μ) - y * g y * (∫ z, f z ∂μ) := by
    have hh : 0 ≤ ∫ z, (y * f y * g z - f y * (z * g z) +
        g y * (z * f z) - y * g y * f z) ∂μ := integral_nonneg (fun z => by
      change 0 ≤ y * f y * g z - f y * (z * g z) + g y * (z * f z) - y * g y * f z
      convert h y z using 1
      ring)
    rw [linearity (hg.const_mul (y * f y)) (hyg.const_mul (f y))
      (hyf.const_mul (g y)) (hf.const_mul (y * g y))] at hh
    simpa only [integral_const_mul] using hh
  have hh : 0 ≤ ∫ y, (y * f y * (∫ z, g z ∂μ) - f y * (∫ z, z * g z ∂μ) +
      g y * (∫ z, z * f z ∂μ) - y * g y * (∫ z, f z ∂μ)) ∂μ := integral_nonneg hi
  rw [linearity (hyf.mul_const (∫ z, g z ∂μ)) (hf.mul_const (∫ z, z * g z ∂μ))
    (hg.mul_const (∫ z, z * f z ∂μ)) (hyg.mul_const (∫ z, f z ∂μ))] at hh
  simp only [integral_mul_const] at hh
  nlinarith

end MathlibExt.MeasureTheory
