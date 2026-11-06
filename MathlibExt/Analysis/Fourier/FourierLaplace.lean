/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# Entire Fourier–Laplace transform on the real line

This module defines the complex-parameter entire extension of the real Fourier
integral in the `exp (-2π i x z)` convention and identifies its restriction to
the real axis with Mathlib's `2π`-normalised Fourier transform.

The motivating source is

* [M. Pandey and M. Radziwiłł, *L¹ means of exponential sums with multiplicative
  coefficients. I*](https://arxiv.org/abs/2307.10329) — the Fourier-transform
convention of §2 and the uses of the entire extension of a compactly supported
function in §3.

For a compactly supported integrable `f : ℝ → ℂ` the integral

```
fourierLaplace f z = ∫ x, f x * exp (-2π I x z)
```

is entire in `z : ℂ`. On the real axis it agrees with the Mathlib Fourier
integral `fourierIntegral Real.fourierChar volume f`.
-/

open MeasureTheory
open scoped FourierTransform

namespace Fourier

/-- **Fourier–Laplace transform.** For $f : \mathbb{R} \to \mathbb{C}$ and $z \in \mathbb{C}$,
the Fourier–Laplace transform of $f$ at $z$ is the Lebesgue integral
$\int_{\mathbb{R}} f(x) \, e^{-2\pi i x z} \, dx$, taken to be $0$ when the integrand is not
integrable. -/
noncomputable def fourierLaplace (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * z)

/-- **Fourier–Laplace transform on the real axis.** For every $f : \mathbb{R} \to \mathbb{C}$
and every real $r$, the Fourier–Laplace transform of $f$ at the complex number $r$, namely
$\int_{\mathbb{R}} f(x) \, e^{-2\pi i x r} \, dx$, equals the Fourier transform of $f$ at $r$
with the $2\pi$ normalization, $\hat f(r) = \int_{\mathbb{R}} e^{-2\pi i x r} f(x) \, dx$. -/
theorem fourierLaplace_ofReal (f : ℝ → ℂ) (r : ℝ) :
    fourierLaplace f (r : ℂ) = Fourier.fourierIntegral Real.fourierChar volume f r := by
  rw [fourierLaplace, Fourier.fourierIntegral_def]
  apply integral_congr_ae
  filter_upwards with x
  -- Goal: `f x * exp (-2π I x r) = (𝐞 (-(x * r)) : ℂ) * f x`
  change f x * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (r : ℂ)) =
    (↑(𝐞 (-(x * r))) : ℂ) * f x
  rw [Real.fourierChar_apply]
  rw [mul_comm (f x)]
  congr 2
  push_cast
  ring

/-- **Derivative of the Fourier–Laplace transform.** Let $f : \mathbb{R} \to \mathbb{C}$ be
integrable with compact support, and let $F(z) = \int_{\mathbb{R}} f(x) \, e^{-2\pi i x z} \, dx$
be its Fourier–Laplace transform. Then at every $z \in \mathbb{C}$, $F$ is complex differentiable
with derivative $F'(z) = \int_{\mathbb{R}} f(x) \, (-2\pi i x) \, e^{-2\pi i x z} \, dx$. -/
theorem hasDerivAt_fourierLaplace {f : ℝ → ℂ} (hf : Integrable f)
    (hfc : HasCompactSupport f) (z : ℂ) :
    HasDerivAt (fourierLaplace f)
      (∫ x : ℝ, f x * ((-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * z))) z := by
  -- The topological support of `f` is compact, hence bounded; choose `R` with
  -- `tsupport f ⊆ ball 0 R`.
  obtain ⟨R, hRpos, hR⟩ := hfc.isCompact.isBounded.subset_ball_lt 0 (0 : ℝ)
  let a : ℝ → ℂ := fun x => -2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)
  let F : ℂ → ℝ → ℂ := fun w x => f x * Complex.exp (a x * w)
  let F' : ℂ → ℝ → ℂ := fun w x => f x * (a x * Complex.exp (a x * w))
  let C : ℝ := 2 * Real.pi * R * Real.exp (2 * Real.pi * R * (‖z‖ + 1))
  have hnorm_a {x : ℝ} (hx : f x ≠ 0) : ‖a x‖ ≤ 2 * Real.pi * R := by
    rw [show ‖a x‖ = 2 * Real.pi * ‖x‖ by simp [a, abs_of_nonneg Real.pi_nonneg]]
    gcongr
    exact (mem_ball_zero_iff.1 (hR (subset_tsupport f hx))).le
  have hnorm_exp {w : ℂ} (hw : w ∈ Metric.ball z 1) {x : ℝ} (hx : f x ≠ 0) :
      ‖Complex.exp (a x * w)‖ ≤ Real.exp (2 * Real.pi * R * (‖z‖ + 1)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      (a x * w).re ≤ ‖a x * w‖ := Complex.re_le_norm _
      _ = ‖a x‖ * ‖w‖ := norm_mul _ _
      _ ≤ (2 * Real.pi * R) * (‖z‖ + 1) := by
        gcongr
        · exact hnorm_a hx
        · have hw' : ‖w - z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
          exact le_of_lt <| calc
            ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
            _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
            _ < 1 + ‖z‖ := by linarith
            _ = ‖z‖ + 1 := add_comm _ _
  have hF_int : Integrable (F z) := by
    refine (hf.norm.const_mul (Real.exp (2 * Real.pi * R * (‖z‖ + 1)))).mono'
      (hf.1.mul (by fun_prop)) ?_
    filter_upwards with x
    by_cases hx : f x = 0
    · simp [F, hx]
    · simp only [F, norm_mul]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hnorm_exp (Metric.mem_ball_self zero_lt_one) hx)
          (norm_nonneg (f x))
  have hF'_meas : AEStronglyMeasurable (F' z) :=
    hf.1.mul (by fun_prop)
  have hbound_int : Integrable (fun x => C * ‖f x‖) :=
    hf.norm.const_mul C
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := F') (bound := fun x => C * ‖f x‖)
    (Metric.ball_mem_nhds z zero_lt_one)
    (Filter.Eventually.of_forall fun w => hf.1.mul (by fun_prop)) hF_int hF'_meas
    (by
      filter_upwards with x
      intro w hw
      by_cases hx : f x = 0
      · simp [F', hx]
      · simp only [F', norm_mul]
        calc
          ‖f x‖ * (‖a x‖ * ‖Complex.exp (a x * w)‖)
              ≤ ‖f x‖ * ((2 * Real.pi * R) *
                Real.exp (2 * Real.pi * R * (‖z‖ + 1))) := by
                gcongr
                · exact hnorm_a hx
                · exact hnorm_exp hw hx
          _ = C * ‖f x‖ := by ring)
    hbound_int
    (Filter.Eventually.of_forall fun x w _ => by
      dsimp only [F, F']
      have hax : HasDerivAt (fun y : ℂ => a x * y) (a x) w := by
        simpa using (hasDerivAt_id w).const_mul (a x)
      simpa [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using
        ((Complex.hasDerivAt_exp (a x * w)).comp w hax).const_mul (f x))
  -- `hmain` is stated for `∫ x, F w x`; unfold it to the `fourierLaplace` form.
  change HasDerivAt
    (fun w => ∫ x : ℝ, f x *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * w)) _ z
  simpa [F, F', a] using hmain.2

/-- **The Fourier–Laplace transform of an integrable compactly supported function is entire.**
Let $f : \mathbb{R} \to \mathbb{C}$ be integrable with compact support. Then its Fourier–Laplace
transform $z \mapsto \int_{\mathbb{R}} f(x) \, e^{-2\pi i x z} \, dx$ is complex differentiable
at every $z \in \mathbb{C}$, that is, it is entire. -/
theorem differentiable_fourierLaplace {f : ℝ → ℂ} (hf : Integrable f)
    (hfc : HasCompactSupport f) : Differentiable ℂ (fourierLaplace f) := by
  intro z
  exact (hasDerivAt_fourierLaplace hf hfc z).differentiableAt

@[simp]
theorem fourierLaplace_zero (f : ℝ → ℂ) : fourierLaplace f 0 = ∫ x, f x := by
  simp [fourierLaplace]

@[simp]
theorem fourierLaplace_zero_function (z : ℂ) : fourierLaplace (0 : ℝ → ℂ) z = 0 := by
  simp [fourierLaplace]

end Fourier
