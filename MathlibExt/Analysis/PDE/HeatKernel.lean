/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The fundamental solution of the heat equation

On a finite-dimensional real inner product space `E` of dimension `n`, the heat kernel is
`Φ(t, x) = (4 π t)^{-n/2} exp(-‖x‖² / (4 t))`. For `t > 0` it is positive, it is integrable with
total mass `1`, and it solves the heat equation `∂ₜ Φ = Δ Φ`, with both sides equal to
`Φ (‖x‖² / (4 t²) - n / (2 t))`. The Laplacian is Mathlib's `InnerProductSpace.laplacian`, and the
mass computation reduces to Mathlib's Gaussian integral
`GaussianFourier.integral_rexp_neg_mul_sq_norm`.

## Main results

* `heatKernel`: the fundamental solution `Φ(t, x)`.
* `integral_heatKernel`: `∫ Φ(t, x) dx = 1` for `t > 0`.
* `laplacian_heatKernel`, `hasDerivAt_heatKernel_time`: the two sides of the heat equation.
* `heatKernel_hasDerivAt_time_eq_laplacian`: `∂ₜ Φ = Δ Φ` for `t > 0`.

The one-dimensional statement that the convolution of `Φ` with bounded continuous data solves the
heat equation with that initial datum is recorded as wanted in
`WantedExt.Analysis.HeatKernelWanted`.

## References

* M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025,
  Chapter 4 (Heat equation),
  https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf: Definition
  4.1 and Lemma 4.2.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS Graduate Studies in Mathematics 19
  (2010), Chapter 2 (fundamental solution of the heat equation). The book was not available to
  this formalization; theorem numbers are not cited from it.
-/

@[expose] public section

open InnerProductSpace Filter Topology Set Laplacian MeasureTheory Real
open scoped RealInnerProductSpace

namespace MathlibExt.Analysis.PDE.HeatKernel

open MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Fundamental solution of the heat equation.** On a real inner product space `E` of finite
dimension `n`, `heatKernel E t x = (4 π t)^{-n/2} exp(-‖x‖² / (4 t))`
(M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025,
Chapter 4, Definition 4.1; Evans, *Partial Differential Equations*, 2nd ed., Chapter 2). Only
`t > 0` is meaningful; the formula is not set to `0` for `t < 0` as in Definition 4.1. -/
noncomputable def heatKernel (t : ℝ) (x : E) : ℝ :=
  (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * exp (-‖x‖ ^ 2 / (4 * t))

variable {E}

/-- **The heat kernel is positive.** For `t > 0` and every `x`, `Φ(t, x) > 0`
(immediate from Definition 4.1 of M. Schmidt, *Partial Differential Equations*, lecture notes,
Universität Mannheim, HWS 2025, Chapter 4). -/
theorem heatKernel_pos {t : ℝ} (ht : 0 < t) (x : E) : 0 < heatKernel E t x := by
  unfold heatKernel
  have : 0 < 4 * π * t := by positivity
  positivity

/-- **Time derivative of the heat kernel.** For `t > 0`,
`∂ₜ Φ(t, x) = Φ(t, x) (‖x‖² / (4 t²) - n / (2 t))` where `n` is the dimension: one side of the
heat equation for the fundamental solution (Evans, *Partial Differential Equations*, 2nd ed.,
Chapter 2; M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim,
HWS 2025, Chapter 4, §4.1). -/
theorem hasDerivAt_heatKernel_time {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => heatKernel E s x)
      (heatKernel E t x * (‖x‖ ^ 2 / (4 * t ^ 2) - Module.finrank ℝ E / (2 * t))) t := by
  set p : ℝ := -(Module.finrank ℝ E : ℝ) / 2
  have h4 : HasDerivAt (fun s : ℝ => 4 * π * s) (4 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (4 * π)
  have hpow := h4.rpow_const (p := p) (Or.inl (by positivity))
  have hexp : HasDerivAt (fun s : ℝ => exp (-‖x‖ ^ 2 / (4 * s)))
      (exp (-‖x‖ ^ 2 / (4 * t)) * (‖x‖ ^ 2 / (4 * t ^ 2))) t := by
    have hinv : HasDerivAt (fun s : ℝ => -‖x‖ ^ 2 / (4 * s)) (‖x‖ ^ 2 / (4 * t ^ 2)) t := by
      have := ((hasDerivAt_id t).const_mul 4).inv (by simp [ht.ne'])
      convert this.const_mul (-‖x‖ ^ 2) using 1
      · funext s; simp [div_eq_mul_inv]
      · simp; field_simp
    exact hinv.exp
  have := hpow.mul hexp
  unfold heatKernel
  convert this using 1
  have hpos : 0 < 4 * π * t := by positivity
  rw [rpow_sub_one hpos.ne']
  simp only [p]
  field_simp
  ring

variable [FiniteDimensional ℝ E]

/-- Second derivative at `0` of `s ↦ c exp(α + β s + γ s²)`. -/
private theorem deriv_deriv_mul_exp_quadratic (c α β γ : ℝ) :
    deriv (deriv fun s : ℝ => c * exp (α + β * s + γ * s ^ 2)) 0 =
      c * exp α * (β ^ 2 + 2 * γ) := by
  have hq : ∀ s : ℝ, HasDerivAt (fun s : ℝ => α + β * s + γ * s ^ 2) (β + 2 * γ * s) s := by
    intro s
    have := (((hasDerivAt_id s).const_mul β).const_add α).add
      (((hasDerivAt_id s).pow 2).const_mul γ)
    convert this using 1
    · funext x; simp [add_assoc]
    · simp; ring
  have hd : deriv (fun s : ℝ => c * exp (α + β * s + γ * s ^ 2)) =
      fun s => c * exp (α + β * s + γ * s ^ 2) * (β + 2 * γ * s) := by
    funext s
    have := ((hq s).exp).const_mul c
    rw [this.deriv]; ring
  rw [hd]
  have h2 : HasDerivAt (fun s : ℝ => c * exp (α + β * s + γ * s ^ 2) * (β + 2 * γ * s))
      (c * (exp (α + β * 0 + γ * 0 ^ 2) * (β + 2 * γ * 0)) * (β + 2 * γ * 0) +
        c * exp (α + β * 0 + γ * 0 ^ 2) * (2 * γ)) 0 := by
    have hl := ((hq 0).exp).const_mul c
    have hr : HasDerivAt (fun s : ℝ => β + 2 * γ * s) (2 * γ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (2 * γ)).const_add β
    exact hl.mul hr
  rw [h2.deriv]
  simp; ring

/-- **Laplacian of the heat kernel.** For `t > 0`,
`Δ Φ(t, ·)(x) = Φ(t, x) (‖x‖² / (4 t²) - n / (2 t))` where `n` is the dimension, computed from
second derivatives along an orthonormal basis (Evans, *Partial Differential Equations*, 2nd ed.,
Chapter 2; M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim,
HWS 2025, Chapter 4, §4.1). -/
theorem laplacian_heatKernel {t : ℝ} (ht : 0 < t) (x : E) :
    Δ (heatKernel E t) x =
      heatKernel E t x * (‖x‖ ^ 2 / (4 * t ^ 2) - Module.finrank ℝ E / (2 * t)) := by
  have hsmooth : ContDiff ℝ 2 (heatKernel E t) := by
    have hq : ContDiff ℝ 2 fun x : E => -‖x‖ ^ 2 / (4 * t) :=
      (contDiff_norm_sq ℝ).neg.div_const _
    exact contDiff_const.mul hq.exp
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  set c := (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)
  have key : ∀ e : E, ‖e‖ = 1 → iteratedFDeriv ℝ 2 (heatKernel E t) x ![e, e] =
      heatKernel E t x * (inner ℝ x e ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
    intro e he
    rw [iteratedFDeriv_two_apply_eq_deriv_deriv hsmooth.contDiffAt e]
    have hline : (fun s : ℝ => heatKernel E t (x + s • e)) = fun s =>
        c * exp (-‖x‖ ^ 2 / (4 * t) + (-(inner ℝ x e) / (2 * t)) * s +
          (-1 / (4 * t)) * s ^ 2) := by
      funext s
      unfold heatKernel
      congr 2
      rw [norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs, he]
      field_simp
      ring
    rw [hline, deriv_deriv_mul_exp_quadratic,
      show heatKernel E t x = c * exp (-‖x‖ ^ 2 / (4 * t)) from rfl]
    field_simp
    ring
  have hb := (stdOrthonormalBasis ℝ E).sum_sq_inner_left x
  simp only [fun i => key _ ((stdOrthonormalBasis ℝ E).norm_eq_one i)]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, hb]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The heat kernel solves the heat equation.** For `t > 0` and every `x`, the time derivative of
`s ↦ Φ(s, x)` at `t` is the Laplacian of `Φ(t, ·)` at `x`: `∂ₜ Φ = Δ Φ` on `(0, ∞) × E`
(Evans, *Partial Differential Equations*, 2nd ed., Chapter 2; M. Schmidt, *Partial Differential
Equations*, lecture notes, Universität Mannheim, HWS 2025, Chapter 4, §4.1). -/
theorem heatKernel_hasDerivAt_time_eq_laplacian {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => heatKernel E s x) (Δ (heatKernel E t) x) t := by
  rw [laplacian_heatKernel ht]
  exact hasDerivAt_heatKernel_time ht x

variable [MeasurableSpace E] [BorelSpace E]

/-- **The heat kernel has total mass one.** For `t > 0`, `∫_E Φ(t, x) dx = 1`, for the volume
of the inner product space (Lebesgue measure on `ℝⁿ`): Lemma 4.2 of M. Schmidt, *Partial
Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, Chapter 4. -/
theorem integral_heatKernel {t : ℝ} (ht : 0 < t) : ∫ x, heatKernel E t x = 1 := by
  unfold heatKernel
  rw [integral_const_mul]
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (b := 1 / (4 * t))
    (by positivity)
  have hfun : (fun x : E => exp (-‖x‖ ^ 2 / (4 * t))) =
      fun x => exp (-(1 / (4 * t)) * ‖x‖ ^ 2) := by
    funext x; congr 1; ring
  rw [hfun, h]
  have hpi : π / (1 / (4 * t)) = 4 * π * t := by field_simp
  rw [hpi, ← rpow_add (by positivity)]
  rw [show -(Module.finrank ℝ E : ℝ) / 2 + (Module.finrank ℝ E : ℝ) / 2 = 0 by ring, rpow_zero]

/-- **The heat kernel is integrable.** For `t > 0`, `x ↦ Φ(t, x)` is Lebesgue integrable, since
its integral is `1 ≠ 0` (M. Schmidt, *Partial Differential Equations*, lecture notes, Universität
Mannheim, HWS 2025, Chapter 4, Lemma 4.2). -/
theorem integrable_heatKernel {t : ℝ} (ht : 0 < t) : Integrable (heatKernel E t) :=
  Integrable.of_integral_ne_zero (by rw [integral_heatKernel ht]; exact one_ne_zero)

end MathlibExt.Analysis.PDE.HeatKernel
