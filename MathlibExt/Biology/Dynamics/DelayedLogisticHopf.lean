/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.DelayedLogistic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Hopf bifurcation data for the Hutchinson delayed logistic equation

`MathlibExt.Biology.Dynamics.DelayedLogistic` shows that the characteristic function
`charFun r τ z = z + r e^{-z τ}` of the linearization `u'(t) = -r u(t - τ)` about the positive
equilibrium `K` has all roots in `Re z < 0` for `τ < τ_c = π / (2 r)`, has the imaginary pair
`± i r` at `τ = τ_c`, and has a root with `Re z > 0` beyond `τ_c`. This file proves the
remaining spectral hypotheses of the Hopf bifurcation theorem for delay equations at `τ_c`.
It also proves a third-order Poincaré–Lindstedt (normal form) expansion: an approximate
periodic orbit of the nonlinear equation with an `O(ε⁴)` residual.

## Main results

Spectral Hopf hypotheses at `τ = τ_c` (`r > 0`).
* `hasDerivAt_charFun`, `charFunDeriv_criticalDelay`, `charFunDeriv_criticalDelay_ne_zero`:
  `∂_z charFun = 1 + (π / 2) i ≠ 0` at `(i r, τ_c)`, so `i r` is a simple root.
* `eq_I_mul_or_eq_neg_I_mul_of_re_eq_zero`: at `τ_c` the only roots on the imaginary axis are
  `± i r` (in particular no resonant roots `i k r`, `k ≠ ± 1`).
* `re_neg_of_charFun_criticalDelay`: every other root at `τ_c` has negative real part.

Transversal crossing.
* `rootBranch`: the root branch through `i r`, built by the complex inverse function theorem
  from `rootDelay r z = -log (-z / r) / z`, the delay at which `z` is a root.
* `rootBranch_criticalDelay`, `eventually_charFun_rootBranch`: `rootBranch r τ_c = i r`, and
  `rootBranch r τ` is a characteristic root for every `τ` near `τ_c`.
* `hasDerivAt_rootBranch`, `re_inv_rootDelayDeriv`: the branch is differentiable at `τ_c`
  with `Re λ'(τ_c) = r² / (1 + (π / 2)²) > 0`.
* `eventually_rootBranch_re_neg_left`, `eventually_rootBranch_re_pos_right`: the root crosses
  the imaginary axis from left to right as `τ` increases through `τ_c`.

Normal form of the approximate orbit (time scaled by `τ`: `v(s) = x(τ s) / K - 1`, so
`v'(s) = -α v(s - 1) (1 + v(s))` with `α = r τ`, `α_c = π / 2`).
* `hopfProfile`, `hopfApprox`: `W_ε(θ) = ε cos θ + ε² (cos 2θ / 5 + sin 2θ / 10)
  + ε³ (cos 3θ / 80 + 3 sin 3θ / 80)` and `v_ε(s) = W_ε(ω(ε) s)`, with frequency
  `ω(ε) = π / 2 - ε² / 20` (`hopfFreq`) and parameter `α(ε) = π / 2 + (3π - 2) / 40 · ε²`
  (`hopfParam`).
* `exists_hopfApprox_residual_le`: `v_ε` solves the scaled equation up to a residual
  `≤ C ε⁴`, uniformly in time, for `|ε| ≤ 1`.
* `exists_hopfOrbit_residual_le`: the same in the original variables. With delay
  `τ(ε) = α(ε) / r`, the function `x_ε(t) = K (1 + v_ε(t / τ(ε)))` satisfies
  `|x_ε' - r x_ε (1 - x_ε(t - τ(ε)) / K)| ≤ C ε⁴`.
* `hopfApprox_periodic`, `criticalDelay_lt_hopfDelay`, `sq_eq_hopfParam`: `v_ε` is periodic
  with period `2π / ω(ε)`. The approximate orbits live on the unstable side `τ(ε) > τ_c`, with
  amplitude law `ε² = 40 (r τ(ε) - π / 2) / (3π - 2)`.

## Scope

What is proved: the linear Hopf hypotheses (simple imaginary pair, no other imaginary roots,
transversal crossing) and the third-order Poincaré–Lindstedt expansion. The expansion fixes the
direction coefficient `(3π - 2) / 40 > 0` and the frequency shift `-1 / 20`. The `O(ε⁴)`
residual bound is a statement about the nonlinear equation.

What is not proved:
* the existence of a true periodic solution near `v_ε` (the Hopf bifurcation theorem for
  delay equations, via a center manifold or Lyapunov–Schmidt reduction in a space of periodic
  functions);
* the orbital stability of the bifurcating orbit;
* uniqueness of the coefficients: the file does not show that other values of the two
  coefficients leave an `ε³` residual.

## References

* J. K. Hale, S. M. Verduyn Lunel, *Introduction to Functional Differential Equations*,
  Springer (1993), §11.1 (Hopf bifurcation for retarded equations).
* B. D. Hassard, N. D. Kazarinoff, Y.-H. Wan, *Theory and Applications of Hopf Bifurcation*,
  Cambridge University Press (1981), Ch. 4 (the delayed logistic equation).
* H. Smith, *An Introduction to Delay Differential Equations with Applications to the Life
  Sciences*, Springer (2011), §6.2.
-/

@[expose] public section

open Real Filter Set
open scoped Topology

namespace MathlibExt.Biology.Dynamics.DelayedLogisticHopf

open MathlibExt.Biology.Dynamics.DelayedLogistic

theorem criticalDelay_pos {r : ℝ} (hr : 0 < r) : 0 < criticalDelay r := by
  unfold criticalDelay; positivity

theorem mul_criticalDelay {r : ℝ} (hr : 0 < r) : r * criticalDelay r = π / 2 := by
  rw [criticalDelay]; field_simp

/-! ### Simplicity of the imaginary pair at `τ_c` -/

/-- The `z`-derivative `1 - r τ e^{-z τ}` of the characteristic function. -/
noncomputable def charFunDeriv (r τ : ℝ) (z : ℂ) : ℂ := 1 - r * τ * Complex.exp (-(z * τ))

theorem hasDerivAt_charFun (r τ : ℝ) (z : ℂ) :
    HasDerivAt (charFun r τ) (charFunDeriv r τ z) z := by
  have h1 : HasDerivAt (fun w : ℂ => -(w * τ)) (-(1 * (τ : ℂ))) z :=
    ((hasDerivAt_id' z).mul_const (τ : ℂ)).neg
  have h2 := (hasDerivAt_id' z).add (h1.cexp.const_mul (r : ℂ))
  refine h2.congr_deriv ?_
  simp only [charFunDeriv]
  ring

/-- At `(z, τ) = (i r, τ_c)` the derivative is `1 + (π / 2) i`. -/
theorem charFunDeriv_criticalDelay {r : ℝ} (hr : 0 < r) :
    charFunDeriv r (criticalDelay r) (Complex.I * r) = 1 + ((π / 2 : ℝ) : ℂ) * Complex.I := by
  have hrτ : (r : ℂ) * (criticalDelay r : ℂ) = ((π / 2 : ℝ) : ℂ) := by
    exact_mod_cast mul_criticalDelay hr
  have h : -(Complex.I * r * (criticalDelay r : ℂ)) = ((-(π / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast at hrτ ⊢; linear_combination (-Complex.I) * hrτ
  rw [charFunDeriv, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, cos_neg,
    sin_neg, cos_pi_div_two, sin_pi_div_two]
  push_cast at hrτ ⊢
  linear_combination Complex.I * hrτ

/-- **Simplicity**: `i r` is a simple root of the characteristic equation at `τ_c`. -/
theorem charFunDeriv_criticalDelay_ne_zero {r : ℝ} (hr : 0 < r) :
    charFunDeriv r (criticalDelay r) (Complex.I * r) ≠ 0 := by
  rw [charFunDeriv_criticalDelay hr]
  intro h
  have := congrArg Complex.re h
  simp at this

/-- **No other imaginary roots**: at `τ = τ_c` the only characteristic roots with `Re z = 0`
are `± i r`. -/
theorem eq_I_mul_or_eq_neg_I_mul_of_re_eq_zero {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : charFun r (criticalDelay r) z = 0) (hre : z.re = 0) :
    z = Complex.I * r ∨ z = -(Complex.I * r) := by
  have hτ : 0 ≤ criticalDelay r := (criticalDelay_pos hr).le
  obtain ⟨hcos, him⟩ := cos_nonpos_and_abs_im_le hr hτ hz hre.ge
  have hb : |z.im * criticalDelay r| ≤ π / 2 := by
    rw [abs_mul, abs_of_nonneg hτ, ← mul_criticalDelay hr]
    gcongr
  have hcos0 : cos (z.im * criticalDelay r) = 0 :=
    le_antisymm hcos (cos_nonneg_of_mem_Icc ⟨(abs_le.1 hb).1, (abs_le.1 hb).2⟩)
  obtain ⟨-, h2⟩ := charFun_eq_zero_iff.1 hz
  simp only [hre, zero_mul, neg_zero, Real.exp_zero, mul_one] at h2
  have hsq := sin_sq_add_cos_sq (z.im * criticalDelay r)
  rw [hcos0] at hsq
  have hfac : (sin (z.im * criticalDelay r) - 1) * (sin (z.im * criticalDelay r) + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.1 hfac with h | h
  · left
    have hs : sin (z.im * criticalDelay r) = 1 := by linarith
    rw [hs, mul_one] at h2
    refine Complex.ext ?_ ?_ <;> simp [hre]
    linarith
  · right
    have hs : sin (z.im * criticalDelay r) = -1 := by linarith
    rw [hs, mul_neg_one] at h2
    refine Complex.ext ?_ ?_ <;> simp [hre]
    linarith

/-- At `τ_c` every characteristic root other than `± i r` has negative real part. -/
theorem re_neg_of_charFun_criticalDelay {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : charFun r (criticalDelay r) z = 0) (h1 : z ≠ Complex.I * r)
    (h2 : z ≠ -(Complex.I * r)) : z.re < 0 := by
  refine lt_of_le_of_ne (re_nonpos_of_charFun_eq_zero hr (criticalDelay_pos hr).le le_rfl hz)
    fun h => ?_
  rcases eq_I_mul_or_eq_neg_I_mul_of_re_eq_zero hr hz h with h' | h'
  · exact h1 h'
  · exact h2 h'

/-! ### The root branch through `i r` and transversality -/

/-- The delay at which `z` is a characteristic root: `rootDelay r z = -log (-z / r) / z`
(principal logarithm). `rootDelay r z = τ` with `τ ≠ 0` forces `charFun r τ z = 0`. -/
noncomputable def rootDelay (r : ℝ) (z : ℂ) : ℂ := -Complex.log (-z / r) / z

/-- The derivative `(1 + (π / 2) i) / r²` of `rootDelay r` at `i r`. -/
noncomputable def rootDelayDeriv (r : ℝ) : ℂ :=
  ((1 / r ^ 2 : ℝ) : ℂ) + ((π / 2 / r ^ 2 : ℝ) : ℂ) * Complex.I

theorem charFun_eq_zero_of_rootDelay_eq {r τ : ℝ} {z : ℂ} (hr : r ≠ 0) (hτ : τ ≠ 0)
    (h : rootDelay r z = τ) : charFun r τ z = 0 := by
  have hz : z ≠ 0 := by
    rintro rfl
    have h0 : rootDelay r 0 = 0 := by simp [rootDelay]
    rw [h0] at h
    exact hτ (by exact_mod_cast h.symm)
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlog : Complex.log (-z / r) = -(z * τ) := by
    rw [rootDelay, div_eq_iff hz] at h
    linear_combination -h
  have hne : -z / r ≠ 0 := div_ne_zero (neg_ne_zero.2 hz) hr'
  have hexp : Complex.exp (-(z * τ)) = -z / r := by rw [← hlog, Complex.exp_log hne]
  have hmul : (r : ℂ) * (-z / r) = -z := by field_simp
  rw [charFun, hexp, hmul]
  ring

theorem rootDelay_I_mul {r : ℝ} (hr : 0 < r) :
    rootDelay r (Complex.I * r) = (criticalDelay r : ℂ) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hval : -(Complex.I * r) / r = -Complex.I := by field_simp
  rw [rootDelay, hval, Complex.log_neg_I, criticalDelay]
  push_cast
  field_simp

theorem hasStrictDerivAt_rootDelay {r : ℝ} (hr : 0 < r) :
    HasStrictDerivAt (rootDelay r) (rootDelayDeriv r) (Complex.I * r) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hval : -(Complex.I * r) / r = -Complex.I := by field_simp
  have hslit : -(Complex.I * r) / r ∈ Complex.slitPlane := by
    rw [hval]; simp [Complex.mem_slitPlane_iff]
  have hg : HasStrictDerivAt (fun w : ℂ => -w / r) (-1 / r) (Complex.I * r) :=
    (hasStrictDerivAt_id _).neg.div_const _
  have hne : Complex.I * (r : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hr'
  refine ((hg.clog hslit).neg.div (hasStrictDerivAt_id _) hne).congr_deriv ?_
  simp only [id_eq, Pi.neg_apply]
  rw [hval, Complex.log_neg_I, rootDelayDeriv]
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

theorem rootDelayDeriv_ne_zero {r : ℝ} (hr : 0 < r) : rootDelayDeriv r ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [rootDelayDeriv, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.zero_re, mul_zero, zero_mul, sub_zero,
    add_zero] at this
  exact absurd this (by positivity)

/-- **Transversality**: `Re (1 / rootDelay'(i r)) = r² / (1 + (π / 2)²)`. -/
theorem re_inv_rootDelayDeriv {r : ℝ} (hr : 0 < r) :
    (rootDelayDeriv r)⁻¹.re = r ^ 2 / (1 + (π / 2) ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [rootDelayDeriv, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  field_simp
  ring

/-- The characteristic root branch through `i r`, as a function of the delay: the local
inverse of `rootDelay r` at `i r`, evaluated on real delays. -/
noncomputable def rootBranch {r : ℝ} (hr : 0 < r) (τ : ℝ) : ℂ :=
  HasStrictDerivAt.localInverse (rootDelay r) (rootDelayDeriv r) (Complex.I * r)
    (hasStrictDerivAt_rootDelay hr) (rootDelayDeriv_ne_zero hr) τ

theorem rootBranch_criticalDelay {r : ℝ} (hr : 0 < r) :
    rootBranch hr (criticalDelay r) = Complex.I * r := by
  have h := ((hasStrictDerivAt_rootDelay hr).eventually_left_inverse
    (rootDelayDeriv_ne_zero hr)).self_of_nhds
  rw [rootDelay_I_mul hr] at h
  exact h

/-- Near `τ_c`, `rootBranch hr τ` is a root of the characteristic equation with delay `τ`. -/
theorem eventually_charFun_rootBranch {r : ℝ} (hr : 0 < r) :
    ∀ᶠ τ in 𝓝 (criticalDelay r), charFun r τ (rootBranch hr τ) = 0 := by
  have h1 := (hasStrictDerivAt_rootDelay hr).eventually_right_inverse (rootDelayDeriv_ne_zero hr)
  rw [rootDelay_I_mul hr] at h1
  have h2 : Tendsto (fun τ : ℝ => (τ : ℂ)) (𝓝 (criticalDelay r)) (𝓝 (criticalDelay r : ℂ)) :=
    Complex.continuous_ofReal.tendsto _
  filter_upwards [h2.eventually h1, eventually_ne_nhds (criticalDelay_pos hr).ne']
    with τ hτ hτ0
  exact charFun_eq_zero_of_rootDelay_eq hr.ne' hτ0 hτ

theorem hasDerivAt_rootBranch {r : ℝ} (hr : 0 < r) :
    HasDerivAt (rootBranch hr) (rootDelayDeriv r)⁻¹ (criticalDelay r) := by
  have h := (hasStrictDerivAt_rootDelay hr).to_localInverse (rootDelayDeriv_ne_zero hr)
  rw [rootDelay_I_mul hr] at h
  exact h.hasDerivAt.comp_ofReal

/-- **Crossing, left side**: just below `τ_c` the branch lies in `Re z < 0`. -/
theorem eventually_rootBranch_re_neg_left {r : ℝ} (hr : 0 < r) :
    ∀ᶠ τ in 𝓝[<] (criticalDelay r), (rootBranch hr τ).re < 0 := by
  filter_upwards [nhdsWithin_le_nhds (eventually_charFun_rootBranch hr),
    nhdsWithin_le_nhds (lt_mem_nhds (criticalDelay_pos hr)), self_mem_nhdsWithin]
    with τ h1 h2 h3
  exact re_neg_of_charFun_eq_zero hr h2.le h3 h1

/-- **Crossing, right side**: just above `τ_c` the branch lies in `Re z > 0`, since
`Re λ'(τ_c) > 0`. -/
theorem eventually_rootBranch_re_pos_right {r : ℝ} (hr : 0 < r) :
    ∀ᶠ τ in 𝓝[>] (criticalDelay r), 0 < (rootBranch hr τ).re := by
  have hd : HasDerivAt (fun τ => (rootBranch hr τ).re) ((rootDelayDeriv r)⁻¹.re)
      (criticalDelay r) := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (criticalDelay r) (hasDerivAt_rootBranch hr)
    exact this
  have hpos : 0 < (rootDelayDeriv r)⁻¹.re := by rw [re_inv_rootDelayDeriv hr]; positivity
  have h0 : (rootBranch hr (criticalDelay r)).re = 0 := by
    rw [rootBranch_criticalDelay hr]; simp
  have hev := (hasDerivAt_iff_tendsto_slope.1 hd).eventually (lt_mem_nhds hpos)
  have hmono : 𝓝[>] (criticalDelay r) ≤ 𝓝[≠] (criticalDelay r) :=
    nhdsWithin_mono _ fun x hx => ne_of_gt (show criticalDelay r < x from hx)
  filter_upwards [hmono hev, self_mem_nhdsWithin] with τ hτ (hτ' : criticalDelay r < τ)
  simp only [slope_def_field, h0, sub_zero] at hτ
  exact (div_pos_iff_of_pos_right (sub_pos.2 hτ')).1 hτ

/-! ### Third-order Poincaré–Lindstedt expansion: the approximate orbit -/

/-- Direction coefficient: `α(ε) = π / 2 + α₂ ε²` with `α₂ = (3π - 2) / 40`. -/
noncomputable def hopfAlpha2 : ℝ := (3 * π - 2) / 40

/-- Frequency correction: `ω(ε) = π / 2 + ω₂ ε²` with `ω₂ = -1 / 20`. -/
noncomputable def hopfOmega2 : ℝ := -1 / 20

/-- The bifurcation parameter `α(ε) = r τ(ε)` of the scaled equation. -/
noncomputable def hopfParam (ε : ℝ) : ℝ := π / 2 + hopfAlpha2 * ε ^ 2

/-- The angular frequency `ω(ε)` of the approximate orbit in scaled time. -/
noncomputable def hopfFreq (ε : ℝ) : ℝ := π / 2 + hopfOmega2 * ε ^ 2

/-- The `2π`-periodic profile of the approximate orbit, to third order. -/
noncomputable def hopfProfile (ε θ : ℝ) : ℝ :=
  ε * cos (1 * θ) + ε ^ 2 * (cos (2 * θ) / 5 + sin (2 * θ) / 10) +
    ε ^ 3 * (cos (3 * θ) / 80 + 3 * sin (3 * θ) / 80)

/-- The `θ`-derivative of `hopfProfile`. -/
noncomputable def hopfProfileDeriv (ε θ : ℝ) : ℝ :=
  -(ε * sin θ) + ε ^ 2 * (-(2 * sin (2 * θ)) / 5 + cos (2 * θ) / 5) +
    ε ^ 3 * (-(3 * sin (3 * θ)) / 80 + 9 * cos (3 * θ) / 80)

/-- The approximate orbit `v_ε(s) = W_ε(ω(ε) s)` of the scaled equation
`v'(s) = -α v(s - 1) (1 + v(s))`. -/
noncomputable def hopfApprox (ε s : ℝ) : ℝ := hopfProfile ε (hopfFreq ε * s)

/-- `hopfProfile` as a polynomial in `cos θ`, `sin θ`. -/
noncomputable def profilePoly (ε C S : ℝ) : ℝ :=
  ε * C + ε ^ 2 * ((2 * C ^ 2 - 1) / 5 + 2 * S * C / 10) +
    ε ^ 3 * ((4 * C ^ 3 - 3 * C) / 80 + 3 * (3 * S - 4 * S ^ 3) / 80)

/-- `hopfProfileDeriv` as a polynomial in `cos θ`, `sin θ`. -/
noncomputable def profileDerivPoly (ε C S : ℝ) : ℝ :=
  -(ε * S) + ε ^ 2 * (-(2 * (2 * S * C)) / 5 + (2 * C ^ 2 - 1) / 5) +
    ε ^ 3 * (-(3 * (3 * S - 4 * S ^ 3)) / 80 + 9 * (4 * C ^ 3 - 3 * C) / 80)

/-- Divided difference of `profilePoly` in its first argument. -/
noncomputable def profileDiffP (ε C S C' : ℝ) : ℝ :=
  ε + ε ^ 2 * (2 * (C + C') / 5 + S / 5) + ε ^ 3 * ((C ^ 2 + C * C' + C' ^ 2) / 20 - 3 / 80)

/-- Divided difference of `profilePoly` in its second argument. -/
noncomputable def profileDiffQ (ε S C' S' : ℝ) : ℝ :=
  ε ^ 2 * (C' / 5) + ε ^ 3 * (9 / 80 - 3 * (S ^ 2 + S * S' + S' ^ 2) / 20)

theorem profilePoly_sub (ε C S C' S' : ℝ) :
    profilePoly ε C S - profilePoly ε C' S' =
      (C - C') * profileDiffP ε C S C' + (S - S') * profileDiffQ ε S C' S' := by
  simp only [profilePoly, profileDiffP, profileDiffQ]
  ring

/-- The `ε⁴` coefficient of the residual (computed by reducing modulo `cos² + sin² = 1`). -/
noncomputable def residualCoeff (ε c s : ℝ) : ℝ :=
  -3*c^4*π/50 - 2*c^3*π*s/25 + 33*c^2*π/400 + 43*c*π*s/400 + ε^10*(-3*c^6*π/16000000 + c^6/8000000
    + 9*c^5*π*s/64000000 - 3*c^5*s/32000000 + 117*c^4*π/256000000 - 39*c^4/128000000 -
    9*c^3*π*s/64000000 + 3*c^3*s/32000000 - 81*c^2*π/256000000 + 27*c^2/128000000 +
    27*c*π*s/512000000 - 9*c*s/256000000 + 27*π/512000000 - 9/256000000) + ε^9*(-3*c^5*π/32000000 +
    c^5/16000000 + 21*c^4*π*s/32000000 - 7*c^4*s/16000000 + 3*c^3*π/6400000 - c^3/3200000 -
    27*c^2*π*s/32000000 + 9*c^2*s/16000000 - 9*c*π/32000000 + 3*c/16000000 + 9*π*s/32000000 -
    3*s/16000000) + ε^8*(-31*c^6*π/3200000 + 9*c^6/1600000 - 33*c^5*π*s/3200000 + 3*c^5*s/400000 +
    207*c^4*π/12800000 - 7*c^4/800000 + 39*c^3*π*s/2560000 - 69*c^3*s/6400000 - 81*c^2*π/12800000 +
    9*c^2/3200000 - 27*c*π*s/6400000 + 39*c*s/12800000 + 9*π/25600000) + ε^7*(-67*c^5*π/1600000 +
    11*c^5/400000 + 19*c^4*π*s/1600000 - c^4*s/200000 + 41*c^3*π/640000 - 13*c^3/320000 +
    9*c^2*π*s/3200000 - 9*c^2*s/1600000 - 129*c*π/6400000 + 39*c/3200000 + 3*π*s/6400000 +
    3*s/3200000) + ε^6*(27*c^6*π/160000 - 3*c^6/20000 - 39*c^5*π*s/160000 + 9*c^5*s/80000 -
    499*c^4*π/1600000 + 213*c^4/800000 + 1071*c^3*π*s/3200000 - 121*c^3*s/800000 + 561*c^2*π/3200000
    - 217*c^2/1600000 - 891*c*π*s/12800000 + 167*c*s/6400000 - 81*π/5120000 + 27/2560000) +
    ε^5*(-11*c^5*π/16000 + 11*c^5/40000 - 13*c^4*π*s/16000 + 23*c^4*s/40000 + 73*c^3*π/80000 -
    27*c^3/80000 + 123*c^2*π*s/160000 - 19*c^2*s/40000 - 57*c*π/320000 + 3*c/80000 - 39*π*s/320000 +
    3*s/40000) + ε^4*(21*c^6*π/8000 - 3*c^6/4000 + 3*c^5*π*s/8000 - c^5*s/1000 - 237*c^4*π/40000 +
    87*c^4/40000 - 17*c^3*π*s/80000 + 23*c^3*s/20000 + 2269*c^2*π/640000 - 467*c^2/320000 -
    71*c*π*s/640000 - c*s/10000 - 93*π/320000 + 79/640000) + ε^3*(13*c^5*π/4000 - c^5/250 -
    41*c^4*π*s/4000 + 3*c^4*s/1000 - 3*c^3*π/640 + 43*c^3/8000 + 163*c^2*π*s/16000 - 29*c^2*s/8000 +
    123*c*π/64000 - 49*c/32000 - 69*π*s/64000 + 7*s/32000) + ε^2*(3*c^6*π/400 + c^5*π*s/100 -
    123*c^4*π/4000 + 3*c^4/500 - 47*c^3*π*s/2000 + c^3*s/125 + 1007*c^2*π/32000 - 9*c^2/800 +
    13*c*π*s/1600 - 19*c*s/4000 - 403*π/64000 + 27/8000) + ε*(c^5*π/25 - 3*c^4*π*s/100 - 7*c^3*π/80
    + 19*c^2*π*s/400 + 13*c*π/320 - 13*π*s/800 + 3*s/400) - 3*π/160

/-- **The Poincaré–Lindstedt cancellation**: with `α = π / 2 + (3π - 2) / 40 · ε²`,
`ω = π / 2 - ε² / 20` and the phase shift `cos (θ - ω) ≈ c ε² / 20 + s`,
`sin (θ - ω) ≈ s ε² / 20 - c`, the residual of the profile is divisible by `ε⁴` on the unit
circle `c² + s² = 1`. -/
theorem residualPoly_eq (ε c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (π / 2 - ε ^ 2 / 20) * profileDerivPoly ε c s +
        (π / 2 + (3 * π - 2) / 40 * ε ^ 2) *
          profilePoly ε (c * (ε ^ 2 / 20) + s) (s * (ε ^ 2 / 20) - c) *
            (1 + profilePoly ε c s) =
      ε ^ 4 * residualCoeff ε c s := by
  simp only [profilePoly, profileDerivPoly, residualCoeff]
  linear_combination (
      ε^14*(27*c^4*π/128000000 - 9*c^4/64000000 - 9*c^3*π*s/64000000 + 3*c^3*s/32000000 -
      27*c^2*π*s^2/128000000 - 27*c^2*π/102400000 + 9*c^2*s^2/64000000 + 9*c^2/51200000 +
      27*c*π*s/512000000 - 9*c*s/256000000 + 27*π*s^4/128000000 + 27*π*s^2/512000000 +
      27*π/512000000 - 9*s^4/64000000 - 9*s^2/256000000 - 9/256000000) + ε^13*(9*c^3*π/32000000 -
      3*c^3/16000000 - 9*c^2*π*s/16000000 + 3*c^2*s/8000000 - 9*c*π*s^2/32000000 - 9*c*π/32000000 +
      3*c*s^2/16000000 + 3*c/16000000 + 9*π*s/32000000 - 3*s/16000000) + ε^12*(63*c^4*π/6400000 -
      9*c^4/1600000 + 3*c^3*π*s/256000 - 27*c^3*s/3200000 - 9*c^2*π*s^2/1600000 - 153*c^2*π/25600000
      + 9*c^2*s^2/3200000 + 9*c^2/3200000 - 81*c*π*s^3/6400000 - 27*c*π*s/6400000 + 27*c*s^3/3200000
      + 39*c*s/12800000 + 9*π*s^4/6400000 + 9*π*s^2/25600000 + 9*π/25600000) + ε^11*(3*c^3*π/64000 -
      3*c^3/100000 + 3*c^2*π*s/1600000 - 3*c^2*s/800000 - 3*c*π*s^2/400000 - 129*c*π/6400000 +
      3*c*s^2/800000 + 39*c/3200000 + 3*π*s/6400000 + 3*s/3200000) + ε^10*(-27*c^4*π/160000 +
      3*c^4/20000 + 27*c^3*π*s/160000 - 9*c^3*s/160000 + 9*c^2*π*s^2/40000 + 1083*c^2*π/6400000 -
      27*c^2*s^2/160000 - 421*c^2/3200000 - 27*c*π*s^3/160000 - 39*c*π*s/1280000 + 9*c*s^3/160000 -
      81*π*s^2/1280000 - 81*π/5120000 + 27*s^2/640000 + 27/2560000) + ε^9*(27*c^3*π/40000 - c^3/4000
      + 3*c^2*π*s/8000 - 9*c^2*s/40000 - 39*c*π*s^2/80000 - 33*c*π/160000 + 3*c*s^2/10000 +
      9*c/160000 - 9*π*s^3/80000 - 3*π*s/80000 + 3*s^3/40000 + 3*s/160000) + ε^8*(-33*c^4*π/16000 +
      3*c^4/8000 - 3*c^3*π*s/3200 + c^3*s/1000 + 9*c^2*π*s^2/4000 + 979*c^2*π/320000 -
      3*c^2*s^2/8000 - 93*c^2/80000 - 9*c*π*s^3/16000 + 57*c*π*s/80000 - 19*c*s/40000 -
      9*π*s^4/16000 - 9*π*s^2/64000 - 93*π/320000 + 3*s^4/8000 - 3*s^2/16000 + 79/640000) +
      ε^7*(c^3*π/1000 + c^3/1000 + 33*c^2*π*s/4000 - c^2*s/250 + 3*c*π/8000 - c*s^2/500 - c/1600 -
      21*π*s^3/4000 + 3*π*s/16000 + 3*s^3/1000 - s/4000) + ε^6*(-3*c^4*π/800 - c^3*π*s/100 +
      3*c^2*π*s^2/800 + 51*c^2*π/1600 - 27*c^2/2000 + 29*c*π*s/2000 - 13*c*s/2000 - 3*π*s^4/800 -
      3*π*s^2/320 - 119*π/12800 + 3*s^2/400 + 43/8000) + ε^5*(-c^3*π/100 + c^2*π*s/25 + c*π*s^2/50 +
      41*c*π/800 - 3*c/100 - 3*π*s^3/100 + π*s/160 - s/100) + ε^4*(27*c^2*π/200 + 13*c*π*s/200 -
      3*π*s^2/40 - 19*π/800 - 1/50) + ε^3*(3*c*π/10 + π*s/10) + ε^2*π/5) * hcs

theorem hopfProfile_eq (ε θ : ℝ) : hopfProfile ε θ = profilePoly ε (cos θ) (sin θ) := by
  simp only [hopfProfile, profilePoly, one_mul, Real.cos_two_mul, Real.sin_two_mul,
    Real.cos_three_mul, Real.sin_three_mul]

theorem hopfProfileDeriv_eq (ε θ : ℝ) :
    hopfProfileDeriv ε θ = profileDerivPoly ε (cos θ) (sin θ) := by
  simp only [hopfProfileDeriv, profileDerivPoly, Real.cos_two_mul, Real.sin_two_mul,
    Real.cos_three_mul, Real.sin_three_mul]

theorem hasDerivAt_hopfProfile (ε θ : ℝ) :
    HasDerivAt (hopfProfile ε) (hopfProfileDeriv ε θ) θ := by
  have hc : ∀ k : ℝ, HasDerivAt (fun x => cos (k * x)) (-sin (k * θ) * (k * 1)) θ :=
    fun k => ((hasDerivAt_id' θ).const_mul k).cos
  have hs : ∀ k : ℝ, HasDerivAt (fun x => sin (k * x)) (cos (k * θ) * (k * 1)) θ :=
    fun k => ((hasDerivAt_id' θ).const_mul k).sin
  have h := (((hc 1).const_mul ε).add ((((hc 2).div_const 5).add
    ((hs 2).div_const 10)).const_mul (ε ^ 2))).add ((((hc 3).div_const 80).add
    (((hs 3).const_mul 3).div_const 80)).const_mul (ε ^ 3))
  refine h.congr_deriv ?_
  simp only [hopfProfileDeriv, one_mul, mul_one]
  ring

theorem hasDerivAt_hopfApprox (ε s : ℝ) :
    HasDerivAt (hopfApprox ε) (hopfFreq ε * hopfProfileDeriv ε (hopfFreq ε * s)) s := by
  have h := (hasDerivAt_hopfProfile ε (hopfFreq ε * s)).comp s
    ((hasDerivAt_id' s).const_mul (hopfFreq ε))
  refine h.congr_deriv ?_
  ring

/-- A continuous function on `ℝ⁵` is bounded on the cube `[-1, 1]⁵`. -/
theorem exists_bound_box (f : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ) (hf : Continuous f) :
    ∃ M, ∀ a b c d e : ℝ, |a| ≤ 1 → |b| ≤ 1 → |c| ≤ 1 → |d| ≤ 1 → |e| ≤ 1 →
      |f (a, b, c, d, e)| ≤ M := by
  have hK : IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ
      Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod
      (isCompact_Icc.prod isCompact_Icc)))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨M, fun a b c d e ha hb hc hd he => ?_⟩
  have := hM (a, b, c, d, e)
    ⟨abs_le.1 ha, abs_le.1 hb, abs_le.1 hc, abs_le.1 hd, abs_le.1 he⟩
  simpa [Real.norm_eq_abs] using this

theorem abs_cos_sub_one_le {ε : ℝ} : |cos (ε ^ 2 / 20) - 1| ≤ ε ^ 4 := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := ε ^ 2 / 20)
  have h2 := cos_le_one (ε ^ 2 / 20)
  have h4 : 0 ≤ ε ^ 4 := by positivity
  have : (ε ^ 2 / 20) ^ 2 / 2 = ε ^ 4 / 800 := by ring
  rw [abs_le]; constructor <;> linarith

theorem abs_sin_sub_le {ε : ℝ} (he : |ε| ≤ 1) : |sin (ε ^ 2 / 20) - ε ^ 2 / 20| ≤ ε ^ 4 := by
  have hδ : 0 ≤ ε ^ 2 / 20 := by positivity
  have hup : sin (ε ^ 2 / 20) ≤ ε ^ 2 / 20 := Real.sin_le hδ
  have hlow : ε ^ 2 / 20 - (ε ^ 2 / 20) ^ 3 / 6 ≤ sin (ε ^ 2 / 20) := by
    rcases hδ.eq_or_lt with h | h
    · rw [← h]; simp
    · exact (Real.sin_gt_sub_cube h).le
  have he2 : ε ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one ε).2 he
  have h4 : 0 ≤ ε ^ 4 := by positivity
  have h3 : (ε ^ 2 / 20) ^ 3 / 6 ≤ ε ^ 4 := by
    have : (ε ^ 2 / 20) ^ 3 / 6 = ε ^ 4 * ε ^ 2 / 48000 := by ring
    rw [this]; nlinarith
  rw [abs_le]; constructor <;> linarith

theorem abs_add_mul_le {a b u v B : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ B)
    (hv : |v| ≤ B) : |a * u + b * v| ≤ 2 * B := by
  calc |a * u + b * v| ≤ |a * u| + |b * v| := abs_add_le _ _
    _ = |a| * |u| + |b| * |v| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * B + 1 * B := by gcongr
    _ = 2 * B := by ring

/-- **Third-order normal form: the approximate orbit** (scaled time). For `|ε| ≤ 1` the
approximate orbit `v_ε(s) = W_ε(ω(ε) s)` satisfies the scaled delayed logistic equation
`v'(s) = -α(ε) v(s - 1) (1 + v(s))` up to a residual bounded by `C ε⁴`, uniformly in `s`. -/
theorem exists_hopfApprox_residual_le : ∃ C, ∀ ε s : ℝ, |ε| ≤ 1 →
    |deriv (hopfApprox ε) s + hopfParam ε * hopfApprox ε (s - 1) * (1 + hopfApprox ε s)| ≤
      C * ε ^ 4 := by
  obtain ⟨M1, hM1⟩ := exists_bound_box (fun p => residualCoeff p.1 p.2.1 p.2.2.1)
    (by simp only [residualCoeff]; fun_prop)
  obtain ⟨M2, hM2⟩ := exists_bound_box (fun p => hopfParam p.1 *
      (1 + profilePoly p.1 p.2.1 p.2.2.1) *
      profileDiffP p.1 (p.2.2.1 * p.2.2.2.1 + p.2.1 * p.2.2.2.2)
        (p.2.2.1 * p.2.2.2.2 - p.2.1 * p.2.2.2.1) (p.2.1 * (p.1 ^ 2 / 20) + p.2.2.1))
    (by simp only [hopfParam, profilePoly, profileDiffP]; fun_prop)
  obtain ⟨M3, hM3⟩ := exists_bound_box (fun p => hopfParam p.1 *
      (1 + profilePoly p.1 p.2.1 p.2.2.1) *
      profileDiffQ p.1 (p.2.2.1 * p.2.2.2.2 - p.2.1 * p.2.2.2.1)
        (p.2.1 * (p.1 ^ 2 / 20) + p.2.2.1) (p.2.2.1 * (p.1 ^ 2 / 20) - p.2.1))
    (by simp only [hopfParam, profilePoly, profileDiffQ]; fun_prop)
  refine ⟨M1 + 2 * M2 + 2 * M3, fun ε t he => ?_⟩
  have hφ : hopfFreq ε * (t - 1) = (hopfFreq ε * t + ε ^ 2 / 20) - π / 2 := by
    simp only [hopfFreq, hopfOmega2]; ring
  have hcos1 : cos (hopfFreq ε * (t - 1)) =
      sin (hopfFreq ε * t) * cos (ε ^ 2 / 20) + cos (hopfFreq ε * t) * sin (ε ^ 2 / 20) := by
    rw [hφ, cos_sub_pi_div_two, sin_add]
  have hsin1 : sin (hopfFreq ε * (t - 1)) =
      sin (hopfFreq ε * t) * sin (ε ^ 2 / 20) - cos (hopfFreq ε * t) * cos (ε ^ 2 / 20) := by
    rw [hφ, sin_sub_pi_div_two, cos_add]; ring
  have hD : deriv (hopfApprox ε) t =
      hopfFreq ε * profileDerivPoly ε (cos (hopfFreq ε * t)) (sin (hopfFreq ε * t)) := by
    rw [(hasDerivAt_hopfApprox ε t).deriv, hopfProfileDeriv_eq]
  have hA1 : hopfApprox ε (t - 1) = profilePoly ε
      (sin (hopfFreq ε * t) * cos (ε ^ 2 / 20) + cos (hopfFreq ε * t) * sin (ε ^ 2 / 20))
      (sin (hopfFreq ε * t) * sin (ε ^ 2 / 20) - cos (hopfFreq ε * t) * cos (ε ^ 2 / 20)) := by
    rw [hopfApprox, hopfProfile_eq, hcos1, hsin1]
  have hA0 : hopfApprox ε t = profilePoly ε (cos (hopfFreq ε * t)) (sin (hopfFreq ε * t)) := by
    rw [hopfApprox, hopfProfile_eq]
  have hcs := cos_sq_add_sin_sq (hopfFreq ε * t)
  have hc := abs_cos_le_one (hopfFreq ε * t)
  have hs := abs_sin_le_one (hopfFreq ε * t)
  have hx := abs_cos_le_one (ε ^ 2 / 20)
  have hy := abs_sin_le_one (ε ^ 2 / 20)
  have hx1 : |cos (ε ^ 2 / 20) - 1| ≤ ε ^ 4 := abs_cos_sub_one_le
  have hy1 := abs_sin_sub_le he
  rw [hD, hA1, hA0]
  generalize cos (hopfFreq ε * t) = c at hcs hc ⊢
  generalize sin (hopfFreq ε * t) = s at hcs hs ⊢
  generalize cos (ε ^ 2 / 20) = x at hx hx1 ⊢
  generalize sin (ε ^ 2 / 20) = y at hy hy1 ⊢
  have key : hopfFreq ε * profileDerivPoly ε c s +
      hopfParam ε * profilePoly ε (s * x + c * y) (s * y - c * x) * (1 + profilePoly ε c s) =
      ε ^ 4 * residualCoeff ε c s +
        (hopfParam ε * (1 + profilePoly ε c s) * profileDiffP ε (s * x + c * y)
          (s * y - c * x) (c * (ε ^ 2 / 20) + s)) * (s * (x - 1) + c * (y - ε ^ 2 / 20)) +
        (hopfParam ε * (1 + profilePoly ε c s) * profileDiffQ ε (s * y - c * x)
          (c * (ε ^ 2 / 20) + s) (s * (ε ^ 2 / 20) - c)) *
          (s * (y - ε ^ 2 / 20) + -c * (x - 1)) := by
    have h1 := residualPoly_eq ε c s hcs
    have h2 := profilePoly_sub ε (s * x + c * y) (s * y - c * x) (c * (ε ^ 2 / 20) + s)
      (s * (ε ^ 2 / 20) - c)
    simp only [hopfFreq, hopfParam, hopfOmega2, hopfAlpha2]
    linear_combination h1 + ((π / 2 + (3 * π - 2) / 40 * ε ^ 2) * (1 + profilePoly ε c s)) * h2
  rw [key]
  have hG : |residualCoeff ε c s| ≤ M1 := hM1 ε c s x y he hc hs hx hy
  have hP : |hopfParam ε * (1 + profilePoly ε c s) * profileDiffP ε (s * x + c * y)
      (s * y - c * x) (c * (ε ^ 2 / 20) + s)| ≤ M2 := hM2 ε c s x y he hc hs hx hy
  have hQ : |hopfParam ε * (1 + profilePoly ε c s) * profileDiffQ ε (s * y - c * x)
      (c * (ε ^ 2 / 20) + s) (s * (ε ^ 2 / 20) - c)| ≤ M3 := hM3 ε c s x y he hc hs hx hy
  have hd1 : |s * (x - 1) + c * (y - ε ^ 2 / 20)| ≤ 2 * ε ^ 4 := abs_add_mul_le hs hc hx1 hy1
  have hd2 : |s * (y - ε ^ 2 / 20) + -c * (x - 1)| ≤ 2 * ε ^ 4 :=
    abs_add_mul_le hs (by rwa [abs_neg]) hy1 hx1
  have h4 : 0 ≤ ε ^ 4 := by positivity
  have hM2' : 0 ≤ M2 := (abs_nonneg _).trans hP
  have hM3' : 0 ≤ M3 := (abs_nonneg _).trans hQ
  generalize residualCoeff ε c s = G at hG ⊢
  generalize hopfParam ε * (1 + profilePoly ε c s) * profileDiffP ε (s * x + c * y)
    (s * y - c * x) (c * (ε ^ 2 / 20) + s) = P at hP ⊢
  generalize hopfParam ε * (1 + profilePoly ε c s) * profileDiffQ ε (s * y - c * x)
    (c * (ε ^ 2 / 20) + s) (s * (ε ^ 2 / 20) - c) = Q at hQ ⊢
  generalize s * (x - 1) + c * (y - ε ^ 2 / 20) = d1 at hd1 ⊢
  generalize s * (y - ε ^ 2 / 20) + -c * (x - 1) = d2 at hd2 ⊢
  have e1 : |ε ^ 4 * G| ≤ ε ^ 4 * M1 := by
    rw [abs_mul, abs_of_nonneg h4]; exact mul_le_mul_of_nonneg_left hG h4
  have e2 : |P * d1| ≤ M2 * (2 * ε ^ 4) := by
    rw [abs_mul]; exact mul_le_mul hP hd1 (abs_nonneg _) hM2'
  have e3 : |Q * d2| ≤ M3 * (2 * ε ^ 4) := by
    rw [abs_mul]; exact mul_le_mul hQ hd2 (abs_nonneg _) hM3'
  calc |ε ^ 4 * G + P * d1 + Q * d2| ≤ |ε ^ 4 * G| + |P * d1| + |Q * d2| :=
        abs_add_three _ _ _
    _ ≤ ε ^ 4 * M1 + M2 * (2 * ε ^ 4) + M3 * (2 * ε ^ 4) := by linarith
    _ = (M1 + 2 * M2 + 2 * M3) * ε ^ 4 := by ring

/-- The profile is `2π`-periodic. -/
theorem hopfProfile_periodic (ε : ℝ) : Function.Periodic (hopfProfile ε) (2 * π) := by
  intro θ
  rw [hopfProfile_eq, hopfProfile_eq, cos_add_two_pi, sin_add_two_pi]

theorem hopfFreq_pos {ε : ℝ} (he : |ε| ≤ 1) : 0 < hopfFreq ε := by
  have he2 : ε ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one ε).2 he
  simp only [hopfFreq, hopfOmega2]
  linarith [pi_gt_three]

/-- **Periodicity**: `v_ε` has period `2π / ω(ε)`. -/
theorem hopfApprox_periodic {ε : ℝ} (he : |ε| ≤ 1) :
    Function.Periodic (hopfApprox ε) (2 * π / hopfFreq ε) := by
  intro s
  have hω := (hopfFreq_pos he).ne'
  have h : hopfFreq ε * (s + 2 * π / hopfFreq ε) = hopfFreq ε * s + 2 * π := by
    have := div_mul_cancel₀ (2 * π) hω
    linear_combination this
  simp only [hopfApprox]
  rw [h]
  exact hopfProfile_periodic ε _

theorem hopfAlpha2_pos : 0 < hopfAlpha2 := by
  unfold hopfAlpha2; linarith [pi_gt_three]

/-- **Amplitude law**: `ε² = 40 (α(ε) - π / 2) / (3π - 2)`. -/
theorem sq_eq_hopfParam (ε : ℝ) : ε ^ 2 = 40 * (hopfParam ε - π / 2) / (3 * π - 2) := by
  have h : 3 * π - 2 ≠ 0 := ne_of_gt (by linarith [pi_gt_three])
  rw [eq_div_iff h]
  simp only [hopfParam, hopfAlpha2]
  field_simp
  ring

/-! ### The approximate orbit in the original variables -/

/-- The delay `τ(ε) = α(ε) / r` at which the approximate orbit of amplitude `ε` lives. -/
noncomputable def hopfDelay (r ε : ℝ) : ℝ := hopfParam ε / r

/-- The approximate periodic orbit `x_ε(t) = K (1 + v_ε(t / τ(ε)))` of Hutchinson's equation. -/
noncomputable def hopfOrbit (r K ε t : ℝ) : ℝ := K * (1 + hopfApprox ε (t / hopfDelay r ε))

theorem hopfDelay_zero (r : ℝ) : hopfDelay r 0 = criticalDelay r := by
  simp only [hopfDelay, hopfParam, criticalDelay]
  ring

/-- **Side of the approximate orbits**: for `ε ≠ 0` the approximate orbits live at delays
`τ(ε) > τ_c`, the side on which the equilibrium is linearly unstable. The direction of the true
bifurcation would need the Hopf theorem, which is not proved here. -/
theorem criticalDelay_lt_hopfDelay {r ε : ℝ} (hr : 0 < r) (hε : ε ≠ 0) :
    criticalDelay r < hopfDelay r ε := by
  have h : hopfDelay r ε - criticalDelay r = hopfAlpha2 * ε ^ 2 / r := by
    simp only [hopfDelay, hopfParam, criticalDelay]
    ring
  have hε2 : 0 < ε ^ 2 := lt_of_le_of_ne (sq_nonneg ε) (Ne.symm (pow_ne_zero 2 hε))
  have : 0 < hopfAlpha2 * ε ^ 2 / r := div_pos (mul_pos hopfAlpha2_pos hε2) hr
  linarith

/-- **Third-order normal form in the original variables**. For `r > 0`, `K ≠ 0` and
`|ε| ≤ 1`, the approximate orbit `x_ε` satisfies Hutchinson's equation with delay `τ(ε)` up to
a residual bounded by `C ε⁴`, uniformly in `t`. -/
theorem exists_hopfOrbit_residual_le {r K : ℝ} (hr : 0 < r) (hK : K ≠ 0) :
    ∃ C, ∀ ε t : ℝ, |ε| ≤ 1 →
      |deriv (hopfOrbit r K ε) t -
          r * hopfOrbit r K ε t * (1 - hopfOrbit r K ε (t - hopfDelay r ε) / K)| ≤
        C * ε ^ 4 := by
  obtain ⟨C, hC⟩ := exists_hopfApprox_residual_le
  refine ⟨|K| * (2 * r / π) * C, fun ε t he => ?_⟩
  have hp : π / 2 ≤ hopfParam ε :=
    le_add_of_nonneg_right (mul_nonneg hopfAlpha2_pos.le (sq_nonneg ε))
  have hτ : 0 < hopfDelay r ε := div_pos (by linarith [pi_pos]) hr
  have hrτ : r * hopfDelay r ε = hopfParam ε := by
    rw [hopfDelay]; field_simp
  have hderiv : HasDerivAt (hopfOrbit r K ε)
      (K * (deriv (hopfApprox ε) (t / hopfDelay r ε) / hopfDelay r ε)) t := by
    have h2 : HasDerivAt (fun y => y / hopfDelay r ε) (1 / hopfDelay r ε) t :=
      (hasDerivAt_id' t).div_const _
    have h3 := (((hasDerivAt_hopfApprox ε (t / hopfDelay r ε)).comp t h2).const_add 1).const_mul K
    refine h3.congr_deriv ?_
    rw [(hasDerivAt_hopfApprox ε (t / hopfDelay r ε)).deriv]
    ring
  have hsub : (t - hopfDelay r ε) / hopfDelay r ε = t / hopfDelay r ε - 1 := by
    field_simp
  have key : K * (deriv (hopfApprox ε) (t / hopfDelay r ε) / hopfDelay r ε) -
      r * hopfOrbit r K ε t * (1 - hopfOrbit r K ε (t - hopfDelay r ε) / K) =
      K / hopfDelay r ε * (deriv (hopfApprox ε) (t / hopfDelay r ε) +
        hopfParam ε * hopfApprox ε (t / hopfDelay r ε - 1) *
          (1 + hopfApprox ε (t / hopfDelay r ε))) := by
    have hk : K * (1 + hopfApprox ε (t / hopfDelay r ε - 1)) / K =
        1 + hopfApprox ε (t / hopfDelay r ε - 1) := by field_simp
    simp only [hopfOrbit]
    rw [hsub, hk, ← hrτ]
    field_simp
    ring
  rw [hderiv.deriv, key, abs_mul]
  have hinv : 1 / hopfDelay r ε ≤ 2 * r / π := by
    rw [div_le_div_iff₀ hτ pi_pos]; linarith
  have hKτ : |K / hopfDelay r ε| ≤ |K| * (2 * r / π) := by
    rw [abs_div, abs_of_pos hτ, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hinv (abs_nonneg K)
  calc |K / hopfDelay r ε| * |_| ≤ |K| * (2 * r / π) * (C * ε ^ 4) :=
        mul_le_mul hKτ (hC ε _ he) (abs_nonneg _) (by positivity)
    _ = |K| * (2 * r / π) * C * ε ^ 4 := by ring

end MathlibExt.Biology.Dynamics.DelayedLogisticHopf
