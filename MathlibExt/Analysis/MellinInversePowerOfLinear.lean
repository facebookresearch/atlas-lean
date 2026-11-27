/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Inverse Mellin transform of `(s - a)^{-m}`

For an integer `m ≥ 2`, real numbers `a < σ` and `x > 0`, the vertical-line integral
$$I(x) = \frac{1}{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty} x^{-s}(s-a)^{-m}\,ds
  = \frac{1}{2\pi}\int_{-\infty}^{\infty} x^{-\sigma-it}(\sigma-a+it)^{-m}\,dt$$
converges absolutely, does not depend on `σ > a`, and equals
`x^{-a} |log x|^{m-1}/(m-1)!` for `0 < x ≤ 1` and `0` for `x ≥ 1`.

In Lean the integral is Mathlib's `mellinInv σ (fun s => ((s - a) ^ m)⁻¹) x`.

## Proof

Instead of shifting the contour, we compute a forward Mellin transform and apply Mathlib's
Mellin inversion theorem `mellinInv_mellin_eq`. Let
`g_n(t) = (max 0 (-log t))^n / n!`. For `n ≥ 1`, `g_n(t) = |log t|^n/n!` for `0 < t ≤ 1` and
`g_n(t) = 0` for `t ≥ 1`, and `g_n` is continuous on `(0, ∞)`. For `n ≥ 1` the substitution
`t = e^{-y}` and the complex Gamma-type integral `∫_0^∞ y^n e^{-wy} dy = n!/w^{n+1}` (`Re w > 0`,
proved by induction with integration by parts) give `𝓜 g_n (w) = w^{-(n+1)}`; for `n = 0` the
Mellin integral of `g_0 = 1` diverges, which is why `m ≥ 2` is needed. Hence, as `m - 1 ≥ 1`, the
Mellin transform of `f(t) = t^{-a} g_{m-1}(t)` is `(s - a)^{-m}` on `Re s > a`, which is
integrable along vertical lines because `m ≥ 2`, and Mellin inversion returns `f(x)`.

## Source

J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki
exposé 631, Astérisque 121–122 (1985), 309–323, §3.3, Lemme 1 and the sentence after it
(p. 315).
-/

@[expose] public section

namespace MetaMathlibExt

open Complex MeasureTheory Set Filter
open scoped Topology

namespace MellinInversePowerOfLinear

/-- The function `y ↦ y^n e^{-wy}` is integrable on `(0, ∞)` when `Re w > 0`. -/
theorem integrableOn_pow_mul_cexp_neg_mul (n : ℕ) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ n * cexp (-(w * y))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ)) (b := w.re)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hw
  refine Integrable.mono' h
    (by fun_prop : Measurable fun y : ℝ => (y : ℂ) ^ n * cexp (-(w * y))).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => le_of_eq ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hy), Complex.norm_exp,
    Real.rpow_natCast, Real.rpow_one]
  simp

/-- **Complex Gamma-type integral.** For `Re w > 0`,
$$\int_0^\infty y^n e^{-wy}\,dy = \frac{n!}{w^{n+1}}.$$ -/
theorem integral_pow_mul_cexp_neg_mul (n : ℕ) {w : ℂ} (hw : 0 < w.re) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ n * cexp (-(w * y)) = n.factorial / w ^ (n + 1) := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  induction n with
  | zero =>
    have h := integral_exp_mul_complex_Ioi (a := -w) (by simpa using hw) 0
    simp only [neg_mul, ofReal_zero, mul_zero, Complex.exp_zero] at h
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one, h]
    field_simp
  | succ n ih =>
    have hu : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => (y : ℂ) ^ (n + 1))
        (((n + 1 : ℕ) : ℂ) * (y : ℂ) ^ n) y := fun y _ => by
      simpa using ((hasDerivAt_id y).ofReal_comp).fun_pow (n + 1)
    have hv : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => -cexp (-(w * y)) / w)
        (cexp (-(w * y))) y := fun y _ => by
      have h1 : HasDerivAt (fun y : ℝ => -(w * (y : ℂ))) (-(w * 1)) y := by
        simpa using (((hasDerivAt_id y).ofReal_comp).const_mul w).fun_neg
      convert (h1.cexp.fun_neg.div_const w) using 1
      field_simp
    have huv' : IntegrableOn ((fun y : ℝ => (y : ℂ) ^ (n + 1)) * fun y : ℝ => cexp (-(w * y)))
        (Ioi 0) := integrableOn_pow_mul_cexp_neg_mul (n + 1) hw
    have hu'v : IntegrableOn ((fun y : ℝ => ((n + 1 : ℕ) : ℂ) * (y : ℂ) ^ n) *
        fun y : ℝ => -cexp (-(w * y)) / w) (Ioi 0) :=
      IntegrableOn.congr_fun
        ((integrableOn_pow_mul_cexp_neg_mul n hw).const_mul (-((n + 1 : ℕ) : ℂ) / w))
        (fun y _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
    have h0 : Tendsto ((fun y : ℝ => (y : ℂ) ^ (n + 1)) * fun y : ℝ => -cexp (-(w * y)) / w)
        (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous ((fun y : ℝ => (y : ℂ) ^ (n + 1)) *
          fun y : ℝ => -cexp (-(w * y)) / w) := by
        simp only [Pi.mul_def]; fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    have hinf : Tendsto ((fun y : ℝ => (y : ℂ) ^ (n + 1)) * fun y : ℝ => -cexp (-(w * y)) / w)
        atTop (𝓝 0) := by
      have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n + 1 : ℕ) : ℝ) _ hw).div_const
        ‖w‖
      simp only [zero_div, Real.rpow_natCast] at hlim
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine hlim.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with y hy
      simp [Complex.norm_exp, abs_of_pos hy]
      ring
    have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
    have e2 : (∫ y in Ioi (0 : ℝ), ((n + 1 : ℕ) : ℂ) * (y : ℂ) ^ n * (-cexp (-(w * y)) / w)) =
        (-((n + 1 : ℕ) : ℂ) / w) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ n * cexp (-(w * y)) := by
      rw [← integral_const_mul]; congr 1; funext y; ring
    rw [key, e2, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The profile `g_n(t) = (max 0 (-log t))^n / n!`. For `n ≥ 1` it equals `|log t|^n / n!` on
`0 < t ≤ 1`, vanishes for `t ≥ 1`, and is continuous on `(0, ∞)`. -/
noncomputable def logProfile (n : ℕ) (t : ℝ) : ℝ := max 0 (-Real.log t) ^ n / n.factorial

/-- The function `f(t) = t^{-a} g_n(t)`. For `n ≥ 1` its Mellin transform is `(s - a)^{-(n+1)}`
on `Re s > a` (`mellin_kernel`); for `n = 0` its Mellin integral diverges. -/
noncomputable def kernel (a : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (-(a : ℂ)) • (logProfile n t : ℂ)

/-- For real `x`, `(e^x)^z = e^{xz}` with the principal complex power. -/
theorem ofReal_exp_cpow (x : ℝ) (z : ℂ) : ((Real.exp x : ℝ) : ℂ) ^ z = cexp (x * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

/-- For `n ≥ 1`, after the substitution `t = e^x`, the Mellin integrand of `g_n` at `w` is the
reflection of `1_{y > 0} y^n e^{-wy} / n!`. -/
theorem exp_smul_mellin_integrand_logProfile {n : ℕ} (hn : n ≠ 0) (w : ℂ) (x : ℝ) :
    Real.exp x • (((Real.exp x : ℝ) : ℂ) ^ (w - 1) • (logProfile n (Real.exp x) : ℂ)) =
      (Ioi (0 : ℝ)).indicator
        (fun y : ℝ => (n.factorial : ℂ)⁻¹ * ((y : ℂ) ^ n * cexp (-(w * y)))) (-x) := by
  rw [ofReal_exp_cpow, logProfile, Real.log_exp]
  by_cases hx : x < 0
  · rw [indicator_of_mem (show -x ∈ Ioi (0 : ℝ) from neg_pos.2 hx), max_eq_right (by linarith),
      Complex.real_smul, smul_eq_mul, Complex.ofReal_exp]
    push_cast
    rw [show -(w * -(x : ℂ)) = x * w by ring, show (x : ℂ) * (w - 1) = x * w - x by ring,
      Complex.exp_sub]
    field_simp
  · rw [indicator_of_notMem (show -x ∉ Ioi (0 : ℝ) by simp; linarith), max_eq_left (by linarith),
      zero_pow hn]
    simp

/-- **Mellin transform of `g_n`.** For `n ≥ 1` and `Re w > 0`, the Mellin integral of `g_n`
converges at `w` and `𝓜 g_n (w) = w^{-(n+1)}`. -/
theorem mellin_logProfile {n : ℕ} (hn : n ≠ 0) {w : ℂ} (hw : 0 < w.re) :
    MellinConvergent (fun t => (logProfile n t : ℂ)) w ∧
      mellin (fun t => (logProfile n t : ℂ)) w = (w ^ (n + 1))⁻¹ := by
  set K : ℝ → ℂ := (Ioi (0 : ℝ)).indicator
    (fun y : ℝ => (n.factorial : ℂ)⁻¹ * ((y : ℂ) ^ n * cexp (-(w * y)))) with hK
  have hKint : Integrable K := (integrable_indicator_iff measurableSet_Ioi).2
    ((integrableOn_pow_mul_cexp_neg_mul n hw).const_mul _)
  set G : ℝ → ℂ := fun t => (t : ℂ) ^ (w - 1) • (logProfile n t : ℂ) with hG
  have hfun : (fun x : ℝ => Real.exp x • G (Real.exp x)) = fun x => K (-x) := by
    funext x; exact exp_smul_mellin_integrand_logProfile hn w x
  refine ⟨?_, ?_⟩
  · change IntegrableOn G (Ioi 0)
    rw [← integrable_comp_exp, hfun]
    exact hKint.comp_neg
  · change ∫ t in Ioi (0 : ℝ), G t = _
    rw [← integral_comp_exp, hfun, integral_neg_eq_self, hK, integral_indicator measurableSet_Ioi,
      integral_const_mul, integral_pow_mul_cexp_neg_mul n hw]
    have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    field_simp

/-- **Mellin transform of the kernel.** For `n ≥ 1` and `Re s > a`, the Mellin integral of
`t^{-a} g_n(t)` converges at `s` and equals `(s - a)^{-(n+1)}`. -/
theorem mellin_kernel {a : ℝ} {n : ℕ} (hn : n ≠ 0) {s : ℂ} (hs : a < s.re) :
    MellinConvergent (kernel a n) s ∧ mellin (kernel a n) s = ((s - a) ^ (n + 1))⁻¹ := by
  have hw : 0 < (s - a).re := by simpa using hs
  obtain ⟨h1, h2⟩ := mellin_logProfile hn hw
  refine ⟨?_, ?_⟩
  · unfold kernel
    rw [MellinConvergent.cpow_smul, ← sub_eq_add_neg]
    exact h1
  · unfold kernel
    rw [mellin_cpow_smul, ← sub_eq_add_neg, h2]

/-- **Vertical integrability of `(s - a)^{-m}`.** For `m ≥ 2` and `a < σ`, the function
`t ↦ (σ + it - a)^{-m}` is integrable on `ℝ`. -/
theorem integrable_inv_sub_pow_vertical {m : ℕ} (hm : 2 ≤ m) {a σ : ℝ} (ha : a < σ) :
    Integrable (fun t : ℝ => (((σ : ℂ) + t * I - a) ^ m)⁻¹) := by
  set u := σ - a with hu_def
  have hu : 0 < u := sub_pos.2 ha
  have hz : ∀ t : ℝ, (σ : ℂ) + t * I - a = (u : ℂ) + t * I := fun t => by
    rw [hu_def]; push_cast; ring
  have hnorm : ∀ t : ℝ, ‖(u : ℂ) + t * I‖ ^ 2 = u ^ 2 + t ^ 2 := fun t => by
    rw [Complex.sq_norm, normSq_add_mul_I]
  have hge : ∀ t : ℝ, u ≤ ‖(u : ℂ) + t * I‖ := fun t => by
    have := abs_re_le_norm ((u : ℂ) + t * I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero] at this
    exact (le_abs_self u).trans this
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hint : Integrable (fun t : ℝ => (u ^ k * u ^ 2)⁻¹ * (1 + (t / u) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_div hu.ne').const_mul _
  refine hint.mono'
    (by fun_prop : Measurable fun t : ℝ => (((σ : ℂ) + t * I - a) ^ (k + 2))⁻¹).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  rw [hz, norm_inv, norm_pow, ← mul_inv]
  have h1 : u ^ k * u ^ 2 * (1 + (t / u) ^ 2) = u ^ k * ‖(u : ℂ) + t * I‖ ^ 2 := by
    rw [hnorm]; field_simp
  rw [h1]
  have hpos : 0 < ‖(u : ℂ) + t * I‖ := hu.trans_le (hge t)
  apply inv_anti₀ (by positivity)
  rw [pow_add]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu.le (hge t) k) (by positivity)

/-- Mellin inversion for the kernel: for `n ≥ 1`, `a < σ` and `x > 0`, the inverse Mellin
transform of `(s - a)^{-(n+1)}` along `Re s = σ` is `x^{-a} g_n(x)`. -/
theorem mellinInv_inv_sub_pow_eq_kernel {a σ x : ℝ} {n : ℕ} (hn : n ≠ 0) (ha : a < σ)
    (hx : 0 < x) : mellinInv σ (fun s => ((s - a) ^ (n + 1))⁻¹) x = kernel a n x := by
  have hre : ∀ y : ℝ, a < ((σ : ℂ) + y * I).re := fun y => by simpa using ha
  have hline : ∀ y : ℝ,
      mellin (kernel a n) (σ + y * I) = (((σ : ℂ) + y * I - a) ^ (n + 1))⁻¹ :=
    fun y => (mellin_kernel hn (hre y)).2
  have hVI : VerticalIntegrable (mellin (kernel a n)) σ := by
    unfold VerticalIntegrable
    simp only [hline]
    exact integrable_inv_sub_pow_vertical (by omega) ha
  have hconv : MellinConvergent (kernel a n) σ := (mellin_kernel hn (by simpa using ha)).1
  have hcont : ContinuousAt (kernel a n) x := by
    unfold kernel logProfile
    exact (continuousAt_ofReal_cpow_const x _ (Or.inr hx.ne')).smul
      (Complex.continuous_ofReal.continuousAt.comp
        (((continuousAt_const.max (Real.continuousAt_log hx.ne').neg).pow n).div_const _))
  rw [← mellinInv_mellin_eq σ (kernel a n) hx hconv hVI hcont]
  simp only [mellinInv, hline]

/-- On `0 < x ≤ 1` the kernel is `x^{-a} |log x|^n / n!`. -/
theorem kernel_of_le_one {a x : ℝ} {n : ℕ} (hx : 0 < x) (hx1 : x ≤ 1) :
    kernel a n x = ((x ^ (-a) * |Real.log x| ^ n / n.factorial : ℝ) : ℂ) := by
  have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
  rw [kernel, logProfile, max_eq_right (neg_nonneg.2 hlog), abs_of_nonpos hlog, smul_eq_mul,
    mul_div_assoc, Complex.ofReal_mul, Complex.ofReal_cpow hx.le]
  push_cast
  ring

/-- For `n ≥ 1` the kernel vanishes on `x ≥ 1`. -/
theorem kernel_of_one_le {a x : ℝ} {n : ℕ} (hn : n ≠ 0) (hx1 : 1 ≤ x) : kernel a n x = 0 := by
  rw [kernel, logProfile, max_eq_left (neg_nonpos.2 (Real.log_nonneg hx1)), zero_pow hn]
  simp

end MellinInversePowerOfLinear

open MellinInversePowerOfLinear

/-- **Absolute convergence.** Let `m ≥ 2` be an integer, let `a < σ` be real and `x > 0`. Then
$$t \mapsto x^{-\sigma-it}(\sigma - a + it)^{-m}$$
is integrable on `ℝ`, i.e. the inverse Mellin integral
$\frac{1}{2\pi}\int_{-\infty}^{\infty} x^{-\sigma-it}(\sigma-a+it)^{-m}\,dt$ converges absolutely.

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki
exposé 631, Astérisque 121–122 (1985), 309–323, §3.3, Lemme 1 and the sentence after it
(p. 315). -/
theorem integrable_cpow_mul_inv_sub_pow {m : ℕ} (hm : 2 ≤ m) {a σ x : ℝ} (ha : a < σ)
    (hx : 0 < x) :
    Integrable (fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + t * I)) * (((σ : ℂ) + t * I - a) ^ m)⁻¹) := by
  refine ((integrable_inv_sub_pow_vertical hm ha).norm.const_mul (x ^ (-σ))).mono'
    (by fun_prop : Measurable fun t : ℝ =>
      (x : ℂ) ^ (-((σ : ℂ) + t * I)) * (((σ : ℂ) + t * I - a) ^ m)⁻¹).aestronglyMeasurable
    (ae_of_all _ fun t => le_of_eq ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- **Value for `0 < x ≤ 1`.** Let `m ≥ 2` be an integer, let `a < σ` be real and `0 < x ≤ 1`.
Then
$$\frac{1}{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty} x^{-s}(s-a)^{-m}\,ds
  = \frac{x^{-a}\,|\log x|^{m-1}}{(m-1)!}.$$

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki
exposé 631, Astérisque 121–122 (1985), 309–323, §3.3, Lemme 1 and the sentence after it
(p. 315). -/
theorem mellinInv_inv_sub_pow_of_le_one {m : ℕ} (hm : 2 ≤ m) {a σ x : ℝ} (ha : a < σ)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    mellinInv σ (fun s => ((s - a) ^ m)⁻¹) x =
      ((x ^ (-a) * |Real.log x| ^ (m - 1) / (m - 1).factorial : ℝ) : ℂ) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [mellinInv_inv_sub_pow_eq_kernel (by omega) ha hx, kernel_of_le_one hx hx1,
    Nat.add_sub_cancel]

/-- **Value for `x ≥ 1`.** Let `m ≥ 2` be an integer, let `a < σ` be real and `x ≥ 1`. Then
$$\frac{1}{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty} x^{-s}(s-a)^{-m}\,ds = 0.$$

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki
exposé 631, Astérisque 121–122 (1985), 309–323, §3.3, Lemme 1 and the sentence after it
(p. 315). -/
theorem mellinInv_inv_sub_pow_of_one_le {m : ℕ} (hm : 2 ≤ m) {a σ x : ℝ} (ha : a < σ)
    (hx1 : 1 ≤ x) : mellinInv σ (fun s => ((s - a) ^ m)⁻¹) x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [mellinInv_inv_sub_pow_eq_kernel (by omega) ha (by linarith), kernel_of_one_le (by omega) hx1]

/-- **Independence of the line.** Let `m ≥ 2` be an integer, let `a` be real and `x > 0`. For any
two abscissae `σ, σ' > a`,
$$\int_{\sigma-i\infty}^{\sigma+i\infty} x^{-s}(s-a)^{-m}\,\frac{ds}{2\pi i}
  = \int_{\sigma'-i\infty}^{\sigma'+i\infty} x^{-s}(s-a)^{-m}\,\frac{ds}{2\pi i}.$$

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki
exposé 631, Astérisque 121–122 (1985), 309–323, §3.3, Lemme 1 and the sentence after it
(p. 315). -/
theorem mellinInv_inv_sub_pow_indep {m : ℕ} (hm : 2 ≤ m) {a σ σ' x : ℝ} (ha : a < σ)
    (ha' : a < σ') (hx : 0 < x) :
    mellinInv σ (fun s => ((s - a) ^ m)⁻¹) x = mellinInv σ' (fun s => ((s - a) ^ m)⁻¹) x := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [mellinInv_inv_sub_pow_eq_kernel (by omega) ha hx,
    mellinInv_inv_sub_pow_eq_kernel (by omega) ha' hx]

/-- **Inverse Mellin transform of `(s − a)^{−m}`.** Let `m ≥ 2` be an integer and let `a < σ` be
real numbers. For `x > 0`, with `x^{-s} = e^{-s \log x}`, the integral
$$I(x) = \int_{\sigma-i\infty}^{\sigma+i\infty} x^{-s}(s-a)^{-m}\,\frac{ds}{2\pi i}
  = \frac{1}{2\pi}\int_{-\infty}^{\infty} x^{-\sigma-it}(\sigma-a+it)^{-m}\,dt$$
converges absolutely, does not depend on `σ > a`, and
$$I(x) = \frac{x^{-a}\,|\log x|^{m-1}}{(m-1)!}\quad (0 < x \le 1), \qquad
  I(x) = 0 \quad (x \ge 1),$$
the two values agreeing at `x = 1` since `m ≥ 2`.

Here `I(x)` is Mathlib's `mellinInv σ (fun s => ((s - a) ^ m)⁻¹) x`. The conjuncts are, in order:
absolute convergence, independence of `σ`, the value on `(0, 1]`, the value on `[1, ∞)`, and the
vanishing of the first formula at `x = 1`.

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki
exposé 631, Astérisque 121–122 (1985), 309–323, §3.3, Lemme 1 and the sentence after it
(p. 315). -/
theorem mellinInv_inv_sub_pow {m : ℕ} (hm : 2 ≤ m) {a σ x : ℝ} (ha : a < σ) (hx : 0 < x) :
    Integrable (fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + t * I)) * (((σ : ℂ) + t * I - a) ^ m)⁻¹) ∧
      (∀ σ' : ℝ, a < σ' →
        mellinInv σ' (fun s => ((s - a) ^ m)⁻¹) x = mellinInv σ (fun s => ((s - a) ^ m)⁻¹) x) ∧
      (x ≤ 1 → mellinInv σ (fun s => ((s - a) ^ m)⁻¹) x =
        ((x ^ (-a) * |Real.log x| ^ (m - 1) / (m - 1).factorial : ℝ) : ℂ)) ∧
      (1 ≤ x → mellinInv σ (fun s => ((s - a) ^ m)⁻¹) x = 0) ∧
      ((1 : ℝ) ^ (-a) * |Real.log 1| ^ (m - 1) / (m - 1).factorial = 0) :=
  ⟨integrable_cpow_mul_inv_sub_pow hm ha hx,
    fun _ ha' => mellinInv_inv_sub_pow_indep hm ha' ha hx,
    mellinInv_inv_sub_pow_of_le_one hm ha hx,
    mellinInv_inv_sub_pow_of_one_le hm ha,
    by rw [Real.log_one, abs_zero, zero_pow (by omega)]; simp⟩

end MetaMathlibExt
