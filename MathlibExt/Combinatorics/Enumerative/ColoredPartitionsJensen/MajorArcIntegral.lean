/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColoredPartitionsJensen.MajorArc

/-!
# The integral side of the major arc

For `τ = y + iθ` (`y > 0`) put `v_s(θ) = τ^{−s} e^{A/τ + mτ}` (principal power) and

  `I_y(s) = (2π)⁻¹ ∫_{−y}^{y} v_s(θ) dθ`   (`iArc`),   `S(s, m) = m^{s−1} bT(s, Am)`   (`sSer`,
`MajorArc`).

This file proves, with no hypothesis beyond the stated inequalities:

* `laplace_cpow`: the **complex Laplace transform** `∫_0^∞ u^{a−1} e^{−τu} du = Γ(a) τ^{−a}` for
`Re a > 0`,
  `Re τ > 0` (Mathlib has the real rate only; the complex rate is the identity theorem on
`Re τ > 0`);
* `integral_line_cpow_exp`: **Hankel's formula on a vertical line**,
`(2π)⁻¹ ∫_ℝ τ^{−s} e^{mτ} dθ = m^{s−1}/Γ(s)`
  for `s > 1`, `m > 0` (Fourier inversion of `1_{u>0} u^{s−1} e^{−yu}`, Mathlib's
  `Integrable.fourierInv_fourier_eq` at the continuity point `u = m`);
* `integral_vInt_line`: the **full-line integral is the series**, `(2π)⁻¹ ∫_ℝ v_s = S(s, m)` for
`s > 1`
  (expand `e^{A/τ}`, dominated convergence, Hankel termwise);
* `norm_sSer_sub_iArc_le`: **tails** `‖S(s, m) − I_y(s)‖ ≤ e^{A/(2y)+my} y^{1−s}/(π(s−1))` (`s > 1`,
`A ≥ 0`),
  from `Re(A/τ) = Ay/(y²+θ²) ≤ A/(2y)` off the arc;
* `iArc_rec`: the **finite-arc recurrence** `m I_y(s) = s I_y(s+1) + A I_y(s+2) + B_y(s)` for every
real `s`
  (FTC on `[−y, y]`), `‖B_y(s)‖ ≤ (√2 y)^{−s} e^{A/(2y)+my}/π` (`norm_bArc_le`); the series obeys
the same
  recurrence without boundary term (`sSer_rec`, from `bT_rec`);
* `norm_iArc_sub_sSer_le`, `norm_iArc_sub_sSer_neg_half`: **descent** from two values `s₀, s₀+1 > 1`
down to
  `s = −r/2` (`s₀ = ⌊r/2⌋ + 2 − r/2 ∈ {3/2, 2}`), every constant explicit:
  `‖I_y(−r/2) − S(−r/2, m)‖ ≤ e^{A/(2y)+my} P_r(y)/π` for `m ≥ A + r/2 + 2`;
* `norm_iArc_sub_sSer_saddle`: at the saddle `y = √(A/m)` the exponential is `e^{(3/2)√(Am)}`
  (`saddle_exp`), against a main term `S(−r/2, m)` of size `e^{2√(Am)}` (`MajorArc`
`bT_neg_half_eq`, `le_besselInt`).
-/

open Filter Topology Set MeasureTheory Complex
open scoped Nat
open FourierTransform

namespace MetaMathlibExt.ColoredPartitionsJensen

@[expose] public section

noncomputable section

/-- Integrability of `u^b e^{-c u}` on `(0, ∞)` (`b > −1`, `c > 0`). -/
theorem integrableOn_rpow_exp {b c : ℝ} (hb : -1 < b) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => u ^ b * Real.exp (-(c * u))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow hb one_pos hc
  refine this.congr_fun (fun u hu => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

theorem norm_laplace_integrand (a τ : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ (a - 1) * cexp (-(τ * u))‖ = u ^ (a.re - 1) * Real.exp (-(τ.re * u)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp]
  simp

theorem continuousOn_laplace_integrand (a τ : ℂ) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ (a - 1) * cexp (-(τ * u))) (Ioi 0) := by
  intro u hu
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.mul ?_ (by fun_prop)
  exact (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hu)).comp continuous_ofReal.continuousAt

theorem integrable_laplace {a τ : ℂ} (ha : 0 < a.re) (hτ : 0 < τ.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (a - 1) * cexp (-(τ * u))) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_rpow_exp (b := a.re - 1) (by linarith) hτ)
    ((continuousOn_laplace_integrand a τ).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
  rw [norm_laplace_integrand a τ hu]

/-- The Laplace integral is complex-differentiable in the rate on `Re τ > 0`. -/
theorem hasDerivAt_laplace_cpow {a : ℂ} (ha : 0 < a.re) {τ₀ : ℂ} (hτ₀ : 0 < τ₀.re) :
    HasDerivAt (fun τ : ℂ => ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (a - 1) * cexp (-(τ * u)))
      (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (a - 1) * (cexp (-(τ₀ * u)) * -(u : ℂ))) τ₀ := by
  set c := τ₀.re / 2 with hc
  have hc0 : 0 < c := by positivity
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun τ u => (u : ℂ) ^ (a - 1) * cexp (-(τ * u)))
    (F' := fun τ u => (u : ℂ) ^ (a - 1) * (cexp (-(τ * u)) * -(u : ℂ)))
    (x₀ := τ₀) (bound := fun u => u ^ a.re * Real.exp (-(c * u))) (Metric.ball_mem_nhds τ₀ hc0)
    (Eventually.of_forall fun τ => (continuousOn_laplace_integrand a τ).aestronglyMeasurable
        measurableSet_Ioi)
    (integrable_laplace ha hτ₀) ?_ ?_ (integrableOn_rpow_exp (by linarith) hc0) ?_
  · exact key.2
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have h1 : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (a - 1)) (Ioi 0) := fun u hu =>
      ((continuousAt_cpow_const (ofReal_mem_slitPlane.2 hu)).comp
          continuous_ofReal.continuousAt).continuousWithinAt
    exact h1.mul (Continuous.continuousOn (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu τ hτ => ?_)
    have hu' : (0 : ℝ) < u := hu
    have hre : c ≤ τ.re := by
      have h1 : ‖τ - τ₀‖ < c := by simpa [dist_eq_norm] using hτ
      have h2 : |(τ - τ₀).re| ≤ ‖τ - τ₀‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h2
      have := (abs_lt.1 (lt_of_le_of_lt h2 h1)).1
      linarith
    rw [← mul_assoc, norm_mul, norm_laplace_integrand a τ hu', norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hu'.le]
    calc u ^ (a.re - 1) * Real.exp (-(τ.re * u)) * u
        = u ^ a.re * Real.exp (-(τ.re * u)) := by
          rw [mul_right_comm, ← Real.rpow_add_one hu'.ne']; ring_nf
      _ ≤ u ^ a.re * Real.exp (-(c * u)) := by
          gcongr
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu τ _ => ?_)
    have h1 : HasDerivAt (fun τ : ℂ => -(τ * u)) (-(1 * (u : ℂ))) τ :=
      ((hasDerivAt_id τ).mul_const (u : ℂ)).neg
    have h2 := h1.cexp.const_mul ((u : ℂ) ^ (a - 1))
    simpa using h2

/-- **Complex Laplace transform of a power**: `∫_0^∞ u^{a−1} e^{−τu} du = Γ(a) τ^{−a}` for
`Re a > 0`,
`Re τ > 0` (principal power). Mathlib has the real-rate case; the complex rate follows by the
    identity theorem. -/
theorem laplace_cpow {a : ℂ} (ha : 0 < a.re) {τ : ℂ} (hτ : 0 < τ.re) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (a - 1) * cexp (-(τ * u)) = Gamma a * τ ^ (-a) := by
  set U : Set ℂ := {z | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ (fun τ : ℂ => ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (a - 1) * cexp (-(τ * u)))
      U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hasDerivAt_laplace_cpow ha
        hz).differentiableAt.differentiableWithinAt) hUo
  have hG : AnalyticOnNhd ℂ (fun τ : ℂ => Gamma a * τ ^ (-a)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    refine (DifferentiableAt.const_mul ?_ _).differentiableWithinAt
    exact differentiableAt_id.cpow_const (mem_slitPlane_iff.2 (Or.inl hz))
  have hreal : ∀ t : ℝ, 0 < t →
      (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (a - 1) * cexp (-((t : ℂ) * u))) = Gamma a * (t : ℂ) ^ (-a)
          := by
    intro t ht
    rw [integral_cpow_mul_exp_neg_mul_Ioi ha ht, one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg,
          mul_comm]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), (fun τ : ℂ => ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (a - 1) * cexp
      (-(τ * u))) z =
      (fun τ : ℂ => Gamma a * τ ^ (-a)) z := by
    have ht : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 := (continuous_ofReal.tendsto _).comp this
        simp only [Function.comp_def, add_zero] at h2
        exact_mod_cast h2
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h' : (1 + 1 / ((n : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    exact hreal _ (by positivity)
  exact hF.eqOn_of_preconnected_of_frequently_eq hG (convex_halfSpace_re_gt 0).isPreconnected
    (by simp [hU]) hfreq hτ

/-! ### The vertical line `τ = y + iθ` -/

/-- `τ = y + iθ`. -/
def tauL (y θ : ℝ) : ℂ := (y : ℂ) + (θ : ℂ) * I

@[simp] theorem tauL_re (y θ : ℝ) : (tauL y θ).re = y := by simp [tauL]

@[simp] theorem tauL_im (y θ : ℝ) : (tauL y θ).im = θ := by simp [tauL]

theorem tauL_ne_zero {y : ℝ} (hy : 0 < y) (θ : ℝ) : tauL y θ ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this; linarith

theorem tauL_mem_slitPlane {y : ℝ} (hy : 0 < y) (θ : ℝ) : tauL y θ ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inl (by simpa using hy))

theorem continuous_tauL (y : ℝ) : Continuous (tauL y) := by unfold tauL; fun_prop

theorem norm_tauL (y θ : ℝ) : ‖tauL y θ‖ = √(y ^ 2 + θ ^ 2) := Complex.norm_add_mul_I y θ

theorem le_norm_tauL (y θ : ℝ) : |y| ≤ ‖tauL y θ‖ := by
  simpa using Complex.abs_re_le_norm (tauL y θ)

theorem abs_le_norm_tauL (y θ : ℝ) : |θ| ≤ ‖tauL y θ‖ := by
  simpa using Complex.abs_im_le_norm (tauL y θ)

theorem norm_tauL_pos {y : ℝ} (hy : 0 < y) (θ : ℝ) : 0 < ‖tauL y θ‖ := norm_pos_iff.2
    (tauL_ne_zero hy θ)

theorem continuous_tauL_cpow {y : ℝ} (hy : 0 < y) (c : ℂ) : Continuous fun θ => tauL y θ ^ c :=
  continuous_iff_continuousAt.2 fun θ =>
    (continuousAt_cpow_const (tauL_mem_slitPlane hy θ)).comp (continuous_tauL y).continuousAt

theorem norm_tauL_cpow (y θ s : ℝ) : ‖tauL y θ ^ (-(s : ℂ))‖ = ‖tauL y θ‖ ^ (-s) := by
  rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring]; exact norm_cpow_real _ _

/-- `θ ↦ |y + iθ|^{−s}` is integrable on `ℝ` for `s > 1`. -/
theorem integrable_norm_tauL_rpow {y s : ℝ} (hy : 0 < y) (hs : 1 < s) :
    Integrable fun θ => ‖tauL y θ‖ ^ (-s) := by
  set c := min y 1 / 2 with hc
  have hc0 : 0 < c := by positivity
  have hlow : ∀ θ, c * (1 + |θ|) ≤ ‖tauL y θ‖ := by
    intro θ
    have h1 := le_norm_tauL y θ
    have h2 := abs_le_norm_tauL y θ
    rw [abs_of_pos hy] at h1
    have hm1 : min y 1 ≤ y := min_le_left _ _
    have hm2 : min y 1 ≤ 1 := min_le_right _ _
    have hm0 : 0 < min y 1 := lt_min hy one_pos
    have : min y 1 * |θ| ≤ |θ| := mul_le_of_le_one_left (abs_nonneg _) hm2
    rw [hc]; nlinarith
  have hint : Integrable fun θ : ℝ => c ^ (-s) * (1 + ‖θ‖) ^ (-s) :=
    (integrable_one_add_norm (by simpa using hs)).const_mul _
  refine hint.mono' ?_ (Eventually.of_forall fun θ => ?_)
  · exact ((continuous_tauL y).norm.rpow_const fun θ => Or.inl (norm_tauL_pos hy
      θ).ne').aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.norm_eq_abs,
      ← Real.mul_rpow hc0.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (hlow θ) (by linarith)

theorem integrable_tauL_cpow {y s : ℝ} (hy : 0 < y) (hs : 1 < s) :
    Integrable fun θ => tauL y θ ^ (-(s : ℂ)) :=
  (integrable_norm_tauL_rpow hy hs).mono' (continuous_tauL_cpow hy _).aestronglyMeasurable
    (Eventually.of_forall fun θ => (norm_tauL_cpow y θ s).le)

/-! ### Fourier inversion: `(2π)⁻¹ ∫ τ^{−s} e^{mτ} dθ = m^{s−1}/Γ(s)` -/

/-- `g(u) = 1_{u>0} u^{s−1} e^{−yu}`. -/
def gL (s y : ℝ) : ℝ → ℂ := Set.indicator (Ioi 0) fun u => (u : ℂ) ^ ((s : ℂ) - 1) * cexp (-((y :
    ℂ) * u))

theorem integrable_gL {s y : ℝ} (hs : 0 < s) (hy : 0 < y) : Integrable (gL s y) :=
  (integrable_indicator_iff measurableSet_Ioi).2 (integrable_laplace (by simpa using hs)
      (by simpa using hy))

theorem fourier_gL {s y : ℝ} (hs : 0 < s) (hy : 0 < y) (ξ : ℝ) :
    𝓕 (gL s y) ξ = Gamma s * tauL y (2 * Real.pi * ξ) ^ (-(s : ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have : (fun v : ℝ => cexp (↑(-2 * Real.pi * v * ξ) * I) • gL s y v) = Set.indicator (Ioi 0)
      (fun v : ℝ => (v : ℂ) ^ ((s : ℂ) - 1) * cexp (-(tauL y (2 * Real.pi * ξ) * v))) := by
    funext v
    by_cases hv : v ∈ Ioi (0 : ℝ)
    · simp only [gL, indicator_of_mem hv, smul_eq_mul]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      simp only [tauL]; push_cast; ring
    · simp [gL, indicator_of_notMem hv]
  rw [this, integral_indicator measurableSet_Ioi, laplace_cpow (by simpa using hs)
      (by simpa using hy)]

theorem integrable_fourier_gL {s y : ℝ} (hs : 1 < s) (hy : 0 < y) : Integrable (𝓕 (gL s y)) := by
  have : 𝓕 (gL s y) = fun ξ => Gamma s * tauL y (2 * Real.pi * ξ) ^ (-(s : ℂ)) :=
    funext (fourier_gL (by linarith) hy)
  rw [this]
  exact ((integrable_tauL_cpow hy hs).comp_mul_left' (by positivity)).const_mul _

theorem continuousAt_gL (s y : ℝ) {m : ℝ} (hm : 0 < m) : ContinuousAt (gL s y) m := by
  have h : ContinuousAt (fun u : ℝ => (u : ℂ) ^ ((s : ℂ) - 1) * cexp (-((y : ℂ) * u))) m :=
    ((continuousAt_cpow_const (ofReal_mem_slitPlane.2 hm)).comp continuous_ofReal.continuousAt).mul
      (by fun_prop)
  exact h.congr (Filter.eventually_of_mem (Ioi_mem_nhds hm) fun u hu => by simp only [gL,
      indicator_of_mem hu])

/-- **Hankel's formula on a vertical line**: `(2π)⁻¹ ∫_ℝ τ^{−s} e^{mτ} dθ = m^{s−1}/Γ(s)`,
`τ = y + iθ`,
`y > 0`, `m > 0`, `s > 1` (Fourier inversion of `1_{u>0} u^{s−1} e^{−yu}`). -/
theorem integral_line_cpow_exp {s y m : ℝ} (hs : 1 < s) (hy : 0 < y) (hm : 0 < m) :
    (2 * Real.pi : ℂ)⁻¹ * ∫ θ, tauL y θ ^ (-(s : ℂ)) * cexp (m * tauL y θ) =
      ((m ^ (s - 1) * (Real.Gamma s)⁻¹ : ℝ) : ℂ) := by
  have hs0 : 0 < s := by linarith
  have hinv := (integrable_gL hs0 hy).fourierInv_fourier_eq (integrable_fourier_gL hs hy)
      (continuousAt_gL s y hm)
  rw [Real.fourierInv_eq'] at hinv
  set h : ℝ → ℂ := fun θ => cexp (↑(θ * m) * I) * tauL y θ ^ (-(s : ℂ)) with hh
  have h1 : (fun v : ℝ => cexp (↑(2 * Real.pi * inner ℝ v m) * I) • 𝓕 (gL s y) v) =
      fun v => Gamma s * h (2 * Real.pi * v) := by
    funext v
    rw [fourier_gL hs0 hy, smul_eq_mul, hh]
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast; ring_nf
  rw [h1, integral_const_mul, Measure.integral_comp_mul_left] at hinv
  have h2 : (fun θ : ℝ => tauL y θ ^ (-(s : ℂ)) * cexp (m * tauL y θ)) =
      fun θ => cexp (m * y) * h θ := by
    funext θ
    rw [hh]; simp only [tauL]
    rw [mul_add, Complex.exp_add]; push_cast; ring_nf
  rw [h2, integral_const_mul]
  have hG : (Gamma s : ℂ) ≠ 0 := by
    rw [Complex.Gamma_ofReal]; exact_mod_cast (Real.Gamma_pos_of_pos hs0).ne'
  simp only [gL, indicator_of_mem (show m ∈ Ioi (0 : ℝ) from hm)] at hinv
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), Complex.real_smul] at hinv
  have key : (2 * Real.pi : ℂ)⁻¹ * ∫ θ, h θ = (m : ℂ) ^ ((s : ℂ) - 1) * cexp (-((y : ℂ) * m)) /
      Gamma s := by
    rw [eq_div_iff hG, ← hinv]; push_cast; ring
  calc (2 * Real.pi : ℂ)⁻¹ * (cexp (m * y) * ∫ θ, h θ)
      = cexp (m * y) * ((2 * Real.pi : ℂ)⁻¹ * ∫ θ, h θ) := by ring
    _ = _ := by
      rw [key, Complex.Gamma_ofReal, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_cpow
          hm.le]
      have he : cexp (m * y) * cexp (-((y : ℂ) * m)) = 1 := by
        rw [← Complex.exp_add, show (m : ℂ) * y + -((y : ℂ) * m) = 0 by ring, Complex.exp_zero]
      push_cast
      linear_combination ((m : ℂ) ^ ((s : ℂ) - 1) * ((Real.Gamma s : ℂ))⁻¹) * he

/-! ### The full-line integral is the series `S(s, m) = m^{s−1} bT(s, Am)` for `s > 1` -/

/-- The major-arc integrand `τ^{−s} e^{A/τ + mτ}`, `τ = y + iθ`. -/
def vInt (A m y s θ : ℝ) : ℂ := tauL y θ ^ (-(s : ℂ)) * cexp (A / tauL y θ + m * tauL y θ)

/-- The series `S(s, m) = m^{s−1} bT(s, Am)`. -/
def sSer (A m s : ℝ) : ℝ := m ^ (s - 1) * bT s (A * m)

theorem norm_vInt (A m y s θ : ℝ) :
    ‖vInt A m y s θ‖ = ‖tauL y θ‖ ^ (-s) * Real.exp (((A : ℂ) / tauL y θ).re + m * y) := by
  rw [vInt, norm_mul, norm_tauL_cpow, Complex.norm_exp]
  simp [tauL]

theorem re_div_tauL_le (A : ℝ) {y : ℝ} (hy : 0 < y) (θ : ℝ) : ((A : ℂ) / tauL y θ).re ≤ |A| / y :=
    by
  calc ((A : ℂ) / tauL y θ).re ≤ ‖(A : ℂ) / tauL y θ‖ := Complex.re_le_norm _
    _ = |A| / ‖tauL y θ‖ := by rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |A| / y := div_le_div_of_nonneg_left (abs_nonneg _) hy
        (by simpa [abs_of_pos hy] using le_norm_tauL y θ)

/-- Off the central arc, `Re(A/τ) = Ay/(y²+θ²) ≤ A/(2y)`. -/
theorem re_div_tauL_le_half {A y θ : ℝ} (hA : 0 ≤ A) (hy : 0 < y) (hθ : y ^ 2 ≤ θ ^ 2) :
    ((A : ℂ) / tauL y θ).re ≤ A / (2 * y) := by
  rw [Complex.div_re, Complex.normSq_apply]
  simp only [ofReal_re, ofReal_im, tauL_re, tauL_im, zero_mul, zero_div, add_zero]
  rw [div_le_div_iff₀ (by nlinarith [mul_pos hy hy, mul_self_nonneg θ]) (by positivity)]
  nlinarith [mul_nonneg hA (sub_nonneg.2 hθ), hy]

theorem continuous_vInt (A m : ℝ) {y : ℝ} (hy : 0 < y) (s : ℝ) : Continuous (vInt A m y s) := by
  unfold vInt
  refine (continuous_tauL_cpow hy _).mul (Continuous.cexp ?_)
  exact (continuous_const.div (continuous_tauL y) (tauL_ne_zero hy)).add
    (continuous_const.mul (continuous_tauL y))

theorem norm_vInt_le (A m : ℝ) {y : ℝ} (hy : 0 < y) (s θ : ℝ) :
    ‖vInt A m y s θ‖ ≤ ‖tauL y θ‖ ^ (-s) * Real.exp (|A| / y + m * y) := by
  rw [norm_vInt]
  gcongr
  exact re_div_tauL_le A hy θ

theorem integrable_vInt (A m : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 < s) : Integrable (vInt A m y s) :=
  ((integrable_norm_tauL_rpow hy hs).mul_const _).mono' (continuous_vInt A m hy
      s).aestronglyMeasurable
    (Eventually.of_forall fun θ => norm_vInt_le A m hy s θ)

/-- **The full-line integral is the series** for `s > 1`:
`(2π)⁻¹ ∫_ℝ τ^{−s} e^{A/τ + mτ} dθ = m^{s−1} bT(s, Am)` (expand `e^{A/τ}`, Hankel termwise). -/
theorem integral_vInt_line (A : ℝ) {m y s : ℝ} (hs : 1 < s) (hy : 0 < y) (hm : 0 < m) :
    (2 * Real.pi : ℂ)⁻¹ * ∫ θ, vInt A m y s θ = (sSer A m s : ℂ) := by
  set F : ℕ → ℝ → ℂ := fun j θ =>
    ((A ^ j / j ! : ℝ) : ℂ) * (tauL y θ ^ (-((s + j : ℝ) : ℂ)) * cexp (m * tauL y θ)) with hF
  set bd : ℕ → ℝ → ℝ := fun j θ => (|A| / y) ^ j / j ! * (‖tauL y θ‖ ^ (-s) * Real.exp (m * y))
      with hbd
  have hcpow : ∀ (j : ℕ) θ, tauL y θ ^ (-((s + j : ℝ) : ℂ)) = tauL y θ ^ (-(s : ℂ)) * (tauL y θ ^
      j)⁻¹ := by
    intro j θ
    rw [show -((s + j : ℝ) : ℂ) = -(s : ℂ) + -(j : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ (tauL_ne_zero hy θ), Complex.cpow_neg _ (j : ℂ), Complex.cpow_natCast]
  have hpt : ∀ θ, HasSum (fun j => F j θ) (vInt A m y s θ) := by
    intro θ
    have h := (NormedSpace.expSeries_div_hasSum_exp ((A : ℂ) / tauL y θ)).mul_right
      (tauL y θ ^ (-(s : ℂ)) * cexp (m * tauL y θ))
    rw [← Complex.exp_eq_exp_ℂ] at h
    convert h using 1
    · funext j
      rw [hF]; simp only
      rw [hcpow, div_pow]; push_cast; ring
    · rw [vInt, Complex.exp_add]; ring
  have hFn : ∀ j θ, ‖F j θ‖ ≤ bd j θ := by
    intro j θ
    have hτ := norm_tauL_pos hy θ
    have hyτ : y ≤ ‖tauL y θ‖ := by simpa [abs_of_pos hy] using le_norm_tauL y θ
    rw [hF, hbd]; simp only
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast,
      norm_tauL_cpow, Complex.norm_exp]
    · have hre : (↑m * tauL y θ).re = m * y := by simp [tauL]
      rw [hre, show -(s + j) = -s + -(j : ℝ) by ring, Real.rpow_add hτ, Real.rpow_neg hτ.le (j : ℝ),
        Real.rpow_natCast]
      have h1 : (‖tauL y θ‖ ^ j)⁻¹ ≤ (y ^ j)⁻¹ := by
        gcongr
      calc |A| ^ j / j ! * (‖tauL y θ‖ ^ (-s) * (‖tauL y θ‖ ^ j)⁻¹ * Real.exp (m * y))
          ≤ |A| ^ j / j ! * (‖tauL y θ‖ ^ (-s) * (y ^ j)⁻¹ * Real.exp (m * y)) := by gcongr
        _ = (|A| / y) ^ j / j ! * (‖tauL y θ‖ ^ (-s) * Real.exp (m * y)) := by
          rw [div_pow]; ring
  have hbi : Integrable (fun θ => ∑' j, bd j θ) := by
    have : (fun θ => ∑' j, bd j θ) = fun θ => Real.exp (|A| / y) * (‖tauL y θ‖ ^ (-s) * Real.exp
        (m * y)) := by
      funext θ
      rw [hbd]; simp only
      rw [tsum_mul_right, Real.exp_eq_exp_ℝ, (NormedSpace.expSeries_div_hasSum_exp (|A| /
          y)).tsum_eq]
    rw [this]
    exact ((integrable_norm_tauL_rpow hy hs).mul_const _).const_mul _
  have hsum := MeasureTheory.hasSum_integral_of_dominated_convergence (μ := volume) (F := F)
    (f := vInt A m y s) bd
    (fun j => Continuous.aestronglyMeasurable (continuous_const.mul ((continuous_tauL_cpow hy _).mul
      (continuous_const.mul (continuous_tauL y)).cexp)))
    (fun j => Eventually.of_forall fun θ => hFn j θ)
    (Eventually.of_forall fun θ => (Real.summable_pow_div_factorial _).mul_right _) hbi
    (Eventually.of_forall hpt)
  have hterm : ∀ j : ℕ, (2 * Real.pi : ℂ)⁻¹ * ∫ θ, F j θ = ((m ^ (s - 1) * bTt s (A * m) j : ℝ) :
      ℂ) := by
    intro j
    have hsj : 1 < s + j := by have := Nat.cast_nonneg (α := ℝ) j; linarith
    rw [hF]; simp only
    rw [integral_const_mul, mul_left_comm, integral_line_cpow_exp hsj hy hm, ← Complex.ofReal_mul]
    congr 1
    rw [bTt, show s + j - 1 = (s - 1) + j by ring, Real.rpow_add hm, Real.rpow_natCast, mul_pow]
    ring
  have h1 := hsum.mul_left (2 * Real.pi : ℂ)⁻¹
  simp only [hterm] at h1
  have h2 : HasSum (fun j => ((m ^ (s - 1) * bTt s (A * m) j : ℝ) : ℂ)) (sSer A m s : ℂ) :=
    Complex.hasSum_ofReal.2 ((hasSum_bT s (A * m)).mul_left _)
  exact h1.unique h2

/-! ### Tails `|θ| ≥ y` -/

/-- The central-arc integral `I_y(s) = (2π)⁻¹ ∫_{−y}^{y} τ^{−s} e^{A/τ + mτ} dθ`. -/
def iArc (A m y s : ℝ) : ℂ := (2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-y)..y, vInt A m y s θ

theorem norm_vInt_le_off {A y : ℝ} (m : ℝ) (hA : 0 ≤ A) (hy : 0 < y) (s : ℝ) {θ : ℝ} (hθ : y ^ 2 ≤
    θ ^ 2) :
    ‖vInt A m y s θ‖ ≤ ‖tauL y θ‖ ^ (-s) * Real.exp (A / (2 * y) + m * y) := by
  rw [norm_vInt]
  gcongr
  exact re_div_tauL_le_half hA hy hθ

/-- One tail: `‖∫_{θ>y} f‖ ≤ E y^{1−s}/(s−1)` when `‖f θ‖ ≤ ‖τ‖^{−s} E` there. -/
theorem norm_integral_Ioi_le {f : ℝ → ℂ} {y s E : ℝ} (hy : 0 < y) (hs : 1 < s) (hE : 0 ≤ E)
    (hf : ∀ θ, y < θ → ‖f θ‖ ≤ ‖tauL y θ‖ ^ (-s) * E) :
    ‖∫ θ in Ioi y, f θ‖ ≤ E * (y ^ (1 - s) / (s - 1)) := by
  have hint : IntegrableOn (fun θ : ℝ => E * θ ^ (-s)) (Ioi y) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hy).const_mul E
  calc ‖∫ θ in Ioi y, f θ‖ ≤ ∫ θ in Ioi y, E * θ ^ (-s) := by
        refine norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2
          (Eventually.of_forall fun θ hθ => ?_))
        have hθ' : y < θ := hθ
        have hθ0 : 0 < θ := hy.trans hθ'
        have h1 : θ ≤ ‖tauL y θ‖ := by simpa [abs_of_pos hθ0] using abs_le_norm_tauL y θ
        calc ‖f θ‖ ≤ ‖tauL y θ‖ ^ (-s) * E := hf θ hθ'
          _ ≤ θ ^ (-s) * E := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hθ0 h1
              (by linarith)) hE
          _ = E * θ ^ (-s) := mul_comm _ _
    _ = E * (y ^ (1 - s) / (s - 1)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hy]
        congr 1
        rw [show -s + 1 = 1 - s by ring, show (1 : ℝ) - s = -(s - 1) by ring, div_neg, neg_div,
            neg_neg]

/-- **Tails**: `‖S(s, m) − I_y(s)‖ ≤ e^{A/(2y) + my} y^{1−s} / (π (s−1))` for `s > 1`, `A ≥ 0`. -/
theorem norm_sSer_sub_iArc_le {A m y s : ℝ} (hA : 0 ≤ A) (hs : 1 < s) (hy : 0 < y) (hm : 0 < m) :
    ‖(sSer A m s : ℂ) - iArc A m y s‖ ≤
      Real.exp (A / (2 * y) + m * y) * y ^ (1 - s) / (Real.pi * (s - 1)) := by
  set E := Real.exp (A / (2 * y) + m * y) with hE
  have hint := integrable_vInt A m hy hs
  have hsplit : (∫ θ, vInt A m y s θ) - ∫ θ in (-y)..y, vInt A m y s θ =
      (∫ θ in Ioi y, vInt A m y s (-θ)) + ∫ θ in Ioi y, vInt A m y s θ := by
    rw [integral_comp_neg_Ioi, ← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn
        hint.integrableOn,
      ← intervalIntegral.integral_Iic_add_Ioi (b := y) hint.integrableOn hint.integrableOn]
    ring
  have hL : ‖∫ θ in Ioi y, vInt A m y s (-θ)‖ ≤ E * (y ^ (1 - s) / (s - 1)) := by
    refine norm_integral_Ioi_le hy hs (Real.exp_pos _).le fun θ hθ => ?_
    have h := norm_vInt_le_off m hA hy s (θ := -θ) (by nlinarith)
    have hn : ‖tauL y (-θ)‖ = ‖tauL y θ‖ := by rw [norm_tauL, norm_tauL, neg_sq]
    rwa [hn] at h
  have hR : ‖∫ θ in Ioi y, vInt A m y s θ‖ ≤ E * (y ^ (1 - s) / (s - 1)) :=
    norm_integral_Ioi_le hy hs (Real.exp_pos _).le fun θ hθ => norm_vInt_le_off m hA hy s
        (by nlinarith)
  have hS := integral_vInt_line A hs hy hm
  have hdiff : (sSer A m s : ℂ) - iArc A m y s = (2 * Real.pi : ℂ)⁻¹ *
      ((∫ θ in Ioi y, vInt A m y s (-θ)) + ∫ θ in Ioi y, vInt A m y s θ) := by
    rw [← hS, iArc, ← hsplit]; ring
  rw [hdiff, norm_mul, norm_inv, show ((2 * Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ)
      by push_cast; ring,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hpi := Real.pi_pos
  calc (2 * Real.pi)⁻¹ * ‖(∫ θ in Ioi y, vInt A m y s (-θ)) + ∫ θ in Ioi y, vInt A m y s θ‖
      ≤ (2 * Real.pi)⁻¹ * (E * (y ^ (1 - s) / (s - 1)) + E * (y ^ (1 - s) / (s - 1))) := by
        gcongr; exact (norm_add_le _ _).trans (add_le_add hL hR)
    _ = E * y ^ (1 - s) / (Real.pi * (s - 1)) := by
        field_simp; ring

/-! ### The finite-arc recurrence -/

theorem hasDerivAt_tauL (y θ : ℝ) : HasDerivAt (tauL y) I θ := by
  have h := (((hasDerivAt_id θ).ofReal_comp).mul_const I).const_add (y : ℂ)
  have e : tauL y = fun x : ℝ => (y : ℂ) + ((id x : ℝ) : ℂ) * I := by funext x; simp [tauL]
  rw [e]; convert h using 1; simp

/-- `d/dθ [τ^{−s} e^{A/τ+mτ}] = i (m v(s) − s v(s+1) − A v(s+2))`, `v(s) = τ^{−s} e^{A/τ+mτ}`. -/
theorem hasDerivAt_vInt (A m : ℝ) {y : ℝ} (hy : 0 < y) (s θ : ℝ) :
    HasDerivAt (vInt A m y s)
      (I * (m * vInt A m y s θ - s * vInt A m y (s + 1) θ - A * vInt A m y (s + 2) θ)) θ := by
  have hτ := hasDerivAt_tauL y θ
  have hne := tauL_ne_zero hy θ
  have h1 : HasDerivAt (fun θ => tauL y θ ^ (-(s : ℂ)))
      (-(s : ℂ) * tauL y θ ^ (-(s : ℂ) - 1) * I) θ :=
    (Complex.hasStrictDerivAt_cpow_const (tauL_mem_slitPlane hy θ)).hasDerivAt.comp θ hτ
  have h2 : HasDerivAt (fun θ => (A : ℂ) / tauL y θ + m * tauL y θ)
      ((0 * tauL y θ - A * I) / tauL y θ ^ 2 + m * I) θ :=
    ((hasDerivAt_const θ (A : ℂ)).div hτ hne).add (hτ.const_mul (m : ℂ))
  have h3 := h1.mul h2.cexp
  change HasDerivAt (fun θ => tauL y θ ^ (-(s : ℂ)) * cexp ((A : ℂ) / tauL y θ + m * tauL y θ)) _ θ
  convert h3 using 1
  simp only [vInt]
  have e1 : tauL y θ ^ (-((s + 1 : ℝ) : ℂ)) = tauL y θ ^ (-(s : ℂ) - 1) := by
    congr 1; push_cast; ring
  have e2 : tauL y θ ^ (-(s : ℂ) - 1) = tauL y θ ^ (-(s : ℂ)) / tauL y θ := by
    rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
  have e3 : tauL y θ ^ (-((s + 2 : ℝ) : ℂ)) = tauL y θ ^ (-(s : ℂ)) / tauL y θ ^ 2 := by
    rw [show -((s + 2 : ℝ) : ℂ) = -(s : ℂ) - 2 by push_cast; ring, Complex.cpow_sub _ _ hne,
        Complex.cpow_two]
  rw [e1, e3, e2]
  field_simp
  ring

theorem intervalIntegrable_vInt (A m : ℝ) {y : ℝ} (hy : 0 < y) (s a b : ℝ) :
    IntervalIntegrable (vInt A m y s) volume a b :=
  (continuous_vInt A m hy s).intervalIntegrable a b

/-- The boundary term `B_y(s) = (2π)⁻¹ (v_s(y) − v_s(−y)) / i`. -/
def bArc (A m y s : ℝ) : ℂ := (2 * Real.pi : ℂ)⁻¹ * (vInt A m y s y - vInt A m y s (-y)) / I

/-- **Finite-arc recurrence**: `m I_y(s) = s I_y(s+1) + A I_y(s+2) + B_y(s)` for every real `s`. -/
theorem iArc_rec (A m : ℝ) {y : ℝ} (hy : 0 < y) (s : ℝ) :
    (m : ℂ) * iArc A m y s = s * iArc A m y (s + 1) + A * iArc A m y (s + 2) + bArc A m y s := by
  have c0 := continuous_vInt A m hy s
  have c1 := continuous_vInt A m hy (s + 1)
  have c2 := continuous_vInt A m hy (s + 2)
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := -y) (b := y)
    (fun θ _ => hasDerivAt_vInt A m hy s θ) (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    ((intervalIntegrable_vInt A m hy s _ _).const_mul _ |>.sub ((intervalIntegrable_vInt A m hy
        (s+1) _ _).const_mul _))
    ((intervalIntegrable_vInt A m hy (s+2) _ _).const_mul _),
    intervalIntegral.integral_sub ((intervalIntegrable_vInt A m hy s _ _).const_mul _)
      ((intervalIntegrable_vInt A m hy (s+1) _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hF
  simp only [iArc, bArc]
  rw [← hF]
  field_simp
  ring

theorem norm_vInt_edge {A y : ℝ} (m : ℝ) (hA : 0 ≤ A) (hy : 0 < y) (s : ℝ) {θ : ℝ} (hθ : θ ^ 2 = y
    ^ 2) :
    ‖vInt A m y s θ‖ ≤ (√2 * y) ^ (-s) * Real.exp (A / (2 * y) + m * y) := by
  have h := norm_vInt_le_off m hA hy s hθ.ge
  have hn : ‖tauL y θ‖ = √2 * y := by
    rw [norm_tauL, hθ, show y ^ 2 + y ^ 2 = (√2 * y) ^ 2 by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring, Real.sqrt_sq (by positivity)]
  rwa [hn] at h

/-- `‖B_y(s)‖ ≤ π⁻¹ (√2 y)^{−s} e^{A/(2y) + my}`. -/
theorem norm_bArc_le {A y : ℝ} (m : ℝ) (hA : 0 ≤ A) (hy : 0 < y) (s : ℝ) :
    ‖bArc A m y s‖ ≤ (√2 * y) ^ (-s) * Real.exp (A / (2 * y) + m * y) / Real.pi := by
  have h1 := norm_vInt_edge m hA hy s (θ := y) rfl
  have h2 := norm_vInt_edge m hA hy s (θ := -y) (neg_sq y)
  rw [bArc, norm_div, Complex.norm_I, div_one, norm_mul, norm_inv,
    show ((2 * Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hpi := Real.pi_pos
  calc (2 * Real.pi)⁻¹ * ‖vInt A m y s y - vInt A m y s (-y)‖
      ≤ (2 * Real.pi)⁻¹ * ((√2 * y) ^ (-s) * Real.exp (A / (2 * y) + m * y) +
          (√2 * y) ^ (-s) * Real.exp (A / (2 * y) + m * y)) := by
        gcongr; exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    _ = _ := by field_simp; ring

/-- The series obeys the same recurrence: `m S(s) = s S(s+1) + A S(s+2)` (from `bT_rec`). -/
theorem sSer_rec (A : ℝ) {m : ℝ} (hm : 0 < m) (s : ℝ) :
    m * sSer A m s = s * sSer A m (s + 1) + A * sSer A m (s + 2) := by
  have e1 : m ^ (s + 1 - 1) = m ^ (s - 1) * m := by
    rw [show s + 1 - 1 = (s - 1) + 1 by ring, Real.rpow_add_one hm.ne']
  have e2 : m ^ (s + 2 - 1) = m ^ (s - 1) * m * m := by
    rw [show s + 2 - 1 = ((s - 1) + 1) + 1 by ring, Real.rpow_add_one hm.ne', Real.rpow_add_one
        hm.ne']
  simp only [sSer]
  rw [e1, e2, bT_rec s (A * m)]
  ring

/-! ### Descent from `s₀ > 1` to `s₀ − k` -/

/-- Abstract descent: if `m D(t) = t D(t+1) + A D(t+2) + B(t)`, `|t| + A ≤ m`, `‖B(t)‖ ≤ β` along
the
`k` steps, and `‖D(s₀)‖, ‖D(s₀+1)‖ ≤ δ`, then `‖D(s₀ − k)‖ ≤ δ + kβ` (`m ≥ 1`). -/
theorem descent_bound {D B : ℝ → ℂ} {m A s₀ δ β : ℝ} (hm : 1 ≤ m) (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hrec : ∀ t, (m : ℂ) * D t = t * D (t + 1) + A * D (t + 2) + B t)
    (h0 : ‖D s₀‖ ≤ δ) (h1 : ‖D (s₀ + 1)‖ ≤ δ) (k : ℕ)
    (hsize : ∀ j : ℕ, j < k → |s₀ - (j + 1)| + A ≤ m)
    (hB : ∀ j : ℕ, j < k → ‖B (s₀ - (j + 1))‖ ≤ β) :
    ‖D (s₀ - k)‖ ≤ δ + k * β ∧ ‖D (s₀ - k + 1)‖ ≤ δ + k * β := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans h0
  induction k with
  | zero => simpa using ⟨h0, h1⟩
  | succ k ih =>
    obtain ⟨ihA, ihB⟩ := ih (fun j hj => hsize j (by omega)) (fun j hj => hB j (by omega))
    set M := δ + k * β with hM
    have hM0 : 0 ≤ M := by positivity
    set t := s₀ - ((k + 1 : ℕ) : ℝ) with ht
    have ht1 : t + 1 = s₀ - k := by rw [ht]; push_cast; ring
    have ht2 : t + 2 = s₀ - k + 1 := by rw [ht]; push_cast; ring
    have hsz : |t| + A ≤ m := by simpa [ht] using hsize k (by omega)
    have hBt : ‖B t‖ ≤ β := by simpa [ht] using hB k (by omega)
    have hm0 : 0 < m := by linarith
    have hDt : ‖D t‖ ≤ M + β := by
      have heq : D t = (t * D (t + 1) + A * D (t + 2) + B t) / m := by
        rw [eq_div_iff (by exact_mod_cast hm0.ne'), ← hrec t, mul_comm]
      rw [heq, norm_div, Complex.norm_real, Real.norm_of_nonneg hm0.le, div_le_iff₀ hm0]
      have hn : ‖(t : ℂ) * D (t + 1) + A * D (t + 2) + B t‖ ≤ |t| * M + A * M + β := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hBt)
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ht1]
          exact mul_le_mul_of_nonneg_left ihA (abs_nonneg _)
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hA, ht2]
          exact mul_le_mul_of_nonneg_left ihB hA
      nlinarith
    refine ⟨?_, ?_⟩
    · push_cast at hDt ⊢; rw [← ht] at *; linarith
    · rw [show s₀ - ((k + 1 : ℕ) : ℝ) + 1 = s₀ - k by push_cast; ring]; push_cast; linarith

/-! ### Assembly: `‖I_y(s₀ − k) − S(s₀ − k)‖` -/

/-- `x^{−t} ≤ x^{−b} + x^{−a}` for `a ≤ t ≤ b`, `x > 0`. -/
theorem rpow_neg_le_add {x a b t : ℝ} (hx : 0 < x) (hat : a ≤ t) (htb : t ≤ b) :
    x ^ (-t) ≤ x ^ (-b) + x ^ (-a) := by
  rcases le_total x 1 with h | h
  · have : x ^ (-t) ≤ x ^ (-b) := Real.rpow_le_rpow_of_exponent_ge hx h (by linarith)
    linarith [Real.rpow_nonneg hx.le (-a)]
  · have : x ^ (-t) ≤ x ^ (-a) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    linarith [Real.rpow_nonneg hx.le (-b)]

/-- **Major arc, integral side, from `s₀ > 1` down `k` steps**: with `E = e^{A/(2y) + my}`,
`‖I_y(s₀−k) − S(s₀−k)‖ ≤ (E/π)(y^{1−s₀}/(s₀−1) + y^{−s₀}/s₀ + k((√2y)^{−s₀} + (√2y)^{−(s₀−k)}))`,
provided `|t| + A ≤ m` on `[s₀ − k, s₀]` and `m ≥ 1`. -/
theorem norm_iArc_sub_sSer_le {A m y s₀ : ℝ} (k : ℕ) (hA : 0 ≤ A) (hy : 0 < y) (hm : 1 ≤ m)
    (hs₀ : 1 < s₀) (hsize : ∀ t, s₀ - k ≤ t → t ≤ s₀ → |t| + A ≤ m) :
    ‖iArc A m y (s₀ - k) - sSer A m (s₀ - k)‖ ≤ Real.exp (A / (2 * y) + m * y) / Real.pi *
      (y ^ (1 - s₀) / (s₀ - 1) + y ^ (-s₀) / s₀ + k * ((√2 * y) ^ (-s₀) + (√2 * y) ^ (-(s₀ - k))))
          := by
  set E := Real.exp (A / (2 * y) + m * y) with hE
  have hm0 : 0 < m := by linarith
  have hpi := Real.pi_pos
  have hE0 : 0 < E := Real.exp_pos _
  set D : ℝ → ℂ := fun t => iArc A m y t - sSer A m t with hD
  have hrec : ∀ t, (m : ℂ) * D t = t * D (t + 1) + A * D (t + 2) + bArc A m y t := by
    intro t
    simp only [hD]
    have h1 := iArc_rec A m hy t
    have h2 : (m : ℂ) * sSer A m t = t * sSer A m (t + 1) + A * sSer A m (t + 2) := by
      exact_mod_cast sSer_rec A hm0 t
    linear_combination h1 - h2
  set δ := E / Real.pi * (y ^ (1 - s₀) / (s₀ - 1) + y ^ (-s₀) / s₀) with hδ
  have ha : 0 ≤ y ^ (1 - s₀) / (s₀ - 1) := div_nonneg (Real.rpow_nonneg hy.le _) (by linarith)
  have hb : 0 ≤ y ^ (-s₀) / s₀ := div_nonneg (Real.rpow_nonneg hy.le _) (by linarith)
  have h0 : ‖D s₀‖ ≤ δ := by
    have := norm_sSer_sub_iArc_le hA hs₀ hy hm0
    rw [norm_sub_rev] at this
    refine this.trans ?_
    rw [hδ, ← hE, show E * y ^ (1 - s₀) / (Real.pi * (s₀ - 1)) = E / Real.pi * (y ^ (1 - s₀) / (s₀
        - 1)) by
      field_simp]
    gcongr; linarith
  have h1 : ‖D (s₀ + 1)‖ ≤ δ := by
    have := norm_sSer_sub_iArc_le hA (s := s₀ + 1) (by linarith) hy hm0
    rw [norm_sub_rev, show 1 - (s₀ + 1) = -s₀ by ring, show s₀ + 1 - 1 = s₀ by ring] at this
    refine this.trans ?_
    rw [hδ, ← hE, show E * y ^ (-s₀) / (Real.pi * s₀) = E / Real.pi * (y ^ (-s₀) / s₀)
        by field_simp]
    gcongr; linarith
  set β := E / Real.pi * ((√2 * y) ^ (-s₀) + (√2 * y) ^ (-(s₀ - k))) with hβdef
  have hx0 : 0 < √2 * y := by positivity
  have hβ0 : 0 ≤ β := by positivity
  have hjk : ∀ j : ℕ, j < k → s₀ - k ≤ s₀ - (j + 1) := by
    intro j hj
    have : ((j : ℝ) + 1) ≤ k := by exact_mod_cast hj
    linarith
  have hB : ∀ j : ℕ, j < k → ‖bArc A m y (s₀ - (j + 1))‖ ≤ β := by
    intro j hj
    refine (norm_bArc_le m hA hy _).trans ?_
    have hx := rpow_neg_le_add hx0 (hjk j hj) (show s₀ - (j + 1) ≤ s₀ by
      have := Nat.cast_nonneg (α := ℝ) j; linarith)
    calc (√2 * y) ^ (-(s₀ - (j + 1))) * E / Real.pi = E / Real.pi * (√2 * y) ^ (-(s₀ - (j + 1)))
        := by ring
      _ ≤ β := by rw [hβdef]; gcongr
  have hsz : ∀ j : ℕ, j < k → |s₀ - (j + 1)| + A ≤ m := fun j hj =>
    hsize _ (hjk j hj) (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have := (descent_bound hm hA hβ0 hrec h0 h1 k hsz hB).1
  refine this.trans (le_of_eq ?_)
  rw [hδ, hβdef]; ring

/-- `y^{1−s₀}/(s₀−1) + y^{−s₀}/s₀ + k((√2y)^{−s₀} + (√2y)^{−(s₀−k)})` at
`s₀ = ⌊r/2⌋ + 2 − r/2 ∈ [3/2, 2]`,
`k = ⌊r/2⌋ + 2`, bounded free of parity. -/
theorem poly_neg_half_le (r : ℕ) {y : ℝ} (hy : 0 < y) :
    let k : ℕ := r / 2 + 2
    let s₀ : ℝ := k - r / 2
    y ^ (1 - s₀) / (s₀ - 1) + y ^ (-s₀) / s₀ + k * ((√2 * y) ^ (-s₀) + (√2 * y) ^ (-(s₀ - k))) ≤
      2 * (y ^ (-(1 : ℝ)) + y ^ (-(1 / 2 : ℝ))) + (y ^ (-(2 : ℝ)) + y ^ (-(3 / 2 : ℝ))) +
        ((r : ℝ) / 2 + 2) * ((√2 * y) ^ (-(2 : ℝ)) + (√2 * y) ^ (-(3 / 2 : ℝ)) + (√2 * y) ^ ((r :
            ℝ) / 2)) := by
  intro k s₀
  have hk : (k : ℝ) = ((r / 2 : ℕ) : ℝ) + 2 := by simp [k]
  have hdiv : (2 : ℝ) * ((r / 2 : ℕ) : ℝ) ≤ r ∧ (r : ℝ) ≤ 2 * ((r / 2 : ℕ) : ℝ) + 1 := by
    constructor
    · exact_mod_cast Nat.mul_div_le r 2
    · have : r ≤ 2 * (r / 2) + 1 := by omega
      exact_mod_cast this
  have hs1 : 3 / 2 ≤ s₀ := by simp only [s₀]; rw [hk]; linarith [hdiv.2]
  have hs2 : s₀ ≤ 2 := by simp only [s₀]; rw [hk]; linarith [hdiv.1]
  have hx0 : 0 < √2 * y := by positivity
  have e1 : y ^ (1 - s₀) / (s₀ - 1) ≤ 2 * (y ^ (-(1 : ℝ)) + y ^ (-(1 / 2 : ℝ))) := by
    have h := rpow_neg_le_add hy (a := 1 / 2) (b := 1) (t := s₀ - 1) (by linarith) (by linarith)
    rw [show -(s₀ - 1) = 1 - s₀ by ring] at h
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ y ^ (-(1 : ℝ)) + y ^ (-(1 / 2 : ℝ)) := by positivity
    nlinarith
  have e2 : y ^ (-s₀) / s₀ ≤ y ^ (-(2 : ℝ)) + y ^ (-(3 / 2 : ℝ)) := by
    have h := rpow_neg_le_add hy (a := 3 / 2) (b := 2) (t := s₀) hs1 hs2
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ y ^ (-(2 : ℝ)) + y ^ (-(3 / 2 : ℝ)) := by positivity
    nlinarith
  have e3 : (√2 * y) ^ (-s₀) ≤ (√2 * y) ^ (-(2 : ℝ)) + (√2 * y) ^ (-(3 / 2 : ℝ)) :=
    rpow_neg_le_add hx0 hs1 hs2
  have e4 : (√2 * y) ^ (-(s₀ - k)) = (√2 * y) ^ ((r : ℝ) / 2) := by
    congr 1; simp only [s₀]; ring
  have e5 : (k : ℝ) ≤ (r : ℝ) / 2 + 2 := by rw [hk]; linarith [hdiv.1]
  rw [e4]
  have : 0 ≤ (√2 * y) ^ (-s₀) + (√2 * y) ^ ((r : ℝ) / 2) := by positivity
  calc y ^ (1 - s₀) / (s₀ - 1) + y ^ (-s₀) / s₀ + k * ((√2 * y) ^ (-s₀) + (√2 * y) ^ ((r : ℝ) / 2))
      ≤ 2 * (y ^ (-(1 : ℝ)) + y ^ (-(1 / 2 : ℝ))) + (y ^ (-(2 : ℝ)) + y ^ (-(3 / 2 : ℝ))) +
          ((r : ℝ) / 2 + 2) * ((√2 * y) ^ (-s₀) + (√2 * y) ^ ((r : ℝ) / 2)) := by
        gcongr
    _ ≤ _ := by gcongr

/-- **The major arc at `s = −r/2`**: for `A ≥ 0`, `y > 0`, `m ≥ A + r/2 + 2`,
`‖I_y(−r/2) − S(−r/2, m)‖ ≤ (e^{A/(2y)+my}/π) · P_r(y)` with the explicit
`P_r(y) = 2(y^{−1} + y^{−1/2}) + y^{−2} + y^{−3/2} + (r/2 + 2)((√2y)^{−2} + (√2y)^{−3/2} +
    (√2y)^{r/2})`. -/
theorem norm_iArc_sub_sSer_neg_half (r : ℕ) {A m y : ℝ} (hA : 0 ≤ A) (hy : 0 < y)
    (hm : A + (r : ℝ) / 2 + 2 ≤ m) :
    ‖iArc A m y (-((r : ℝ) / 2)) - sSer A m (-((r : ℝ) / 2))‖ ≤
      Real.exp (A / (2 * y) + m * y) / Real.pi *
        (2 * (y ^ (-(1 : ℝ)) + y ^ (-(1 / 2 : ℝ))) + (y ^ (-(2 : ℝ)) + y ^ (-(3 / 2 : ℝ))) +
          ((r : ℝ) / 2 + 2) * ((√2 * y) ^ (-(2 : ℝ)) + (√2 * y) ^ (-(3 / 2 : ℝ)) + (√2 * y) ^ ((r
              : ℝ) / 2))) := by
  set k : ℕ := r / 2 + 2 with hkdef
  set s₀ : ℝ := k - r / 2 with hs₀def
  have hk : (k : ℝ) = ((r / 2 : ℕ) : ℝ) + 2 := by simp [hkdef]
  have hdiv : (2 : ℝ) * ((r / 2 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.mul_div_le r 2
  have hdiv2 : (r : ℝ) ≤ 2 * ((r / 2 : ℕ) : ℝ) + 1 := by
    have h := Nat.div_add_mod r 2
    have h2 : r % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have : r ≤ 2 * (r / 2) + 1 := by omega
    exact_mod_cast this
  have hs1 : 1 < s₀ := by rw [hs₀def, hk]; linarith
  have hs2 : s₀ ≤ 2 := by rw [hs₀def, hk]; linarith
  have hsk : s₀ - k = -((r : ℝ) / 2) := by rw [hs₀def]; ring
  have hm1 : 1 ≤ m := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  have hsize : ∀ t, s₀ - k ≤ t → t ≤ s₀ → |t| + A ≤ m := by
    intro t h1 h2
    rw [hsk] at h1
    have : |t| ≤ (r : ℝ) / 2 + 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have main := norm_iArc_sub_sSer_le k hA hy hm1 hs1 hsize
  calc ‖iArc A m y (-((r : ℝ) / 2)) - sSer A m (-((r : ℝ) / 2))‖
      = ‖iArc A m y (s₀ - k) - sSer A m (s₀ - k)‖ := by rw [hsk]
    _ ≤ _ := main
    _ ≤ _ := mul_le_mul_of_nonneg_left (poly_neg_half_le r hy) (by positivity)

/-- At the saddle `y = √(A/m)` the exponential is `e^{(3/2)√(Am)}`. -/
theorem saddle_exp {A m : ℝ} (hA : 0 < A) (hm : 0 < m) :
    A / (2 * √(A / m)) + m * √(A / m) = 3 / 2 * √(A * m) := by
  obtain ⟨a, ha, rfl⟩ : ∃ a, 0 < a ∧ A = a ^ 2 := ⟨√A, Real.sqrt_pos.2 hA, (Real.sq_sqrt
      hA.le).symm⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b, 0 < b ∧ m = b ^ 2 := ⟨√m, Real.sqrt_pos.2 hm, (Real.sq_sqrt
      hm.le).symm⟩
  rw [show a ^ 2 / b ^ 2 = (a / b) ^ 2 by ring, show a ^ 2 * b ^ 2 = (a * b) ^ 2 by ring,
    Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
  field_simp
  ring

/-- **At the saddle** `y = √(A/m)`: `‖I_y(−r/2) − S(−r/2, m)‖ ≤ e^{(3/2)√(Am)} P_r(√(A/m)) / π`
(`A > 0`, `m ≥ A + r/2 + 2`); the main term `S(−r/2, m)` is of size `e^{2√(Am)}` times a power of
`m`. -/
theorem norm_iArc_sub_sSer_saddle (r : ℕ) {A m : ℝ} (hA : 0 < A) (hm : A + (r : ℝ) / 2 + 2 ≤ m) :
    ‖iArc A m (√(A / m)) (-((r : ℝ) / 2)) - sSer A m (-((r : ℝ) / 2))‖ ≤
      Real.exp (3 / 2 * √(A * m)) / Real.pi *
        (2 * (√(A / m) ^ (-(1 : ℝ)) + √(A / m) ^ (-(1 / 2 : ℝ))) +
          (√(A / m) ^ (-(2 : ℝ)) + √(A / m) ^ (-(3 / 2 : ℝ))) +
          ((r : ℝ) / 2 + 2) * ((√2 * √(A / m)) ^ (-(2 : ℝ)) + (√2 * √(A / m)) ^ (-(3 / 2 : ℝ)) +
            (√2 * √(A / m)) ^ ((r : ℝ) / 2))) := by
  have hm0 : 0 < m := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  have h := norm_iArc_sub_sSer_neg_half r hA.le (Real.sqrt_pos.2 (div_pos hA hm0)) hm
  rwa [saddle_exp hA hm0] at h

end

end

end MetaMathlibExt.ColoredPartitionsJensen
