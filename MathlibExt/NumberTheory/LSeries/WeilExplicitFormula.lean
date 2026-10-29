/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.RiemannXiZeros
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import MathlibExt.Analysis.Complex.RectangleResidue
import MathlibExt.Analysis.SpecialFunctions.Gamma.DigammaAsymptotics
import MathlibExt.NumberTheory.LSeries.LiouvilleSummatory
import MathlibExt.NumberTheory.LSeries.RiemannXiLogDeriv
import MathlibExt.NumberTheory.LSeries.RiemannZetaLogDerivZeros
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Weil's explicit formula

Let `h` be holomorphic and even on a strip `|Re s| ≤ 1/2 + ε` and `O(|s|^{-1-ε})` there. Moving the
line of integration across the critical strip and using the functional equation `ξ(1 - s) = ξ(s)`,
the sum of `h(ρ - 1/2)` over the nontrivial zeros `ρ` of `ζ` with `Im ρ > 0` is
`(1 / 2π) ∫ ξ'/ξ(1/2 + s) h(s) dt` along `Re s = 1/2 + ε`. Splitting `ξ'/ξ` into `ζ'/ζ` and the
logarithmic derivative of the Gamma factor gives Weil's explicit formula, relating the zeros to the
prime powers through the Fourier transform of `h` on the imaginary axis.

All sums over zeros run over a family `z` listing the zeros of `ξ` with multiplicity.

## Main statements

* `RiemannXi.deriv_riemannXi_one_sub`, `RiemannXi.logDeriv_riemannXi_one_sub`: the functional
  equation for `ξ'` and `ξ'/ξ`.
* `RiemannXi.logDeriv_riemannXi_eq`:
  `ξ'/ξ(s) = ζ'/ζ(s) + 1/(s - 1) - (log π)/2 + ψ(s/2 + 1)/2`.
* `RiemannXi.hasSum_zeros_eq_integral_logDeriv_riemannXi`: the sum of `h(ρ - 1/2)` over the zeros
  with `Im ρ > 0` as a contour integral of `ξ'/ξ`.
* `RiemannXi.weil_explicit_formula`: **Weil's explicit formula**
  `∑_{Im ρ > 0} h(ρ - 1/2) + ∑_n Λ(n)/√n ĥ₀(log n)
    = h(1/2) - (1/2) log π ĥ₀(0) + (1/2) ∫ ψ(1/4 + iπt) h₀(t) dt`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Complex FourierTransform

namespace RiemannXi

/-! ### Auxiliary estimates -/

section Auxiliary

/-- A function holomorphic on the strip `|Re s| ≤ 1/2 + ε` and `O(|s|^{-1-ε})` for `|s| ≥ 1` is
`O((1 + |s|)^{-1-ε})` on the whole strip. -/
private lemma exists_norm_le_one_add_norm_rpow {ε : ℝ} (hε : 0 < ε) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h {s | |s.re| ≤ 1 / 2 + ε})
    (hdecay : ∃ C : ℝ, ∀ s : ℂ, |s.re| ≤ 1 / 2 + ε → 1 ≤ ‖s‖ → ‖h s‖ ≤ C * ‖s‖ ^ (-1 - ε)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, |s.re| ≤ 1 / 2 + ε → ‖h s‖ ≤ M * (1 + ‖s‖) ^ (-1 - ε) := by
  obtain ⟨C, hC⟩ := hdecay
  have hK : IsCompact ({s : ℂ | |s.re| ≤ 1 / 2 + ε} ∩ Metric.closedBall 0 1) :=
    (isCompact_closedBall 0 1).inter_left
      (isClosed_le (continuous_abs.comp continuous_re) continuous_const)
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (hh.continuousOn.mono inter_subset_left)
  set P : ℝ := (2 : ℝ) ^ (1 + ε) with hP
  have hPpos : 0 < P := by positivity
  have h2 : (2 : ℝ) ^ (-1 - ε) = P⁻¹ := by
    rw [show (-1 - ε) = -(1 + ε) by ring, Real.rpow_neg (by norm_num)]
  refine ⟨(|C| + |M₀|) * P, by positivity, fun s hs => ?_⟩
  have hpos : 0 < 1 + ‖s‖ := by positivity
  have hq0 : 0 ≤ (1 + ‖s‖) ^ (-1 - ε) := by positivity
  rcases le_or_gt 1 ‖s‖ with h1 | h1
  · have hb := hC s hs h1
    have hle : ‖s‖ ^ (-1 - ε) ≤ ((1 + ‖s‖) / 2) ^ (-1 - ε) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    rw [Real.div_rpow hpos.le (by norm_num), h2, div_inv_eq_mul] at hle
    have hn0 : 0 ≤ ‖s‖ ^ (-1 - ε) := by positivity
    have h3 : C * ‖s‖ ^ (-1 - ε) ≤ |C| * ‖s‖ ^ (-1 - ε) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hn0
    have h4 : |C| * ‖s‖ ^ (-1 - ε) ≤ |C| * ((1 + ‖s‖) ^ (-1 - ε) * P) :=
      mul_le_mul_of_nonneg_left hle (abs_nonneg C)
    have h5 : 0 ≤ |M₀| * P * (1 + ‖s‖) ^ (-1 - ε) := by positivity
    nlinarith
  · have hb := hM₀ s ⟨hs, by simpa using h1.le⟩
    have hle : (2 : ℝ) ^ (-1 - ε) ≤ (1 + ‖s‖) ^ (-1 - ε) :=
      Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)
    rw [h2] at hle
    have h3 : |M₀| = |M₀| * P * P⁻¹ := by field_simp
    have h4 : |M₀| * P * P⁻¹ ≤ |M₀| * P * (1 + ‖s‖) ^ (-1 - ε) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have h5 : 0 ≤ |C| * P * (1 + ‖s‖) ^ (-1 - ε) := by positivity
    have := le_abs_self M₀
    nlinarith

/-- A real zero of `ξ` would be a zero of `ζ` on `[0, 1]`; there are none. -/
private lemma im_ne_zero_of_mem_riemannZetaNontrivialZeros {ρ : ℂ}
    (hρ : ρ ∈ riemannZetaNontrivialZeros) : ρ.im ≠ 0 := by
  intro h
  have hρ' : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [h]
  have hz := hρ.1
  rw [hρ'] at hz
  rcases eq_or_lt_of_le hρ.2.1 with h0 | h0
  · rw [← h0] at hz; simp [riemannZeta_zero] at hz
  rcases eq_or_lt_of_le hρ.2.2 with h1 | h1
  · rw [h1] at hz; exact riemannZeta_ne_zero_of_one_le_re (by simp) hz
  exact riemannZeta_ofReal_ne_zero_of_pos_of_lt_one h0 h1 hz

private lemma differentiableAt_logDeriv_riemannXi {w : ℂ} (hw : riemannXi w ≠ 0) :
    DifferentiableAt ℂ (logDeriv riemannXi) w := by
  have ha := differentiable_riemannXi.analyticAt w
  have : logDeriv riemannXi = fun u => deriv riemannXi u / riemannXi u := by
    funext u; rw [logDeriv_apply]
  rw [this]
  exact ha.deriv.differentiableAt.div ha.differentiableAt hw

private lemma continuous_logDeriv_riemannXi_mul_line {ε : ℝ} (hε : 0 < ε) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h {s | |s.re| ≤ 1 / 2 + ε}) :
    Continuous fun t : ℝ => logDeriv riemannXi (1 / 2 + (((1 / 2 + ε : ℝ) : ℂ) + t * I)) *
      h (((1 / 2 + ε : ℝ) : ℂ) + t * I) := by
  have hpath : Continuous fun t : ℝ => ((1 / 2 + ε : ℝ) : ℂ) + t * I := by fun_prop
  refine Continuous.mul ?_ (hh.continuousOn.comp_continuous hpath fun t => ?_)
  · refine continuous_iff_continuousAt.mpr fun t => ?_
    have hne : riemannXi (1 / 2 + (((1 / 2 + ε : ℝ) : ℂ) + t * I)) ≠ 0 := by
      intro h0
      have := ((riemannXi_eq_zero_iff _).mp h0).2.2
      simp at this; linarith
    exact (differentiableAt_logDeriv_riemannXi hne).continuousAt.comp
      (f := fun t : ℝ => 1 / 2 + (((1 / 2 + ε : ℝ) : ℂ) + t * I))
      ((continuous_const.add hpath).continuousAt)
  · change |(((1 / 2 + ε : ℝ) : ℂ) + t * I).re| ≤ 1 / 2 + ε
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero,
      add_zero]
    rw [abs_of_pos (by linarith)]

/-- The principal part of `ξ'/ξ(1/2 + s) h(s)` at a zero of order `m`. -/
private lemma exists_eventually_logDeriv_riemannXi_mul_eq {ε : ℝ} {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h {s | |s.re| ≤ 1 / 2 + ε})
    {p : ℂ} (hp : |p.re| < 1 / 2 + ε) {m : ℕ} (hm : analyticOrderAt riemannXi (1 / 2 + p) = m) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧ ∀ᶠ s in 𝓝[≠] p,
      logDeriv riemannXi (1 / 2 + s) * h s = (m : ℂ) * h p / (s - p) + φ s := by
  obtain ⟨ξ₁, hξ₁a, hξ₁0, hξ₁e⟩ :=
    (differentiable_riemannXi.analyticAt (1 / 2 + p)).analyticOrderAt_eq_natCast.mp hm
  have ht : Tendsto (fun s : ℂ => 1 / 2 + s) (𝓝 p) (𝓝 (1 / 2 + p)) :=
    (continuous_const.add continuous_id).tendsto p
  have hE : AnalyticAt ℂ (fun s => ξ₁ (1 / 2 + s)) p :=
    hξ₁a.comp (analyticAt_const.add analyticAt_id)
  have hf : ∀ᶠ s in 𝓝[≠] p, (fun s => riemannXi (1 / 2 + s)) s =
      (s - p) ^ (m : ℤ) * (fun s => ξ₁ (1 / 2 + s)) s := by
    filter_upwards [nhdsWithin_le_nhds (ht.eventually hξ₁e)] with s hs
    rw [hs, zpow_natCast, smul_eq_mul, show (1 / 2 + s - (1 / 2 + p)) = s - p by ring]
  have hL := Complex.eventually_logDeriv_eq_of_eq_zpow_mul hE hξ₁0 hf
  have hstrip : {s : ℂ | |s.re| ≤ 1 / 2 + ε} ∈ 𝓝 p := by
    have ho : IsOpen {s : ℂ | |s.re| < 1 / 2 + ε} :=
      isOpen_lt (continuous_abs.comp continuous_re) continuous_const
    exact Filter.mem_of_superset (ho.mem_nhds hp) fun s hs => by
      simp only [mem_ofPred_eq] at hs ⊢; exact hs.le
  have hH : AnalyticAt ℂ h p := hh.analyticAt hstrip
  have hΨ : DifferentiableAt ℂ
      (fun s => deriv (fun s => ξ₁ (1 / 2 + s)) s / ξ₁ (1 / 2 + s) * h s) p :=
    (hE.deriv.differentiableAt.div hE.differentiableAt hξ₁0).mul hH.differentiableAt
  apply Complex.exists_eventually_eq_div_sub_add_of_analyticAt (c := (m : ℂ)) hH hΨ
  filter_upwards [hL] with s hs
  have e : logDeriv riemannXi (1 / 2 + s) = logDeriv (fun s => riemannXi (1 / 2 + s)) s := by
    rw [logDeriv_apply, logDeriv_apply, deriv_comp_const_add riemannXi (1 / 2) s]
  rw [e, hs, logDeriv_apply]
  push_cast
  ring

/-- **The rectangle identity.** For `T > 0` not the ordinate of a zero, the integral of
`F(s) = ξ'/ξ(1/2 + s) h(s)` over the right edge `Re s = 1/2 + ε`, `|Im s| ≤ T`, minus the top edge,
is `2πi ∑_{0 < γ < T} h(ρ - 1/2)`; the left and bottom edges are absorbed by the oddness of `F`. -/
private lemma rectangle_identity {ε : ℝ} (hε : 0 < ε) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h {s | |s.re| ≤ 1 / 2 + ε}) (hsymm : ∀ s, h (-s) = h s)
    {ι : Type*} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w)
    {T : ℝ} (hT : 0 < T) (hTz : ∀ ρ ∈ riemannZetaNontrivialZeros, ρ.im ≠ T) (NF : Finset ι)
    (hNF : ∀ n, n ∈ NF ↔ 0 < (z n).im ∧ (z n).im < T) (F : ℂ → ℂ)
    (hF : ∀ s, F s = logDeriv riemannXi (1 / 2 + s) * h s) :
    I * (∫ t in (-T)..T, F (((1 / 2 + ε : ℝ) : ℂ) + t * I)) -
        (∫ x in (-(1 / 2 + ε))..(1 / 2 + ε), F (x + T * I)) =
      2 * (Real.pi : ℂ) * I * ∑ n ∈ NF, h (z n - 1 / 2) := by
  classical
  set c : ℝ := 1 / 2 + ε with hc
  have hc0 : 0 < c := by positivity
  have hodd : ∀ s, F (-s) = -F s := by
    intro s
    rw [hF, hF, hsymm, show (1 : ℂ) / 2 + -s = 1 - (1 / 2 + s) by ring,
      logDeriv_riemannXi_one_sub]
    ring
  set Z : Finset ℂ := NF.image (fun n => z n - 1 / 2) with hZ
  let mo : ℂ → ℕ := fun p => (analyticOrderAt riemannXi (1 / 2 + p)).toNat
  let r : ℂ → ℂ := fun p => (mo p : ℂ) * h p
  have hZprop : ∀ p ∈ Z, |p.re| ≤ 1 / 2 ∧ 0 < p.im ∧ p.im < T := by
    intro p hp
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
    have hm := mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz n
    obtain ⟨h1, h2⟩ := (hNF n).mp hn
    refine ⟨?_, by simpa using h1, by simpa using h2⟩
    have : (z n - 1 / 2).re = (z n).re - 1 / 2 := by simp
    rw [this, abs_le]
    constructor <;> linarith [hm.2.1, hm.2.2]
  have hloc : ∀ p ∈ Z, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, F s = r p / (s - p) + φ s := by
    intro p hp
    have hre := (hZprop p hp).1
    have hm : analyticOrderAt riemannXi (1 / 2 + p) = (mo p : ℕ) :=
      (ENat.natCast_toNat (analyticOrderAt_riemannXi_ne_top _)).symm
    obtain ⟨φ, h1, h2⟩ :=
      exists_eventually_logDeriv_riemannXi_mul_eq hh (by linarith : |p.re| < 1 / 2 + ε) hm
    refine ⟨φ, h1, ?_⟩
    filter_upwards [h2] with s hs
    rw [hF, hs]
  let z0 : ℂ := ⟨-c, 0⟩
  let w0 : ℂ := ⟨c, T⟩
  have hKre : ∀ s ∈ Set.uIcc z0.re w0.re ×ℂ Set.uIcc z0.im w0.im,
      -c ≤ s.re ∧ s.re ≤ c ∧ 0 ≤ s.im ∧ s.im ≤ T := by
    intro s hs
    obtain ⟨h1, h2⟩ := mem_reProdIm.mp hs
    rw [show z0.re = -c from rfl, show w0.re = c from rfl,
      Set.uIcc_of_le (by linarith)] at h1
    rw [show z0.im = 0 from rfl, show w0.im = T from rfl, Set.uIcc_of_le (by linarith)] at h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have hdiff : ∀ s ∈ Set.uIcc z0.re w0.re ×ℂ Set.uIcc z0.im w0.im, s ∉ Z →
      DifferentiableWithinAt ℂ F (Set.uIcc z0.re w0.re ×ℂ Set.uIcc z0.im w0.im) s := by
    intro s hsK hsZ
    obtain ⟨k1, k2, k3, k4⟩ := hKre s hsK
    have hξ : riemannXi (1 / 2 + s) ≠ 0 := by
      intro h0
      have hnt := (riemannXi_eq_zero_iff _).mp h0
      have him : (1 / 2 + s).im = s.im := by simp
      have h1 := im_ne_zero_of_mem_riemannZetaNontrivialZeros hnt
      have h2 := hTz _ hnt
      rw [him] at h1 h2
      obtain ⟨n, hn⟩ := exists_eq_of_card_eq_analyticOrderAt hz hnt
      have hnNF : n ∈ NF := (hNF n).mpr ⟨by rw [hn, him]; exact lt_of_le_of_ne k3 (Ne.symm h1),
        by rw [hn, him]; exact lt_of_le_of_ne k4 h2⟩
      exact hsZ (Finset.mem_image.mpr ⟨n, hnNF, by rw [hn]; ring⟩)
    have hd1 : DifferentiableAt ℂ (fun s => logDeriv riemannXi (1 / 2 + s)) s :=
      (differentiableAt_logDeriv_riemannXi hξ).comp s
        ((differentiableAt_const _).add differentiableAt_id)
    have hsub : Set.uIcc z0.re w0.re ×ℂ Set.uIcc z0.im w0.im ⊆ {s : ℂ | |s.re| ≤ 1 / 2 + ε} :=
      fun u hu => by
        obtain ⟨u1, u2, -, -⟩ := hKre u hu
        exact abs_le.mpr ⟨u1, u2⟩
    have hd2 : DifferentiableWithinAt ℂ h (Set.uIcc z0.re w0.re ×ℂ Set.uIcc z0.im w0.im) s :=
      (hh s (hsub hsK)).mono hsub
    exact (hd1.differentiableWithinAt.mul hd2).congr (fun y _ => hF y) (hF s)
  obtain ⟨g, hg, hfg⟩ := Complex.exists_differentiableOn_eq_add_sum_div_sub _ Z r F hloc hdiff
  have hin : ∀ p ∈ Z, z0.re < p.re ∧ p.re < w0.re ∧ z0.im < p.im ∧ p.im < w0.im := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hZprop p hp
    change -c < p.re ∧ p.re < c ∧ 0 < p.im ∧ p.im < T
    have := abs_le.mp h1
    exact ⟨by linarith, by linarith, h2, h3⟩
  have hRS := RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum ⟨z0, w0⟩ Z r F g
    hin hg hfg
  simp only [RectilinearRectangle.boundaryIntegral, z0, w0, smul_eq_mul] at hRS
  -- the residue sum
  have hsum : ∑ p ∈ Z, r p = ∑ n ∈ NF, h (z n - 1 / 2) := by
    rw [Finset.sum_comp (fun p => h p) (fun n => z n - 1 / 2)]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨-, hp2, hp3⟩ := hZprop p hp
    have hfib : Finite {n // z n = 1 / 2 + p} := finite_of_card_eq_analyticOrderAt hz _
    have hcard := hz (1 / 2 + p)
    rw [ENat.card_eq_coe_natCard, Nat.subtype_card (NF.filter (fun n => z n - 1 / 2 = p)) (by
      intro n
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨-, h⟩; linear_combination h
      · intro h
        refine ⟨(hNF n).mpr ⟨?_, ?_⟩, by rw [h]; ring⟩
        · rw [h]; simpa using hp2
        · rw [h]; simpa using hp3),
      ← ENat.natCast_toNat (analyticOrderAt_riemannXi_ne_top _)] at hcard
    have hc' : (NF.filter (fun n => z n - 1 / 2 = p)).card = mo p := by exact_mod_cast hcard
    rw [hc', nsmul_eq_mul]
  -- oddness on the bottom edge and the left edge
  have hbot : ∫ x in (-c)..c, F ((x : ℂ) + ((0 : ℝ) : ℂ) * I) = 0 := by
    have e : (fun x : ℝ => F ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) = fun x : ℝ => F (x : ℂ) := by
      funext x; simp
    rw [e]
    have h1 : ∫ x in (-c)..c, F ((-x : ℝ) : ℂ) = ∫ x in (-c)..c, F (x : ℂ) := by
      rw [intervalIntegral.integral_comp_neg (fun x : ℝ => F (x : ℂ)), neg_neg]
    have h2 : ∫ x in (-c)..c, F ((-x : ℝ) : ℂ) = -∫ x in (-c)..c, F (x : ℂ) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [ofReal_neg]
      exact hodd _
    have := h1.symm.trans h2
    linear_combination this / 2
  have hleft : ∫ y in (0 : ℝ)..T, F (((-c : ℝ) : ℂ) + (y : ℂ) * I) =
      -∫ y in (-T)..0, F ((c : ℂ) + (y : ℂ) * I) := by
    have h1 : ∫ y in (0 : ℝ)..T, F ((c : ℂ) + ((-y : ℝ) : ℂ) * I) =
        ∫ y in (-T)..0, F ((c : ℂ) + (y : ℂ) * I) := by
      rw [intervalIntegral.integral_comp_neg (fun y : ℝ => F ((c : ℂ) + (y : ℂ) * I)), neg_zero]
    rw [← h1, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [← hodd]
    congr 1
    push_cast
    ring
  have hGc : Continuous fun t : ℝ => F ((c : ℂ) + (t : ℂ) * I) := by
    simpa only [hF] using continuous_logDeriv_riemannXi_mul_line hε hh
  have hsplit : ∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I) =
      (∫ t in (-T)..0, F ((c : ℂ) + (t : ℂ) * I)) +
        ∫ t in (0 : ℝ)..T, F ((c : ℂ) + (t : ℂ) * I) :=
    (intervalIntegral.integral_add_adjacent_intervals (hGc.intervalIntegrable _ _)
      (hGc.intervalIntegrable _ _)).symm
  rw [hsplit, ← hsum]
  linear_combination hRS - hbot + I * hleft

private lemma integrable_logDeriv_riemannXi_mul_line {ε : ℝ} (hε : 0 < ε) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h {s | |s.re| ≤ 1 / 2 + ε}) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s : ℂ, |s.re| ≤ 1 / 2 + ε → ‖h s‖ ≤ M * (1 + ‖s‖) ^ (-1 - ε)) :
    Integrable fun t : ℝ =>
      logDeriv riemannXi (1 / 2 + (((1 / 2 + ε : ℝ) : ℂ) + t * I)) *
        h (((1 / 2 + ε : ℝ) : ℂ) + t * I) := by
  obtain ⟨KA, hKA⟩ := exists_norm_logDeriv_riemannXi_le hε
  have hcont := continuous_logDeriv_riemannXi_mul_line hε hh
  set B : ℝ := |KA| + Real.log (2 + ε) + 2 / ε with hB
  have hl2 : 0 ≤ Real.log (2 + ε) := Real.log_nonneg (by linarith)
  have hB0 : 0 ≤ B := by positivity
  have hint := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 1 + ε / 2)
    (by rw [Module.finrank_self]; push_cast; linarith)).const_mul (B * M)
  refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs]
  set x : ℝ := 1 + |t| with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith [abs_nonneg t]
  have hx0 : 0 < x := by linarith
  -- the `ξ'/ξ` factor
  set w : ℂ := 1 / 2 + (((1 / 2 + ε : ℝ) : ℂ) + t * I) with hw
  have hwre : w.re = 1 + ε := by simp [hw]; ring
  have hwim : w.im = t := by simp [hw]
  have hwn : ‖w‖ ≤ 1 + ε + |t| := by
    calc ‖w‖ ≤ |w.re| + |w.im| := norm_le_abs_re_add_abs_im _
      _ = 1 + ε + |t| := by rw [hwre, hwim, abs_of_pos (by linarith)]
  have hL := hKA w (by rw [hwre])
  have hlog : Real.log (‖w‖ + 1) ≤ Real.log (2 + ε) + 2 / ε * x ^ (ε / 2) := by
    have h1 : ‖w‖ + 1 ≤ (2 + ε) * x := by rw [hx]; nlinarith [abs_nonneg t]
    have h2 : Real.log (‖w‖ + 1) ≤ Real.log (2 + ε) + Real.log x := by
      rw [← Real.log_mul (by linarith) hx0.ne']
      exact Real.log_le_log (by positivity) h1
    have h3 : Real.log x ≤ x ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div hx0.le (by positivity)
    have h4 : x ^ (ε / 2) / (ε / 2) = 2 / ε * x ^ (ε / 2) := by field_simp
    linarith
  have hxe : 1 ≤ x ^ (ε / 2) := Real.one_le_rpow hx1 (by positivity)
  have hL' : ‖logDeriv riemannXi w‖ ≤ B * x ^ (ε / 2) := by
    have h1 : |KA| * 1 ≤ |KA| * x ^ (ε / 2) := mul_le_mul_of_nonneg_left hxe (abs_nonneg _)
    have h2 : Real.log (2 + ε) * 1 ≤ Real.log (2 + ε) * x ^ (ε / 2) :=
      mul_le_mul_of_nonneg_left hxe hl2
    have h3 := le_abs_self KA
    rw [hB]
    nlinarith
  -- the `h` factor
  set u : ℂ := ((1 / 2 + ε : ℝ) : ℂ) + t * I with hu
  have hure : |u.re| ≤ 1 / 2 + ε := by
    simp only [hu, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one,
      sub_zero, add_zero]
    rw [abs_of_pos (by linarith)]
  have hun : x ≤ 1 + ‖u‖ := by
    have : |t| ≤ ‖u‖ := by
      have := abs_im_le_norm u
      simpa [hu] using this
    rw [hx]; linarith
  have hH : ‖h u‖ ≤ M * x ^ (-1 - ε) :=
    (hM u hure).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx0 hun (by linarith)) hM0)
  have hpow : x ^ (ε / 2) * x ^ (-1 - ε) = x ^ (-(1 + ε / 2)) := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [norm_mul]
  calc ‖logDeriv riemannXi w‖ * ‖h u‖ ≤ (B * x ^ (ε / 2)) * (M * x ^ (-1 - ε)) :=
        mul_le_mul hL' hH (norm_nonneg _) (by positivity)
    _ = B * M * x ^ (-(1 + ε / 2)) := by rw [← hpow]; ring

private lemma summable_ite_apply_sub_half {ε : ℝ} (hε : 0 < ε) {h : ℂ → ℂ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ s : ℂ, |s.re| ≤ 1 / 2 + ε → ‖h s‖ ≤ M * (1 + ‖s‖) ^ (-1 - ε))
    {ι : Type*} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) :
    Summable fun n => if 0 < (z n).im then h (z n - 1 / 2) else 0 := by
  have hsum : Summable fun n => ‖z n‖ ^ (-1 - ε) :=
    hasGrowthOrderLE_riemannXi.summable_norm_rpow_neg differentiable_riemannXi zero_le_one
      riemannXi_zero_ne_zero hz hε
  refine (hsum.mul_left M).of_norm_bounded fun n => ?_
  have hm := mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz n
  have hz0 : z n ≠ 0 := ne_zero_of_card_eq_analyticOrderAt hz n
  have hb : ‖h (z n - 1 / 2)‖ ≤ M * ‖z n‖ ^ (-1 - ε) := by
    refine (hM _ ?_).trans (mul_le_mul_of_nonneg_left ?_ hM0)
    · have : (z n - 1 / 2).re = (z n).re - 1 / 2 := by simp
      rw [this, abs_le]
      constructor <;> linarith [hm.2.1, hm.2.2]
    · refine Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz0) ?_ (by linarith)
      have := norm_sub_norm_le (z n) (z n - 1 / 2)
      rw [sub_sub_cancel] at this
      have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      linarith
  split_ifs
  · exact hb
  · rw [norm_zero]; positivity

end Auxiliary

/-- **The zero sum as a contour integral of `ξ'/ξ`.** Let `ε > 0` and let `h` be holomorphic on the
strip `|Re s| ≤ 1/2 + ε`, even, and `O(|s|^{-1-ε})` there. Then
`∑_{Im ρ > 0} h(ρ - 1/2) = (1 / 2π) ∫ ξ'/ξ(1/2 + s) h(s) dt`, the integral along the line
`s = 1/2 + ε + it`, the sum over the nontrivial zeros `ρ` of `ζ` with multiplicity (any family `z`
listing the zeros of `ξ` with multiplicity). -/
theorem hasSum_zeros_eq_integral_logDeriv_riemannXi {ε : ℝ} (hε : 0 < ε) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h {s | |s.re| ≤ 1 / 2 + ε}) (hsymm : ∀ s, h (-s) = h s)
    (hdecay : ∃ C : ℝ, ∀ s : ℂ, |s.re| ≤ 1 / 2 + ε → 1 ≤ ‖s‖ → ‖h s‖ ≤ C * ‖s‖ ^ (-1 - ε))
    {ι : Type*} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) :
    HasSum (fun n => if 0 < (z n).im then h (z n - 1 / 2) else 0)
      (1 / (2 * (Real.pi : ℂ)) * ∫ t : ℝ,
        logDeriv riemannXi (1 / 2 + (((1 / 2 + ε : ℝ) : ℂ) + t * I)) *
          h (((1 / 2 + ε : ℝ) : ℂ) + t * I)) := by
  classical
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_one_add_norm_rpow hε hh hdecay
  have hGint := integrable_logDeriv_riemannXi_mul_line hε hh hM0 hM
  have hsumm := summable_ite_apply_sub_half hε hM0 hM z hz
  set f : ι → ℂ := fun n => if 0 < (z n).im then h (z n - 1 / 2) else 0 with hfdef
  set F : ℂ → ℂ := fun s => logDeriv riemannXi (1 / 2 + s) * h s with hFdef
  set G : ℝ → ℂ := fun t => F (((1 / 2 + ε : ℝ) : ℂ) + t * I) with hGdef
  change HasSum f (1 / (2 * (Real.pi : ℂ)) * ∫ t : ℝ, G t)
  obtain ⟨K, T₁, hT₁, hhor⟩ := exists_good_height_norm_logDeriv_riemannXi_le hε
  choose! Tp hTp1 hTp0 hTpz hTpb using hhor
  have hTp2 : ∀ T ≥ T₁, ∀ ρ ∈ riemannZetaNontrivialZeros, ρ.im ≠ Tp T :=
    fun T hT ρ hρ h => hTpz T hT ρ hρ (by rw [h, abs_of_pos (by linarith [hTp0 T hT])])
  have hTp3 : ∀ T ≥ T₁, ∀ σ : ℝ, -ε ≤ σ → σ ≤ 1 + ε →
      ‖logDeriv riemannXi ((σ : ℂ) + (Tp T : ℂ) * I)‖ ≤ K * Real.log (Tp T) ^ 2 :=
    fun T hT σ h1 h2 => (hTpb T hT σ h1 h2).1
  have hTlo : ∀ T ≥ T₁, T - 1 ≤ Tp T := fun T hT => by
    have := hTp1 T hT; rw [abs_le] at this; linarith
  have htend : Tendsto Tp atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right _ (-1) tendsto_id)
    filter_upwards [eventually_ge_atTop T₁] with T hT
    have := hTlo T hT
    simp only [id]; linarith
  let NF : ℝ → Finset ι := fun T =>
    (finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt hz (Tp T)).toFinset
  have hNFp : ∀ T, ∀ n, n ∈ (NF T).filter (fun n => 0 < (z n).im) ↔
      0 < (z n).im ∧ (z n).im < Tp T := by
    intro T n
    simp only [NF, Finset.mem_filter, Set.Finite.mem_toFinset, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (abs_lt.mp h1).2⟩
    · rintro ⟨h1, h2⟩; exact ⟨abs_lt.mpr ⟨by linarith, h2⟩, h1⟩
  have hid : ∀ T ≥ max T₁ 2, I * (∫ t in (-Tp T)..(Tp T), G t) -
      (∫ x in (-(1 / 2 + ε))..(1 / 2 + ε), F (x + Tp T * I)) =
      2 * (Real.pi : ℂ) * I * ∑ n ∈ NF T, f n := by
    intro T hT
    have hT1 : T₁ ≤ T := le_trans (le_max_left _ _) hT
    have hpos : 0 < Tp T := by linarith [hTlo T hT1, le_max_right T₁ 2]
    rw [rectangle_identity hε hh hsymm z hz hpos (hTp2 T hT1) _ (hNFp T) F (fun s => rfl),
      Finset.sum_filter]
  -- limits
  have hlim1 : Tendsto (fun T => ∫ t in (-Tp T)..(Tp T), G t) atTop (𝓝 (∫ t, G t)) :=
    intervalIntegral_tendsto_integral hGint (tendsto_neg_atTop_atBot.comp htend) htend
  have hlim2 : Tendsto (fun T => ∫ x in (-(1 / 2 + ε))..(1 / 2 + ε), F (x + Tp T * I))
      atTop (𝓝 0) := by
    have hg := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp htend
    have hg' := hg.const_mul (K * M * (2 * (1 / 2 + ε)))
    rw [mul_zero] at hg'
    refine squeeze_zero_norm' ?_ hg'
    filter_upwards [eventually_ge_atTop (max T₁ 2)] with T hT
    have hT1 : T₁ ≤ T := le_trans (le_max_left _ _) hT
    set T' := Tp T with hT'
    have hT'1 : 1 ≤ T' := by linarith [hTlo T hT1, le_max_right T₁ 2]
    have hbound : ∀ x ∈ Set.uIoc (-(1 / 2 + ε)) (1 / 2 + ε),
        ‖F ((x : ℂ) + (T' : ℂ) * I)‖ ≤ K * Real.log T' ^ 2 * (M / T') := by
      intro x hx
      rw [Set.uIoc_of_le (by linarith)] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have e : (1 / 2 : ℂ) + ((x : ℂ) + (T' : ℂ) * I) =
          ((1 / 2 + x : ℝ) : ℂ) + (T' : ℂ) * I := by
        push_cast; ring
      have hL : ‖logDeriv riemannXi (1 / 2 + ((x : ℂ) + (T' : ℂ) * I))‖ ≤
          K * Real.log T' ^ 2 := by
        rw [e]; exact hTp3 T hT1 (1 / 2 + x) (by linarith) (by linarith)
      set u : ℂ := (x : ℂ) + (T' : ℂ) * I with hu
      have hure : |u.re| ≤ 1 / 2 + ε := by
        have : u.re = x := by simp [hu]
        rw [this, abs_le]; constructor <;> linarith
      have hun : T' ≤ ‖u‖ := by
        have := abs_im_le_norm u
        have him : u.im = T' := by simp [hu]
        rw [him, abs_of_pos (by linarith)] at this
        exact this
      have hH : ‖h u‖ ≤ M / T' := by
        refine (hM u hure).trans ?_
        have h1 : (1 + ‖u‖) ^ (-1 - ε) ≤ (1 + ‖u‖) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg u]) (by linarith)
        rw [Real.rpow_neg_one] at h1
        have h2 : (1 + ‖u‖)⁻¹ ≤ 1 / T' := by
          rw [← one_div]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
        calc M * (1 + ‖u‖) ^ (-1 - ε) ≤ M * (1 / T') :=
              mul_le_mul_of_nonneg_left (h1.trans h2) hM0
          _ = M / T' := by ring
      change ‖logDeriv riemannXi (1 / 2 + u) * h u‖ ≤ K * Real.log T' ^ 2 * (M / T')
      rw [norm_mul]
      exact mul_le_mul hL hH (norm_nonneg _) ((norm_nonneg _).trans hL)
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have habs : |1 / 2 + ε - -(1 / 2 + ε)| = 2 * (1 / 2 + ε) := by
      rw [abs_of_pos (by linarith)]; ring
    rw [habs] at hn
    refine hn.trans (le_of_eq ?_)
    simp only [Function.comp, one_mul, add_zero]
    ring
  have hfin : Tendsto NF atTop atTop := by
    refine Filter.tendsto_atTop.mpr fun s => ?_
    filter_upwards [htend.eventually_ge_atTop (∑ n ∈ s, |(z n).im| + 1)] with T hT
    intro n hn
    simp only [NF, Set.Finite.mem_toFinset, mem_ofPred_eq]
    have := Finset.single_le_sum (f := fun n => |(z n).im|) (fun _ _ => abs_nonneg _) hn
    linarith
  have hlim3 : Tendsto (fun T => ∑ n ∈ NF T, f n) atTop (𝓝 (∑' n, f n)) :=
    hsumm.hasSum.comp hfin
  have hA := (hlim1.const_mul I).sub hlim2
  have hB := hlim3.const_mul (2 * (Real.pi : ℂ) * I)
  have heq : (fun T => I * (∫ t in (-Tp T)..(Tp T), G t) -
      ∫ x in (-(1 / 2 + ε))..(1 / 2 + ε), F (x + Tp T * I)) =ᶠ[atTop]
      fun T => 2 * (Real.pi : ℂ) * I * ∑ n ∈ NF T, f n := by
    filter_upwards [eventually_ge_atTop (max T₁ 2)] with T hT using hid T hT
  have hlim := tendsto_nhds_unique (hA.congr' heq) hB
  have hI : I ≠ 0 := I_ne_zero
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hval : ∑' n, f n = 1 / (2 * (Real.pi : ℂ)) * ∫ t, G t := by
    have h1 : I * (∫ t, G t) = I * ((∑' n, f n) * (2 * Real.pi)) := by
      linear_combination hlim
    have h2 := mul_left_cancel₀ hI h1
    rw [h2]
    field_simp
  rw [← hval]
  exact hsumm.hasSum

/-! ### Weil's explicit formula -/

section Weil

private lemma exists_norm_logDeriv_riemannZeta_le_const {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, ∀ w : ℂ, 1 + δ ≤ w.re → ‖logDeriv riemannZeta w‖ ≤ K := by
  obtain ⟨K, -, hK⟩ := exists_norm_logDeriv_riemannZeta_le hδ
  exact ⟨K, fun w hw => by rw [logDeriv_apply]; exact hK w hw⟩

private lemma differentiableAt_digamma_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ Complex.digamma w := by
  have hne : ∀ v : ℂ, 0 < v.re → ∀ m : ℕ, v ≠ -(m : ℂ) := by
    intro v hv m h
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hA : AnalyticAt ℂ Complex.Gamma w := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with v hv
    exact Complex.differentiableAt_Gamma v (hne v hv)
  have h : Complex.digamma = fun v => deriv Complex.Gamma v / Complex.Gamma v := by
    funext v; rfl
  rw [h]
  exact hA.deriv.differentiableAt.div hA.differentiableAt (Complex.Gamma_ne_zero (hne w hw))

private lemma continuousAt_logDeriv_riemannZeta {w : ℂ} (hw : 1 < w.re) :
    ContinuousAt (logDeriv riemannZeta) w := by
  have hA : AnalyticAt ℂ riemannZeta w := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with v hv
    refine differentiableAt_riemannZeta fun h => ?_
    rw [h] at hv; simp at hv
  have h : logDeriv riemannZeta = fun v => deriv riemannZeta v / riemannZeta v := by
    funext v; rw [logDeriv_apply]
  rw [h]
  exact hA.deriv.continuousAt.div hA.continuousAt
    (riemannZeta_ne_zero_of_one_le_re hw.le)

private lemma integrable_of_norm_le_one_add_abs_rpow {g : ℝ → ℂ} (hg : Continuous g) {δ B : ℝ}
    (hδ : 0 < δ)
    (hb : ∀ t : ℝ, ‖g t‖ ≤ B * (1 + |t|) ^ (-1 - δ)) : Integrable g := by
  have hint := (integrable_one_add_norm (E := ℝ) (μ := MeasureTheory.volume) (r := 1 + δ)
    (by rw [Module.finrank_self]; push_cast; linarith)).const_mul B
  refine hint.mono' hg.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs]
  rw [show -(1 + δ) = -1 - δ by ring]
  exact hb t

private lemma one_add_norm_rpow_le_one_add_abs_im_rpow {δ : ℝ} (hδ : 0 ≤ δ) (s : ℂ) :
    (1 + ‖s‖) ^ (-1 - δ) ≤ (1 + |s.im|) ^ (-1 - δ) :=
  Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [Complex.abs_im_le_norm s])
    (by linarith)

private lemma one_add_rpow_le_one_div {δ : ℝ} (hδ : 0 ≤ δ) {x : ℝ} (hx : 1 ≤ x) :
    (1 + x) ^ (-1 - δ) ≤ 1 / x := by
  have h1 : (1 + x) ^ (-1 - δ) ≤ (1 + x) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [Real.rpow_neg_one] at h1
  refine h1.trans ?_
  rw [← one_div]; exact one_div_le_one_div_of_le (by linarith) (by linarith)

private lemma integral_vertical_sub_eq_two_pi_mul_sum_of_div_abs_im {c : ℝ} (hc : 0 < c)
    (F : ℂ → ℂ) (S : Finset ℂ) (r : ℂ → ℂ)
    (hS : ∀ p ∈ S, 0 < p.re ∧ p.re < c)
    (hloc : ∀ p ∈ S, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, F s = r p / (s - p) + φ s)
    (hdiff : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c → s ∉ S →
      DifferentiableWithinAt ℂ F {s : ℂ | 0 ≤ s.re ∧ s.re ≤ c} s)
    (hB : ∃ B : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c → 1 ≤ |s.im| → ‖F s‖ ≤ B / |s.im|)
    (hi0 : Integrable fun t : ℝ => F ((t : ℂ) * I))
    (hic : Integrable fun t : ℝ => F ((c : ℂ) + (t : ℂ) * I)) :
    (∫ t : ℝ, F ((c : ℂ) + (t : ℂ) * I)) - ∫ t : ℝ, F ((t : ℂ) * I) =
      2 * (Real.pi : ℂ) * ∑ p ∈ S, r p := by
  classical
  obtain ⟨B, hB⟩ := hB
  set T₀ : ℝ := 1 + ∑ p ∈ S, |p.im| with hT₀
  have hT₀1 : 1 ≤ T₀ := by
    have : 0 ≤ ∑ p ∈ S, |p.im| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hid : ∀ T ≥ T₀,
      (∫ x : ℝ in (0 : ℝ)..c, F ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
        - (∫ x : ℝ in (0 : ℝ)..c, F ((x : ℂ) + (T : ℂ) * I))
        + I * (∫ y : ℝ in (-T)..T, F ((c : ℂ) + (y : ℂ) * I))
        - I * (∫ y : ℝ in (-T)..T, F (((0 : ℝ) : ℂ) + (y : ℂ) * I))
        = 2 * (Real.pi : ℂ) * I * ∑ p ∈ S, r p := by
    intro T hT
    let z0 : ℂ := ⟨0, -T⟩
    let w0 : ℂ := ⟨c, T⟩
    have hKsub : Set.uIcc z0.re w0.re ×ℂ Set.uIcc z0.im w0.im ⊆
        {s : ℂ | 0 ≤ s.re ∧ s.re ≤ c} := by
      intro s hs
      obtain ⟨h1, -⟩ := Complex.mem_reProdIm.mp hs
      rw [show z0.re = 0 from rfl, show w0.re = c from rfl, Set.uIcc_of_le hc.le] at h1
      exact h1
    have hdiffK : ∀ s ∈ Set.uIcc z0.re w0.re ×ℂ Set.uIcc z0.im w0.im, s ∉ S →
        DifferentiableWithinAt ℂ F (Set.uIcc z0.re w0.re ×ℂ Set.uIcc z0.im w0.im) s := by
      intro s hs hsS
      obtain ⟨h1, h2⟩ := hKsub hs
      exact (hdiff s h1 h2 hsS).mono hKsub
    obtain ⟨g, hg, hfg⟩ := Complex.exists_differentiableOn_eq_add_sum_div_sub _ S r F hloc hdiffK
    have hin : ∀ p ∈ S, z0.re < p.re ∧ p.re < w0.re ∧ z0.im < p.im ∧ p.im < w0.im := by
      intro p hp
      have h1 := Finset.single_le_sum (f := fun p => |p.im|) (fun _ _ => abs_nonneg _) hp
      have h2 := abs_lt.mp (show |p.im| < T by linarith)
      exact ⟨(hS p hp).1, (hS p hp).2, h2.1, h2.2⟩
    have hRS := RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum ⟨z0, w0⟩ S r F g
      hin hg hfg
    simp only [RectilinearRectangle.boundaryIntegral, z0, w0, smul_eq_mul] at hRS
    linear_combination hRS
  -- limits
  have hlimc : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, F ((c : ℂ) + (y : ℂ) * I)) atTop
      (𝓝 (∫ t : ℝ, F ((c : ℂ) + (t : ℂ) * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hic tendsto_neg_atTop_atBot tendsto_id
  have hlim0 : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, F (((0 : ℝ) : ℂ) + (y : ℂ) * I)) atTop
      (𝓝 (∫ t : ℝ, F ((t : ℂ) * I))) := by
    have e : (fun y : ℝ => F (((0 : ℝ) : ℂ) + (y : ℂ) * I)) = fun y : ℝ => F ((y : ℂ) * I) := by
      funext y; simp
    simp only [e]
    exact MeasureTheory.intervalIntegral_tendsto_integral hi0 tendsto_neg_atTop_atBot tendsto_id
  have hhor : ∀ σ : ℝ → ℝ, (∀ T, 1 ≤ T → |σ T| = T) →
      Tendsto (fun T : ℝ => ∫ x : ℝ in (0 : ℝ)..c, F ((x : ℂ) + ((σ T : ℝ) : ℂ) * I)) atTop
        (𝓝 0) := by
    intro σ hσ
    have hg : Tendsto (fun T : ℝ => |B| * c * T⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (|B| * c)
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hb : ∀ x ∈ Set.uIoc (0 : ℝ) c, ‖F ((x : ℂ) + ((σ T : ℝ) : ℂ) * I)‖ ≤ |B| * T⁻¹ := by
      intro x hx
      rw [Set.uIoc_of_le hc.le] at hx
      have him : ((x : ℂ) + ((σ T : ℝ) : ℂ) * I).im = σ T := by simp
      have hre : ((x : ℂ) + ((σ T : ℝ) : ℂ) * I).re = x := by simp
      have := hB _ (by rw [hre]; exact hx.1.le) (by rw [hre]; exact hx.2)
        (by rw [him, hσ T hT]; exact hT)
      rw [him, hσ T hT] at this
      refine this.trans ?_
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [sub_zero, abs_of_pos hc] at this
    linarith
  have hb1 := hhor (fun T => -T) (fun T hT => by rw [abs_neg, abs_of_pos (by linarith)])
  have hb2 := hhor (fun T => T) (fun T hT => abs_of_pos (by linarith))
  have hL := ((hb1.sub hb2).add (hlimc.const_mul I)).sub (hlim0.const_mul I)
  have heq := tendsto_nhds_unique hL (tendsto_const_nhds.congr'
    (by filter_upwards [eventually_ge_atTop T₀] with T hT using (hid T hT).symm))
  have hI : I ≠ 0 := Complex.I_ne_zero
  apply mul_left_cancel₀ hI
  linear_combination heq

private lemma continuous_comp_vertical_line {c : ℝ} (hc : 0 < c) (F : ℂ → ℂ) (S : Finset ℂ)
    (hS : ∀ p ∈ S, 0 < p.re ∧ p.re < c)
    (hdiff : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c → s ∉ S →
      DifferentiableWithinAt ℂ F {s : ℂ | 0 ≤ s.re ∧ s.re ≤ c} s)
    {x : ℝ} (hx : x = 0 ∨ x = c) :
    Continuous fun t : ℝ => F ((x : ℂ) + (t : ℂ) * I) := by
  have hT : ContinuousOn F {s : ℂ | (0 ≤ s.re ∧ s.re ≤ c) ∧ s ∉ S} := by
    intro s hs
    exact (hdiff s hs.1.1 hs.1.2 hs.2).continuousWithinAt.mono fun u hu => hu.1
  refine hT.comp_continuous (by fun_prop) fun t => ?_
  have hre : ((x : ℂ) + (t : ℂ) * I).re = x := by simp
  refine ⟨by rw [hre]; rcases hx with rfl | rfl <;> constructor <;> linarith, fun hm => ?_⟩
  have := hS _ hm
  rw [hre] at this
  rcases hx with rfl | rfl <;> linarith [this.1, this.2]

private lemma integrable_comp_of_norm_le {F : ℂ → ℂ} {p : ℝ → ℂ} (hp : ∀ t, (p t).im = t)
    (hcont : Continuous fun t => F (p t)) {B δ : ℝ} (hδ : 0 < δ)
    (hb : ∀ t, ‖F (p t)‖ ≤ B * (1 + ‖p t‖) ^ (-1 - δ)) : Integrable fun t => F (p t) := by
  refine integrable_of_norm_le_one_add_abs_rpow hcont (B := |B|) hδ fun t => ?_
  refine (hb t).trans ?_
  have h1 := one_add_norm_rpow_le_one_add_abs_im_rpow hδ.le (p t)
  rw [hp] at h1
  have h0 : 0 ≤ (1 + ‖p t‖) ^ (-1 - δ) := by positivity
  calc B * (1 + ‖p t‖) ^ (-1 - δ) ≤ |B| * (1 + ‖p t‖) ^ (-1 - δ) :=
        mul_le_mul_of_nonneg_right (le_abs_self B) h0
    _ ≤ |B| * (1 + |t|) ^ (-1 - δ) := mul_le_mul_of_nonneg_left h1 (abs_nonneg B)

private lemma integral_vertical_sub_eq_two_pi_mul_sum {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (F : ℂ → ℂ) (S : Finset ℂ)
    (r : ℂ → ℂ) (hS : ∀ p ∈ S, 0 < p.re ∧ p.re < c)
    (hloc : ∀ p ∈ S, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, F s = r p / (s - p) + φ s)
    (hdiff : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c → s ∉ S →
      DifferentiableWithinAt ℂ F {s : ℂ | 0 ≤ s.re ∧ s.re ≤ c} s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c → (s.re = 0 ∨ s.re = c ∨ 1 ≤ |s.im|) →
      ‖F s‖ ≤ B * (1 + ‖s‖) ^ (-1 - δ)) :
    (∫ t : ℝ, F ((c : ℂ) + (t : ℂ) * I)) - ∫ t : ℝ, F ((t : ℂ) * I) =
      2 * (Real.pi : ℂ) * ∑ p ∈ S, r p := by
  obtain ⟨B, hB⟩ := hbd
  have hc0 := continuous_comp_vertical_line hc F S hS hdiff (x := 0) (Or.inl rfl)
  have hcc := continuous_comp_vertical_line hc F S hS hdiff (x := c) (Or.inr rfl)
  have e0 : (fun t : ℝ => F (((0 : ℝ) : ℂ) + (t : ℂ) * I)) = fun t : ℝ => F ((t : ℂ) * I) := by
    funext t; simp
  rw [e0] at hc0
  have hi0 : Integrable fun t : ℝ => F ((t : ℂ) * I) :=
    integrable_comp_of_norm_le (p := fun t : ℝ => (t : ℂ) * I) (fun t => by simp) hc0 hδ
      fun t => hB _ (by simp) (by simp; linarith) (Or.inl (by simp))
  have hic : Integrable fun t : ℝ => F ((c : ℂ) + (t : ℂ) * I) :=
    integrable_comp_of_norm_le (p := fun t : ℝ => (c : ℂ) + (t : ℂ) * I) (fun t => by simp) hcc hδ
      fun t => hB _ (by simp; linarith) (by simp) (Or.inr (Or.inl (by simp)))
  refine integral_vertical_sub_eq_two_pi_mul_sum_of_div_abs_im hc F S r hS hloc hdiff
    ⟨|B|, fun s h1 h2 h3 => ?_⟩ hi0 hic
  refine (hB s h1 h2 (Or.inr (Or.inr h3))).trans ?_
  have hq := (one_add_norm_rpow_le_one_add_abs_im_rpow hδ.le s).trans
    (one_add_rpow_le_one_div hδ.le h3)
  have h0 : 0 ≤ (1 + ‖s‖) ^ (-1 - δ) := by positivity
  calc B * (1 + ‖s‖) ^ (-1 - δ) ≤ |B| * (1 + ‖s‖) ^ (-1 - δ) :=
        mul_le_mul_of_nonneg_right (le_abs_self B) h0
    _ ≤ |B| * (1 / |s.im|) := mul_le_mul_of_nonneg_left hq (abs_nonneg B)
    _ = |B| / |s.im| := by ring

/-- The Fourier transform of a function on `ℝ` as an integral against `e^{-2πity}`. -/
private lemma fourier_eq_integral (h0 : ℝ → ℂ) (y : ℝ) :
    𝓕 h0 y = ∫ t : ℝ, h0 t * Complex.exp (-2 * Real.pi * I * t * y) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1
  funext t
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

private lemma integral_exp_mul_eq_fourier {h : ℂ → ℂ} {h0 : ℝ → ℂ}
    (hh0 : ∀ t : ℝ, h (t * I) = h0 (t / (2 * Real.pi))) (y : ℝ) :
    ∫ t : ℝ, Complex.exp (-(t : ℂ) * I * y) * h ((t : ℂ) * I) =
      2 * (Real.pi : ℂ) * ∫ u : ℝ, (h0 u : ℂ) * Complex.exp (-2 * Real.pi * I * u * y) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have e : (fun t : ℝ => Complex.exp (-(t : ℂ) * I * y) * h ((t : ℂ) * I)) =
      fun t : ℝ => (fun u : ℝ => (h0 u : ℂ) * Complex.exp (-2 * Real.pi * I * u * y))
        (t / (2 * Real.pi)) := by
    funext t
    rw [hh0, mul_comm]
    congr 2
    push_cast
    field_simp
  rw [e, Measure.integral_comp_div
    (fun u : ℝ => (h0 u : ℂ) * Complex.exp (-2 * Real.pi * I * u * y)) (2 * Real.pi),
    Complex.real_smul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  push_cast; ring

private lemma exists_norm_digamma_le_log_one_add :
    ∃ K : ℝ, ∀ u : ℂ, 1 / 4 ≤ u.re → ‖Complex.digamma u‖ ≤ K + Real.log (1 + ‖u‖) := by
  obtain ⟨Cψ, hCψ⟩ := Complex.exists_norm_digamma_le_log_add
  refine ⟨|Cψ| + 4, fun u hu => ?_⟩
  have hne : ∀ m : ℕ, u ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hadd := Complex.digamma_apply_add_one u hne
  have hre1 : (u + 1).re = u.re + 1 := by simp
  have hn1 : 1 ≤ ‖u + 1‖ := le_trans (by rw [hre1]; linarith) (Complex.re_le_norm _)
  have hψ := hCψ (u + 1) (by rw [hre1]; linarith) hn1
  have := le_abs_self Cψ
  have hun : 1 / 4 ≤ ‖u‖ := le_trans hu (Complex.re_le_norm _)
  have hinv : ‖u⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    calc ‖u‖⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hun
      _ = 4 := by norm_num
  have hlog : Real.log ‖u + 1‖ ≤ Real.log (1 + ‖u‖) :=
    Real.log_le_log (by linarith) (by
      calc ‖u + 1‖ ≤ ‖u‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = 1 + ‖u‖ := by simp; ring)
  have : Complex.digamma u = Complex.digamma (u + 1) - u⁻¹ := by rw [hadd]; ring
  rw [this]
  calc ‖Complex.digamma (u + 1) - u⁻¹‖ ≤ ‖Complex.digamma (u + 1)‖ + ‖u⁻¹‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

private lemma log_one_add_le_rpow {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ 2 / ε * (1 + x) ^ (ε / 2) := by
  have h := Real.log_le_rpow_div (x := 1 + x) (by linarith) (by positivity : 0 < ε / 2)
  have e : (1 + x) ^ (ε / 2) / (ε / 2) = 2 / ε * (1 + x) ^ (ε / 2) := by field_simp
  linarith

private lemma exists_norm_gammaFactor_logDeriv_le {ε : ℝ} (hε : 0 < ε) :
    ∃ KA : ℝ, ∀ s : ℂ, 0 ≤ s.re → min ε (1 / 2) ≤ ‖s - 1 / 2‖ →
      ‖1 / (1 / 2 + s - 1) - (Real.log Real.pi : ℂ) / 2 +
        Complex.digamma ((1 / 2 + s) / 2 + 1) / 2‖ ≤ KA * (1 + ‖s‖) ^ (ε / 2) := by
  obtain ⟨Kψ, hKψ⟩ := exists_norm_digamma_le_log_one_add
  set δ0 : ℝ := min ε (1 / 2) with hδ0
  have hδ0p : 0 < δ0 := lt_min hε (by norm_num)
  refine ⟨1 / δ0 + |Real.log Real.pi| / 2 + (|Kψ| + Real.log 3) / 2 + 1 / ε,
    fun s hs hsd => ?_⟩
  set X : ℝ := (1 + ‖s‖) ^ (ε / 2) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow (by linarith [norm_nonneg s]) (by positivity)
  set u : ℂ := (1 / 2 + s) / 2 + 1 with hu
  have hure : 1 / 4 ≤ u.re := by
    have : u.re = (1 / 2 + s.re) / 2 + 1 := by simp [hu]
    rw [this]; linarith
  have hψ := hKψ u hure
  have hun : 1 + ‖u‖ ≤ 3 * (1 + ‖s‖) := by
    have : ‖u‖ ≤ ‖s‖ / 2 + 5 / 4 := by
      calc ‖u‖ = ‖s / 2 + 5 / 4‖ := by rw [hu]; ring_nf
        _ ≤ ‖s / 2‖ + ‖(5 / 4 : ℂ)‖ := norm_add_le _ _
        _ = ‖s‖ / 2 + 5 / 4 := by
          rw [norm_div]; norm_num [Complex.norm_ofNat]
    linarith [norm_nonneg s]
  have hlogu : Real.log (1 + ‖u‖) ≤ Real.log 3 + 2 / ε * X := by
    have h1 : Real.log (1 + ‖u‖) ≤ Real.log 3 + Real.log (1 + ‖s‖) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) hun
    have h2 := log_one_add_le_rpow hε (norm_nonneg s)
    linarith
  have hinv : ‖1 / (1 / 2 + s - 1)‖ ≤ 1 / δ0 := by
    rw [norm_div, norm_one, show (1 / 2 + s - 1 : ℂ) = s - 1 / 2 by ring]
    exact one_div_le_one_div_of_le hδ0p hsd
  have hlp : ‖(Real.log Real.pi : ℂ) / 2‖ = |Real.log Real.pi| / 2 := by
    rw [norm_div, Complex.norm_real]; simp
  have hdg : ‖Complex.digamma u / 2‖ = ‖Complex.digamma u‖ / 2 := by
    rw [norm_div]; simp
  have htri : ‖1 / (1 / 2 + s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma u / 2‖ ≤
      1 / δ0 + |Real.log Real.pi| / 2 + ‖Complex.digamma u‖ / 2 := by
    rw [← hlp, ← hdg]
    exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add hinv le_rfl)) le_rfl)
  have hK := le_abs_self Kψ
  have hA0 : 0 ≤ 1 / δ0 + |Real.log Real.pi| / 2 + (|Kψ| + Real.log 3) / 2 := by
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have h3 : (1 / δ0 + |Real.log Real.pi| / 2 + (|Kψ| + Real.log 3) / 2) * 1 ≤
      (1 / δ0 + |Real.log Real.pi| / 2 + (|Kψ| + Real.log 3) / 2) * X :=
    mul_le_mul_of_nonneg_left hX1 hA0
  have h4 : 2 / ε * X / 2 = 1 / ε * X := by ring
  refine htri.trans ?_
  nlinarith

private lemma norm_mul_le_one_add_rpow {ε : ℝ} {a b : ℂ} {K M x : ℝ} (hx : 0 ≤ x)
    (_hM0 : 0 ≤ M) (ha : ‖a‖ ≤ K * (1 + x) ^ (ε / 2)) (hb : ‖b‖ ≤ M * (1 + x) ^ (-1 - ε)) :
    ‖a * b‖ ≤ K * M * (1 + x) ^ (-1 - ε / 2) := by
  have hx1 : 0 < 1 + x := by linarith
  have hpow : (1 + x) ^ (ε / 2) * (1 + x) ^ (-1 - ε) = (1 + x) ^ (-1 - ε / 2) := by
    rw [← Real.rpow_add hx1]; ring_nf
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ (K * (1 + x) ^ (ε / 2)) * (M * (1 + x) ^ (-1 - ε)) :=
        mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)
    _ = K * M * (1 + x) ^ (-1 - ε / 2) := by rw [← hpow]; ring

private lemma gammaFactor_part {ε : ℝ} (hε : 0 < ε) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h {s | |s.re| ≤ 1 / 2 + ε}) (hsymm : ∀ s, h (-s) = h s)
    {h0 : ℝ → ℂ} (hh0 : ∀ t : ℝ, h (t * I) = h0 (t / (2 * Real.pi))) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s : ℂ, |s.re| ≤ 1 / 2 + ε → ‖h s‖ ≤ M * (1 + ‖s‖) ^ (-1 - ε)) :
    Integrable (fun t : ℝ => (fun s : ℂ => 1 / (1 / 2 + s - 1) - (Real.log Real.pi : ℂ) / 2 +
      digamma ((1 / 2 + s) / 2 + 1) / 2) (((1 / 2 + ε : ℝ) : ℂ) + t * I) *
        h (((1 / 2 + ε : ℝ) : ℂ) + t * I)) ∧
    ∫ t : ℝ, (fun s : ℂ => 1 / (1 / 2 + s - 1) - (Real.log Real.pi : ℂ) / 2 +
        digamma ((1 / 2 + s) / 2 + 1) / 2) (((1 / 2 + ε : ℝ) : ℂ) + t * I) *
          h (((1 / 2 + ε : ℝ) : ℂ) + t * I) =
      2 * (Real.pi : ℂ) * h (1 / 2) - (Real.log Real.pi : ℂ) / 2 * (2 * (Real.pi : ℂ) *
        ∫ t : ℝ, (h0 t : ℂ) * Complex.exp (-2 * Real.pi * I * t * 0)) +
        1 / 2 * (2 * (Real.pi : ℂ) * ∫ t : ℝ, digamma (1 / 4 + I * Real.pi * t) * h0 t) := by
  classical
  obtain ⟨KA, hKA⟩ := exists_norm_gammaFactor_logDeriv_le hε
  obtain ⟨Kψ, hKψ⟩ := exists_norm_digamma_le_log_one_add
  set c : ℝ := 1 / 2 + ε with hc
  have hc0 : 0 < c := by positivity
  have hε2 : 0 < ε / 2 := by positivity
  have hMs : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c → ‖h s‖ ≤ M * (1 + ‖s‖) ^ (-1 - ε) :=
    fun s h1 h2 => hM s (abs_le.mpr ⟨by linarith, h2⟩)
  have hhw : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c →
      DifferentiableWithinAt ℂ h {s : ℂ | 0 ≤ s.re ∧ s.re ≤ c} s := fun s h1 h2 =>
    (hh s (abs_le.mpr ⟨by linarith, h2⟩)).mono fun u hu =>
      abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
  have hHc : Continuous fun t : ℝ => h ((c : ℂ) + t * I) :=
    hh.continuousOn.comp_continuous (by fun_prop) fun t => by
      change |((c : ℂ) + t * I).re| ≤ 1 / 2 + ε
      rw [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero, hc,
        abs_of_pos (by linarith)]
  have hH0 : Continuous fun t : ℝ => h ((t : ℂ) * I) :=
    hh.continuousOn.comp_continuous (by fun_prop) fun t => by
      change |((t : ℂ) * I).re| ≤ 1 / 2 + ε
      rw [re_ofReal_mul, I_re, mul_zero, abs_zero]; linarith
  set A : ℂ → ℂ := fun s => 1 / (1 / 2 + s - 1) - (Real.log Real.pi : ℂ) / 2 +
    Complex.digamma ((1 / 2 + s) / 2 + 1) / 2 with hA
  -- (2) the Gamma-factor part, shifted to the line `0`
  have hAdiff : ∀ s : ℂ, 0 ≤ s.re → s ≠ 1 / 2 → DifferentiableAt ℂ A s := by
    intro s hs hs2
    have h1 : (1 / 2 + s - 1 : ℂ) ≠ 0 := fun h1 => hs2 (by linear_combination h1)
    have h2 : DifferentiableAt ℂ Complex.digamma ((1 / 2 + s) / 2 + 1) :=
      differentiableAt_digamma_of_re_pos (by simp; linarith)
    have h3 : DifferentiableAt ℂ (fun s : ℂ => Complex.digamma ((1 / 2 + s) / 2 + 1)) s :=
      h2.comp s (by fun_prop)
    have h4 : DifferentiableAt ℂ (fun s : ℂ => 1 / (1 / 2 + s - 1)) s := by
      fun_prop (disch := exact h1)
    exact (h4.sub (differentiableAt_const _)).add (h3.div_const 2)
  have hdist : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c → (s.re = 0 ∨ s.re = c ∨ 1 ≤ |s.im|) →
      min ε (1 / 2) ≤ ‖s - 1 / 2‖ := by
    intro s h1 h2 h3
    have hre : |(s - 1 / 2).re| ≤ ‖s - 1 / 2‖ := Complex.abs_re_le_norm _
    have him : |(s - 1 / 2).im| ≤ ‖s - 1 / 2‖ := Complex.abs_im_le_norm _
    have e1 : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    have e2 : (s - 1 / 2).im = s.im := by simp
    rw [e1] at hre; rw [e2] at him
    rcases h3 with h3 | h3 | h3
    · rw [h3] at hre; norm_num at hre
      exact (min_le_right _ _).trans hre
    · rw [h3, hc, show (1 / 2 + ε - 1 / 2 : ℝ) = ε by ring, abs_of_pos hε] at hre
      exact (min_le_left _ _).trans hre
    · exact (min_le_right _ _).trans (by linarith)
  have hAh : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c → (s.re = 0 ∨ s.re = c ∨ 1 ≤ |s.im|) →
      ‖A s * h s‖ ≤ KA * M * (1 + ‖s‖) ^ (-1 - ε / 2) := fun s h1 h2 h3 =>
    norm_mul_le_one_add_rpow (norm_nonneg s) hM0 (hKA s h1 (hdist s h1 h2 h3)) (hMs s h1 h2)
  have hstripA : (∫ t : ℝ, A ((c : ℂ) + t * I) * h ((c : ℂ) + t * I)) -
      ∫ t : ℝ, A ((t : ℂ) * I) * h ((t : ℂ) * I) = 2 * (Real.pi : ℂ) * h (1 / 2) := by
    have hloc : ∀ p ∈ ({1 / 2} : Finset ℂ), ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
        ∀ᶠ s in nhdsWithin p {p}ᶜ, A s * h s = h p / (s - p) + φ s := by
      intro p hp
      rw [Finset.mem_singleton] at hp; subst hp
      have hH : AnalyticAt ℂ h (1 / 2) := by
        have ho : IsOpen {s : ℂ | |s.re| < 1 / 2 + ε} :=
          isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
        refine hh.analyticAt (Filter.mem_of_superset (ho.mem_nhds ?_) fun s hs => by
          simp only [Set.mem_ofPred_eq] at hs ⊢; exact hs.le)
        change |(1 / 2 : ℂ).re| < 1 / 2 + ε
        norm_num; linarith
      have hΨ : DifferentiableAt ℂ (fun s : ℂ => (-(Real.log Real.pi : ℂ) / 2 +
          Complex.digamma ((1 / 2 + s) / 2 + 1) / 2) * h s) (1 / 2) := by
        have h2 : DifferentiableAt ℂ Complex.digamma ((1 / 2 + 1 / 2) / 2 + 1) :=
          differentiableAt_digamma_of_re_pos (by norm_num)
        have h3 : DifferentiableAt ℂ (fun s : ℂ => Complex.digamma ((1 / 2 + s) / 2 + 1))
            (1 / 2) := h2.comp (1 / 2 : ℂ) (by fun_prop)
        exact ((differentiableAt_const _).add (h3.div_const 2)).mul hH.differentiableAt
      obtain ⟨φ, hφ1, hφ2⟩ := Complex.exists_eventually_eq_div_sub_add_of_analyticAt (c := 1)
        (F := fun s => A s * h s) hH hΨ
        (Filter.Eventually.of_forall fun s => by
          simp only [hA]
          rw [show (1 / 2 + s - 1 : ℂ) = s - 1 / 2 by ring]
          ring)
      refine ⟨φ, hφ1, ?_⟩
      filter_upwards [hφ2] with s hs
      rw [hs]; ring
    have := integral_vertical_sub_eq_two_pi_mul_sum hc0 hε2 (fun s => A s * h s) {1 / 2} h
      (by intro p hp; rw [Finset.mem_singleton] at hp; subst hp; norm_num; linarith) hloc
      (fun s h1 h2 h3 => ((hAdiff s h1 (by simpa using h3)).differentiableWithinAt).mul
        (hhw s h1 h2))
      ⟨KA * M, hAh⟩
    simpa using this
  -- (3) the line `0`
  set O : ℝ → ℂ := fun t => 1 / ((t : ℂ) * I - 1 / 2) + 1 / ((t : ℂ) * I + 1 / 2) with hO
  set D : ℝ → ℂ := fun t => Complex.digamma (1 / 4 + (t : ℂ) * I / 2) with hD
  have hne1 : ∀ t : ℝ, (t : ℂ) * I + 1 / 2 ≠ 0 := fun t h1 => by
    have := congrArg Complex.re h1; simp at this
  have hne2 : ∀ t : ℝ, (t : ℂ) * I - 1 / 2 ≠ 0 := fun t h1 => by
    have := congrArg Complex.re h1; simp at this
  have hne3 : ∀ t : ℝ, (1 / 4 + (t : ℂ) * I / 2) ≠ 0 := fun t h1 => by
    have := congrArg Complex.re h1; simp at this
  have hA0 : ∀ t : ℝ, A ((t : ℂ) * I) = O t - (Real.log Real.pi : ℂ) / 2 + D t / 2 := by
    intro t
    have hne : ∀ m : ℕ, (1 / 4 + (t : ℂ) * I / 2) ≠ -(m : ℂ) := by
      intro m h1; have := congrArg Complex.re h1; simp at this
      linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have hadd := Complex.digamma_apply_add_one _ hne
    have e : (1 / 2 + (t : ℂ) * I) / 2 + 1 = (1 / 4 + (t : ℂ) * I / 2) + 1 := by ring
    simp only [hA, hO, hD]
    have hu : (1 / 4 + (t : ℂ) * I / 2)⁻¹ = 2 / ((t : ℂ) * I + 1 / 2) := by
      rw [show (1 / 4 + (t : ℂ) * I / 2) = ((t : ℂ) * I + 1 / 2) / 2 by ring, inv_div]
    rw [e, hadd, show (1 / 2 + (t : ℂ) * I - 1) = (t : ℂ) * I - 1 / 2 by ring, hu]
    ring
  have hint_h0 : MeasureTheory.Integrable fun t : ℝ => h ((t : ℂ) * I) :=
    integrable_comp_of_norm_le (p := fun t : ℝ => (t : ℂ) * I) (fun t => by simp) hH0 hε
      fun t => hMs _ (by simp) (by simp; linarith)
  have hOb : ∀ t : ℝ, ‖O t‖ ≤ 4 := by
    intro t
    have hb : ∀ a : ℂ, a.re = 1 / 2 ∨ a.re = -(1 / 2) → ‖1 / ((t : ℂ) * I + a)‖ ≤ 2 := by
      intro a ha
      rw [norm_div, norm_one]
      have hre : |((t : ℂ) * I + a).re| ≤ ‖(t : ℂ) * I + a‖ := Complex.abs_re_le_norm _
      have e : ((t : ℂ) * I + a).re = a.re := by simp
      rw [e] at hre
      have : (1 / 2 : ℝ) ≤ ‖(t : ℂ) * I + a‖ := by
        rcases ha with h | h <;> rw [h] at hre <;> norm_num at hre <;> linarith
      calc 1 / ‖(t : ℂ) * I + a‖ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) this
        _ = 2 := by norm_num
    have h1 := hb (1 / 2) (Or.inl (by norm_num))
    have h2 := hb (-(1 / 2)) (Or.inr (by norm_num))
    simp only [hO]
    rw [show (t : ℂ) * I - 1 / 2 = (t : ℂ) * I + -(1 / 2) by ring]
    calc _ ≤ ‖1 / ((t : ℂ) * I + -(1 / 2))‖ + ‖1 / ((t : ℂ) * I + 1 / 2)‖ := norm_add_le _ _
      _ ≤ 4 := by linarith
  have hOc : Continuous O := by
    simp only [hO]
    exact (continuous_const.div (by fun_prop) hne2).add (continuous_const.div (by fun_prop) hne1)
  have hint_O : MeasureTheory.Integrable fun t : ℝ => O t * h ((t : ℂ) * I) := by
    have hI : MeasureTheory.Integrable fun t : ℝ =>
        (fun s : ℂ => O s.im * h s) ((fun t : ℝ => (t : ℂ) * I) t) := by
      refine integrable_comp_of_norm_le (F := fun s => O s.im * h s) (p := fun t : ℝ => (t : ℂ) * I)
        (B := 4 * M) (fun t => by simp) ?_ hε2 ?_
      · exact (hOc.mul hH0).congr fun t => by simp
      · intro t
        refine norm_mul_le_one_add_rpow (norm_nonneg _) hM0 ?_
          (hMs ((t : ℂ) * I) (by simp) (by simp; linarith))
        have hX : 1 ≤ (1 + ‖(t : ℂ) * I‖) ^ (ε / 2) :=
          Real.one_le_rpow (by linarith [norm_nonneg ((t : ℂ) * I)]) hε2.le
        have := hOb t
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
          Complex.I_re, mul_one, mul_zero, add_zero]
        nlinarith
    exact hI.congr (Filter.Eventually.of_forall fun t => by simp)
  have hDc : Continuous D := by
    simp only [hD]
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (differentiableAt_digamma_of_re_pos (by simp)).continuousAt.comp
      (f := fun t : ℝ => 1 / 4 + (t : ℂ) * I / 2) (by fun_prop : Continuous _).continuousAt
  have hDb : ∀ t : ℝ, ‖D t‖ ≤ (|Kψ| + Real.log 2 + 2 / ε) * (1 + ‖(t : ℂ) * I‖) ^ (ε / 2) := by
    intro t
    set X := (1 + ‖(t : ℂ) * I‖) ^ (ε / 2) with hX
    have hX1 : 1 ≤ X := Real.one_le_rpow (by linarith [norm_nonneg ((t : ℂ) * I)]) hε2.le
    have h1 := hKψ (1 / 4 + (t : ℂ) * I / 2) (by simp)
    have hun : 1 + ‖1 / 4 + (t : ℂ) * I / 2‖ ≤ 2 * (1 + ‖(t : ℂ) * I‖) := by
      have : ‖1 / 4 + (t : ℂ) * I / 2‖ ≤ 1 / 4 + ‖(t : ℂ) * I‖ / 2 := by
        calc _ ≤ ‖(1 / 4 : ℂ)‖ + ‖(t : ℂ) * I / 2‖ := norm_add_le _ _
          _ = 1 / 4 + ‖(t : ℂ) * I‖ / 2 := by rw [norm_div]; norm_num
      linarith [norm_nonneg ((t : ℂ) * I)]
    have h2 : Real.log (1 + ‖1 / 4 + (t : ℂ) * I / 2‖) ≤
        Real.log 2 + Real.log (1 + ‖(t : ℂ) * I‖) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) hun
    have h3 := log_one_add_le_rpow hε (norm_nonneg ((t : ℂ) * I))
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h4 : (|Kψ| + Real.log 2) * 1 ≤ (|Kψ| + Real.log 2) * X :=
      mul_le_mul_of_nonneg_left hX1 (by positivity)
    have := le_abs_self Kψ
    simp only [hD]
    nlinarith
  have hint_D : MeasureTheory.Integrable fun t : ℝ => D t * h ((t : ℂ) * I) := by
    have hI : MeasureTheory.Integrable fun t : ℝ =>
        (fun s : ℂ => D s.im * h s) ((fun t : ℝ => (t : ℂ) * I) t) := by
      refine integrable_comp_of_norm_le (F := fun s => D s.im * h s) (p := fun t : ℝ => (t : ℂ) * I)
        (B := (|Kψ| + Real.log 2 + 2 / ε) * M) (fun t => by simp) ?_ hε2 ?_
      · exact (hDc.mul hH0).congr fun t => by simp
      · intro t
        refine norm_mul_le_one_add_rpow (norm_nonneg _) hM0 ?_
          (hMs ((t : ℂ) * I) (by simp) (by simp; linarith))
        simpa using hDb t
    exact hI.congr (Filter.Eventually.of_forall fun t => by simp)
  have hline0 : ∫ t : ℝ, A ((t : ℂ) * I) * h ((t : ℂ) * I) =
      (∫ t : ℝ, O t * h ((t : ℂ) * I)) - (Real.log Real.pi : ℂ) / 2 * (∫ t : ℝ, h ((t : ℂ) * I)) +
        1 / 2 * ∫ t : ℝ, D t * h ((t : ℂ) * I) := by
    have e : (fun t : ℝ => A ((t : ℂ) * I) * h ((t : ℂ) * I)) = fun t : ℝ =>
        (O t * h ((t : ℂ) * I) - (Real.log Real.pi : ℂ) / 2 * h ((t : ℂ) * I)) +
          1 / 2 * (D t * h ((t : ℂ) * I)) := by
      funext t; rw [hA0 t]; ring
    rw [e, MeasureTheory.integral_add
      (f := fun t : ℝ => O t * h ((t : ℂ) * I) - (Real.log Real.pi : ℂ) / 2 * h ((t : ℂ) * I))
      (g := fun t : ℝ => 1 / 2 * (D t * h ((t : ℂ) * I)))
      (hint_O.sub (hint_h0.const_mul _)) (hint_D.const_mul _),
      MeasureTheory.integral_sub (f := fun t : ℝ => O t * h ((t : ℂ) * I))
      (g := fun t : ℝ => (Real.log Real.pi : ℂ) / 2 * h ((t : ℂ) * I))
      hint_O (hint_h0.const_mul _), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  have hodd : ∫ t : ℝ, O t * h ((t : ℂ) * I) = 0 := by
    have h1 := MeasureTheory.integral_neg_eq_self (fun t : ℝ => O t * h ((t : ℂ) * I))
      MeasureTheory.volume
    have h2 : (fun t : ℝ => O (-t) * h (((-t : ℝ) : ℂ) * I)) =
        fun t => -(O t * h ((t : ℂ) * I)) := by
      funext t
      have e : (((-t : ℝ) : ℂ) * I) = -((t : ℂ) * I) := by push_cast; ring
      rw [e, hsymm]
      have e1 : 1 / (((-t : ℝ) : ℂ) * I - 1 / 2) = -(1 / ((t : ℂ) * I + 1 / 2)) := by
        rw [show ((-t : ℝ) : ℂ) * I - 1 / 2 = -((t : ℂ) * I + 1 / 2) by push_cast; ring,
          one_div_neg_eq_neg_one_div]
      have e2 : 1 / (((-t : ℝ) : ℂ) * I + 1 / 2) = -(1 / ((t : ℂ) * I - 1 / 2)) := by
        rw [show ((-t : ℝ) : ℂ) * I + 1 / 2 = -((t : ℂ) * I - 1 / 2) by push_cast; ring,
          one_div_neg_eq_neg_one_div]
      simp only [hO]
      rw [e1, e2]; ring
    simp only [h2, MeasureTheory.integral_neg] at h1
    linear_combination -h1 / 2
  have hF0 : ∫ t : ℝ, h ((t : ℂ) * I) =
      2 * (Real.pi : ℂ) * ∫ t : ℝ, (h0 t : ℂ) * Complex.exp (-2 * Real.pi * I * t * 0) := by
    have := integral_exp_mul_eq_fourier hh0 0
    simp only [Complex.ofReal_zero] at this
    have e : (fun t : ℝ => Complex.exp (-(t : ℂ) * I * 0) * h ((t : ℂ) * I)) =
        fun t : ℝ => h ((t : ℂ) * I) := by funext t; simp
    rw [e] at this; exact this
  have hDsub : ∫ t : ℝ, D t * h ((t : ℂ) * I) =
      2 * (Real.pi : ℂ) * ∫ t : ℝ, Complex.digamma (1 / 4 + I * Real.pi * t) * h0 t := by
    have e : (fun t : ℝ => D t * h ((t : ℂ) * I)) = fun t : ℝ =>
        (fun u : ℝ => digamma (1 / 4 + I * Real.pi * u) * (h0 u : ℂ)) (t / (2 * Real.pi)) := by
      funext t
      simp only [hD]
      rw [hh0]
      congr 2
      push_cast
      field_simp
    rw [e, MeasureTheory.Measure.integral_comp_div
      (fun u : ℝ => Complex.digamma (1 / 4 + I * Real.pi * u) * (h0 u : ℂ)) (2 * Real.pi),
      Complex.real_smul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    push_cast; ring
  have hAcint : MeasureTheory.Integrable fun t : ℝ =>
      A ((c : ℂ) + t * I) * h ((c : ℂ) + t * I) := by
    have hcont : Continuous fun t : ℝ => A ((c : ℂ) + t * I) := by
      refine continuous_iff_continuousAt.mpr fun t => ?_
      refine (hAdiff _ (by simp; linarith) ?_).continuousAt.comp
        (f := fun t : ℝ => (c : ℂ) + t * I) (by fun_prop : Continuous _).continuousAt
      intro h1; have := congrArg Complex.re h1; simp at this; linarith
    exact integrable_comp_of_norm_le (F := fun s => A s * h s) (p := fun t : ℝ => (c : ℂ) + t * I)
      (fun t => by simp) (hcont.mul hHc) hε2
      (fun t => hAh _ (by simp; linarith) (by simp) (Or.inr (Or.inl (by simp))))
  have hIA : ∫ t : ℝ, A ((c : ℂ) + t * I) * h ((c : ℂ) + t * I) =
      2 * (Real.pi : ℂ) * h (1 / 2) - (Real.log Real.pi : ℂ) / 2 * (2 * (Real.pi : ℂ) *
        ∫ t : ℝ, (h0 t : ℂ) * Complex.exp (-2 * Real.pi * I * t * 0)) +
        1 / 2 * (2 * (Real.pi : ℂ) * ∫ t : ℝ, digamma (1 / 4 + I * Real.pi * t) * h0 t) := by
    linear_combination hstripA + hline0 + hodd - (Real.log Real.pi : ℂ) / 2 * hF0 + 1 / 2 * hDsub
  exact ⟨hAcint, hIA⟩

private lemma primePower_part {ε : ℝ} (hε : 0 < ε) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h {s | |s.re| ≤ 1 / 2 + ε})
    {h0 : ℝ → ℂ} (hh0 : ∀ t : ℝ, h (t * I) = h0 (t / (2 * Real.pi))) {M : ℝ} (_hM0 : 0 ≤ M)
    (hM : ∀ s : ℂ, |s.re| ≤ 1 / 2 + ε → ‖h s‖ ≤ M * (1 + ‖s‖) ^ (-1 - ε)) :
    Integrable (fun t : ℝ => logDeriv riemannZeta (1 / 2 + (((1 / 2 + ε : ℝ) : ℂ) + t * I)) *
      h (((1 / 2 + ε : ℝ) : ℂ) + t * I)) ∧
    HasSum (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        ∫ t : ℝ, (h0 t : ℂ) * Complex.exp (-2 * Real.pi * I * t * Real.log n))
      (-(1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        logDeriv riemannZeta (1 / 2 + (((1 / 2 + ε : ℝ) : ℂ) + t * I)) *
          h (((1 / 2 + ε : ℝ) : ℂ) + t * I)) := by
  classical
  obtain ⟨Kζ, hKζ⟩ := exists_norm_logDeriv_riemannZeta_le_const hε
  set c : ℝ := 1 / 2 + ε with hc
  have hc0 : 0 < c := by positivity
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hMs : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c → ‖h s‖ ≤ M * (1 + ‖s‖) ^ (-1 - ε) :=
    fun s h1 h2 => hM s (abs_le.mpr ⟨by linarith, h2⟩)
  have hhw : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c →
      DifferentiableWithinAt ℂ h {s : ℂ | 0 ≤ s.re ∧ s.re ≤ c} s := fun s h1 h2 =>
    (hh s (abs_le.mpr ⟨by linarith, h2⟩)).mono fun u hu =>
      abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
  have hHc : Continuous fun t : ℝ => h ((c : ℂ) + t * I) :=
    hh.continuousOn.comp_continuous (by fun_prop) fun t => by
      change |((c : ℂ) + t * I).re| ≤ 1 / 2 + ε
      rw [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero, hc,
        abs_of_pos (by linarith)]
  have hH0 : Continuous fun t : ℝ => h ((t : ℂ) * I) :=
    hh.continuousOn.comp_continuous (by fun_prop) fun t => by
      change |((t : ℂ) * I).re| ≤ 1 / 2 + ε
      rw [re_ofReal_mul, I_re, mul_zero, abs_zero]; linarith
  set Zf : ℂ → ℂ := fun s => logDeriv riemannZeta (1 / 2 + s) with hZf
  have hlre : ∀ t : ℝ, (1 / 2 + ((c : ℂ) + t * I)).re = 1 + ε := fun t => by
    simp [hc]; ring
  -- (4) the prime-power part
  set cn : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
    with hcn
  have hterm : ∀ (n : ℕ) (s : ℂ),
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 + s) n =
        cn n * (n : ℂ) ^ (-s) := by
    intro n s
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hcn]
    · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have hsq : (n : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt n : ℝ) : ℂ) := by
        rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _)]; norm_num
      have hsq0 : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
      have hs0 : (n : ℂ) ^ s ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero hn0]; exact Complex.exp_ne_zero _
      rw [LSeries.term_def, ite_eq_right hn.ne', Complex.cpow_add _ _ hn0, Complex.cpow_neg, hsq]
      simp only [hcn]
      push_cast
      field_simp
  have hGb : ∀ n : ℕ, 1 ≤ n → ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c →
      ‖(n : ℂ) ^ (-s) * h s‖ ≤ M * (1 + ‖s‖) ^ (-1 - ε) := by
    intro n hn s h1 h2
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    have : (n : ℝ) ^ (-s).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by simp; linarith)
    calc _ ≤ 1 * (M * (1 + ‖s‖) ^ (-1 - ε)) :=
          mul_le_mul this (hMs s h1 h2) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hGshift : ∀ n : ℕ, 1 ≤ n →
      (∫ t : ℝ, (n : ℂ) ^ (-((c : ℂ) + t * I)) * h ((c : ℂ) + t * I)) =
        ∫ t : ℝ, (n : ℂ) ^ (-((t : ℂ) * I)) * h ((t : ℂ) * I) := by
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have := integral_vertical_sub_eq_two_pi_mul_sum hc0 hε (fun s => (n : ℂ) ^ (-s) * h s) ∅
      (fun _ => 0) (by simp)
      (by simp)
      (fun s h1 h2 _ => (((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => -s) s).const_cpow
        (Or.inl hn0)).differentiableWithinAt).mul (hhw s h1 h2))
      ⟨M, fun s h1 h2 _ => hGb n hn s h1 h2⟩
    simpa [sub_eq_zero] using this
  have hGint : ∀ n : ℕ, 1 ≤ n → MeasureTheory.Integrable fun t : ℝ =>
      (n : ℂ) ^ (-((c : ℂ) + t * I)) * h ((c : ℂ) + t * I) := by
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact integrable_comp_of_norm_le (F := fun s => (n : ℂ) ^ (-s) * h s)
      (p := fun t : ℝ => (c : ℂ) + t * I) (fun t => by simp)
      (((by fun_prop : Continuous fun t : ℝ => -((c : ℂ) + t * I)).const_cpow
        (Or.inl hn0)).mul hHc) hε
      (fun t => hGb n hn _ (by simp; linarith) (by simp))
  set Fn : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 + ((c : ℂ) + t * I)) n *
      h ((c : ℂ) + t * I) with hFn
  have hFn_eq : ∀ n t, Fn n t =
      cn n * ((n : ℂ) ^ (-((c : ℂ) + t * I)) * h ((c : ℂ) + t * I)) := by
    intro n t; simp only [hFn]; rw [hterm]; ring
  have hcn0 : cn 0 = 0 := by simp [hcn]
  have hFint : ∀ n, MeasureTheory.Integrable (Fn n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : Fn 0 = fun _ => 0 := by funext t; rw [hFn_eq, hcn0, zero_mul]
      rw [this]; exact MeasureTheory.integrable_zero _ _ _
    · have : Fn n = fun t : ℝ =>
          cn n * ((n : ℂ) ^ (-((c : ℂ) + t * I)) * h ((c : ℂ) + t * I)) := funext (hFn_eq n)
      rw [this]; exact (hGint n hn).const_mul _
  have hnt : ∀ n (t : ℝ),
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (1 / 2 + ((c : ℂ) + t * I)) n‖ =
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((1 + ε : ℝ) : ℂ) n‖ := by
    intro n t; rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hlre t, Complex.ofReal_re]
  have hFsum : Summable fun n => ∫ t, ‖Fn n t‖ := by
    have e : ∀ n, ∫ t, ‖Fn n t‖ =
        ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((1 + ε : ℝ) : ℂ) n‖ *
          ∫ t : ℝ, ‖h ((c : ℂ) + t * I)‖ := by
      intro n; simp only [hFn, norm_mul, hnt]; exact MeasureTheory.integral_const_mul _ _
    simp only [e]
    exact (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((1 + ε : ℝ) : ℂ))
      (by simp; linarith)).norm.mul_right _
  have hHS := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hFsum
  have hZsum : ∀ t : ℝ, ∑' n, Fn n t = -(Zf ((c : ℂ) + t * I) * h ((c : ℂ) + t * I)) := by
    intro t
    simp only [hFn]
    rw [tsum_mul_right]
    change LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (1 / 2 + ((c : ℂ) + t * I)) * _ = _
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (by rw [hlre t]; linarith)]
    simp only [hZf, logDeriv_apply]; ring
  have hFnI : ∀ n, ∫ t, Fn n t = 2 * (Real.pi : ℂ) * (cn n *
      ∫ t : ℝ, (h0 t : ℂ) * Complex.exp (-2 * Real.pi * I * t * Real.log n)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hFn_eq, hcn0, zero_mul, MeasureTheory.integral_zero, mul_zero]
    · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [hFn_eq]
      rw [MeasureTheory.integral_const_mul, hGshift n hn]
      have e : (fun t : ℝ => (n : ℂ) ^ (-((t : ℂ) * I)) * h ((t : ℂ) * I)) =
          fun t : ℝ => Complex.exp (-(t : ℂ) * I * (Real.log n : ℝ)) * h ((t : ℂ) * I) := by
        funext t
        rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
        congr 2; ring
      rw [e, integral_exp_mul_eq_fourier hh0]
      ring
  have hP : HasSum (fun n : ℕ => cn n *
      ∫ t : ℝ, (h0 t : ℂ) * Complex.exp (-2 * Real.pi * I * t * Real.log n))
      (-(1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, Zf ((c : ℂ) + t * I) * h ((c : ℂ) + t * I)) := by
    have h1 := hHS.mul_left (1 / (2 * (Real.pi : ℂ)))
    have e1 : (fun n => 1 / (2 * (Real.pi : ℂ)) * ∫ t, Fn n t) = fun n : ℕ => cn n *
        ∫ t : ℝ, (h0 t : ℂ) * Complex.exp (-2 * Real.pi * I * t * Real.log n) := by
      funext n
      rw [hFnI, ← mul_assoc, one_div_mul_cancel (mul_ne_zero two_ne_zero hpi), one_mul]
    rw [e1] at h1
    simp only [hZsum, MeasureTheory.integral_neg] at h1
    rw [show -(1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, Zf ((c : ℂ) + t * I) * h ((c : ℂ) + t * I) =
      1 / (2 * (Real.pi : ℂ)) * -∫ t : ℝ, Zf ((c : ℂ) + t * I) * h ((c : ℂ) + t * I) by ring]
    exact h1
  have hZint : MeasureTheory.Integrable fun t : ℝ =>
      Zf ((c : ℂ) + t * I) * h ((c : ℂ) + t * I) := by
    have hcont : Continuous fun t : ℝ => Zf ((c : ℂ) + t * I) := by
      refine continuous_iff_continuousAt.mpr fun t => ?_
      exact (continuousAt_logDeriv_riemannZeta (by rw [hlre t]; linarith)).comp
        (f := fun t : ℝ => 1 / 2 + ((c : ℂ) + t * I)) (by fun_prop : Continuous _).continuousAt
    refine integrable_comp_of_norm_le (F := fun s => Zf s * h s) (p := fun t : ℝ => (c : ℂ) + t * I)
      (B := |Kζ| * M) (fun t => by simp) (hcont.mul hHc) hε ?_
    intro t
    have h1 : ‖Zf ((c : ℂ) + t * I)‖ ≤ Kζ := hKζ (1 / 2 + ((c : ℂ) + t * I)) (by rw [hlre t])
    have h2 := hMs ((c : ℂ) + t * I) (by simp; linarith) (by simp)
    change ‖Zf ((c : ℂ) + t * I) * h ((c : ℂ) + t * I)‖ ≤ _
    rw [norm_mul]
    calc _ ≤ |Kζ| * (M * (1 + ‖(c : ℂ) + t * I‖) ^ (-1 - ε)) :=
          mul_le_mul (h1.trans (le_abs_self _)) h2 (norm_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  exact ⟨hZint, hP⟩

/-- **Weil's explicit formula.** Let `ε > 0` and let `h` be holomorphic on the strip
`|Re s| ≤ 1/2 + ε`, even, and `O(|s|^{-1-ε})` there, and write `h(it) = h₀(t / 2π)` on the
imaginary axis. Then, with `ĥ₀ = 𝓕 h₀` the Fourier transform,
`∑_{Im ρ > 0} h(ρ - 1/2) + ∑_n Λ(n)/√n ĥ₀(log n)
  = h(1/2) - (1/2) (log π) ĥ₀(0) + (1/2) ∫ ψ(1/4 + iπt) h₀(t) dt`,
where `ψ = Γ'/Γ`, the first sum runs over the nontrivial zeros `ρ` of `ζ` with multiplicity (any
family `z` listing the zeros of `ξ` with multiplicity), and both series converge. -/
theorem weil_explicit_formula {ε : ℝ} (hε : 0 < ε) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h {s | |s.re| ≤ 1 / 2 + ε}) (hsymm : ∀ s, h (-s) = h s)
    (hdecay : ∃ C : ℝ, ∀ s : ℂ, |s.re| ≤ 1 / 2 + ε → 1 ≤ ‖s‖ → ‖h s‖ ≤ C * ‖s‖ ^ (-1 - ε))
    {h0 : ℝ → ℂ} (hh0 : ∀ t : ℝ, h (t * I) = h0 (t / (2 * Real.pi)))
    {ι : Type*} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) :
    ∃ S P : ℂ, HasSum (fun n => if 0 < (z n).im then h (z n - 1 / 2) else 0) S ∧
      HasSum (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        𝓕 h0 (Real.log n)) P ∧
      S + P = h (1 / 2) - 1 / 2 * (Real.log Real.pi : ℂ) * 𝓕 h0 0 +
        1 / 2 * ∫ t : ℝ, digamma (1 / 4 + I * Real.pi * t) * h0 t := by
  simp only [fourier_eq_integral, ofReal_zero]
  classical
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_one_add_norm_rpow hε hh hdecay
  have hzero := hasSum_zeros_eq_integral_logDeriv_riemannXi hε hh hsymm hdecay z hz
  obtain ⟨hZint, hP⟩ := primePower_part hε hh hh0 hM0 hM
  obtain ⟨hAcint, hIA⟩ := gammaFactor_part hε hh hsymm hh0 hM0 hM
  set c : ℝ := 1 / 2 + ε with hc
  have hc0 : 0 < c := by positivity
  set A : ℂ → ℂ := fun s => 1 / (1 / 2 + s - 1) - (Real.log Real.pi : ℂ) / 2 +
    Complex.digamma ((1 / 2 + s) / 2 + 1) / 2 with hA
  set Zf : ℂ → ℂ := fun s => logDeriv riemannZeta (1 / 2 + s) with hZf
  have hlre : ∀ t : ℝ, (1 / 2 + ((c : ℂ) + t * I)).re = 1 + ε := fun t => by
    simp [hc]; ring
  -- (1) decomposition on the line `c`
  have hdec : ∀ t : ℝ, logDeriv riemannXi (1 / 2 + ((c : ℂ) + t * I)) * h ((c : ℂ) + t * I) =
      Zf ((c : ℂ) + t * I) * h ((c : ℂ) + t * I) +
        A ((c : ℂ) + t * I) * h ((c : ℂ) + t * I) := by
    intro t
    have hs1 : 1 / 2 + ((c : ℂ) + t * I) ≠ 1 := fun h1 => by
      have := hlre t; rw [h1] at this; simp at this; linarith
    have hζ : riemannZeta (1 / 2 + ((c : ℂ) + t * I)) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by rw [hlre t]; linarith)
    rw [logDeriv_riemannXi_eq hs1 hζ]
    simp only [hA, hZf]; ring
  -- assembly
  have hLsplit : ∫ t : ℝ, logDeriv riemannXi (1 / 2 + ((c : ℂ) + t * I)) * h ((c : ℂ) + t * I) =
      (∫ t : ℝ, Zf ((c : ℂ) + t * I) * h ((c : ℂ) + t * I)) +
        ∫ t : ℝ, A ((c : ℂ) + t * I) * h ((c : ℂ) + t * I) := by
    rw [← MeasureTheory.integral_add hZint hAcint]
    congr 1; funext t; exact hdec t
  refine ⟨_, _, hzero, hP, ?_⟩
  rw [hLsplit, hIA]
  generalize (∫ t : ℝ, Zf ((c : ℂ) + t * I) * h ((c : ℂ) + t * I)) = IZ
  generalize (∫ t : ℝ, (h0 t : ℂ) * Complex.exp (-2 * Real.pi * I * t * 0)) = H0
  generalize (∫ t : ℝ, Complex.digamma (1 / 4 + I * Real.pi * t) * h0 t) = Dg
  field_simp
  ring


end Weil

end RiemannXi
