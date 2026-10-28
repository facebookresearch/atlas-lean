/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.LSeries.Deriv
public import MathlibExt.Analysis.Complex.EntireOrder
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import MathlibExt.Analysis.Complex.HadamardFactorization
import MathlibExt.Analysis.SpecialFunctions.Gamma.DigammaAsymptotics
import MathlibExt.NumberTheory.LSeries.CoefficientRecovery

/-!
# Rigidity of Euler-type functions with a Gamma-factor functional equation

Let `f` be meromorphic, holomorphic and nonvanishing on `Re s ≥ 1/2`, with `log f` a Dirichlet
series `∑ c n n^{-s}` for large `Re s`. Suppose that
`H(s) = A^s ∏ Γ(α_i s + β_i) / ∏ Γ(γ_j s + δ_j) · f(s)` satisfies `H(s) = w · conj (H(1 - conj s))`
and agrees (off a discrete set) with an entire function of finite order. Then `f` is constant on
`Re s ≥ 1/2`.

The entire function is nonvanishing, hence `exp` of a polynomial `g`. Taking logarithmic
derivatives on a vertical line far to the right and using `ψ(z) = log z + O(1/|z|)` shows that
`g'` is constant, the Gamma-factor degrees balance, and the derivative of `∑ c n n^{-s}` tends
to a constant along the line. Coefficient recovery by vertical mean values then forces
`c n = 0` for `n ≥ 2`.

## Main statements

* `Complex.exists_polynomial_eq_exp_of_hasGrowthOrderLE`: a nonvanishing entire function of
  finite order is `exp` of a polynomial.
* `LSeries.exists_eq_const_of_gamma_functional_equation`: the rigidity theorem.
-/

open Filter Topology

@[expose] public section

/-- Two functions continuous at `x` that agree off a discrete set agree at `x`. -/
private lemma apply_eq_of_eventually_codiscrete {F G : ℂ → ℂ} {x : ℂ} (hF : ContinuousAt F x)
    (hG : ContinuousAt G x) (h : ∀ᶠ s in Filter.codiscrete ℂ, F s = G s) : F x = G x := by
  have h1 : ∀ᶠ s in 𝓝[≠] x, F s = G s := by
    have := (mem_codiscrete.mp h) x
    exact (by simpa using disjoint_principal_right.mp this : {s | F s = G s} ∈ 𝓝[≠] x)
  exact tendsto_nhds_unique_of_eventuallyEq (hF.tendsto.mono_left nhdsWithin_le_nhds)
    (hG.tendsto.mono_left nhdsWithin_le_nhds) h1

/-- **Nonvanishing entire functions of finite order.** An entire function without zeros and of
finite order is `exp` of a polynomial. -/
theorem Complex.exists_polynomial_eq_exp_of_hasGrowthOrderLE {E : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ E) (hρ : Complex.HasGrowthOrderLE E ρ) (hf0 : ∀ z, E z ≠ 0) :
    ∃ g : Polynomial ℂ, ∀ z, E z = Complex.exp (g.eval z) := by
  obtain ⟨h, hdiff, -, hfexp⟩ := Complex.exists_differentiable_eq_cexp_of_ne_zero hf hf0
  have hRe : ∀ s > ρ, ∃ A > (0 : ℝ), ∀ z, (h z).re ≤ A + ‖z‖ ^ s := by
    intro s hs
    obtain ⟨c, hc⟩ := (hρ (s - ρ) (by linarith)).bound
    obtain ⟨R0, -, hR0⟩ :=
      (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.mp hc
    obtain ⟨C0, hC0⟩ := (isCompact_closedBall (0 : ℂ) R0).exists_bound_of_continuousOn
      hdiff.continuous.continuousOn
    refine ⟨|Real.log (max c 1)| + |C0| + 1, by positivity, fun z => ?_⟩
    have hpow : 0 ≤ ‖z‖ ^ s := Real.rpow_nonneg (norm_nonneg z) s
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) R0
    · have := hC0 z hz
      have := Complex.re_le_norm (h z)
      have := le_abs_self C0
      have := abs_nonneg (Real.log (max c 1))
      linarith
    · have h1 := hR0 hz
      rw [show ρ + (s - ρ) = s by ring, hfexp z, Complex.norm_exp, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)] at h1
      have h2 : Real.exp (h z).re ≤ Real.exp (Real.log (max c 1) + ‖z‖ ^ s) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
        exact h1.trans (by gcongr; exact le_max_left _ _)
      have := Real.exp_le_exp.mp h2
      have := le_abs_self (Real.log (max c 1))
      have := abs_nonneg C0
      linarith
  have hzero : ∀ n : ℕ, max ρ 0 < n → iteratedDeriv n h 0 = 0 := by
    intro n hn
    obtain ⟨A, -, hA'⟩ := hRe ((max ρ 0 + n) / 2) (by have := le_max_left ρ 0; linarith)
    exact Complex.iteratedDeriv_eq_zero_of_re_le_rpow hdiff (s := (max ρ 0 + n) / 2)
      (by have := le_max_right ρ 0; linarith)
      zero_le_one (fun z => by simpa using hA' z) (by linarith)
  set N := ⌊max ρ 0⌋₊ with hN
  set g : Polynomial ℂ := ∑ n ∈ Finset.range (N + 1),
    Polynomial.monomial n ((n.factorial : ℂ)⁻¹ * iteratedDeriv n h 0) with hg
  refine ⟨g, fun z => ?_⟩
  rw [hfexp, Complex.eq_sum_range_of_iteratedDeriv_eq_zero hdiff (N := N) (fun n hn => hzero n ?_)
      z, hg,
    Polynomial.eval_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Polynomial.eval_monomial]
  · have := Nat.lt_floor_add_one (max ρ 0)
    have : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith

/-- `log (u + b) - log u → 0` when `u, u + b` stay in the right half-plane and `‖u‖ → ∞`. -/
private lemma tendsto_log_add_sub_log {α : Type*} {l : Filter α} {u : α → ℂ} (b : ℂ)
    (hu : Filter.Tendsto (fun x => ‖u x‖) l Filter.atTop)
    (hre : ∀ᶠ x in l, 0 < (u x).re ∧ 0 < (u x + b).re) :
    Filter.Tendsto (fun x => Complex.log (u x + b) - Complex.log (u x)) l (nhds 0) := by
  have hinv : Filter.Tendsto (fun x => (u x)⁻¹) l (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv]
    exact tendsto_inv_atTop_zero.comp hu
  have h1 : Filter.Tendsto (fun x => 1 + b * (u x)⁻¹) l (nhds 1) := by
    simpa using (hinv.const_mul b).const_add 1
  have h2 : Filter.Tendsto (fun x => Complex.log (1 + b * (u x)⁻¹)) l (nhds 0) := by
    have := (continuousAt_clog (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp h1
    rw [Complex.log_one] at this
    exact this
  refine h2.congr' ?_
  filter_upwards [hre] with x ⟨h0, hb⟩
  have hu0 : u x ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hub0 : u x + b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  have a1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h0)
  have a2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have hexp : Complex.exp (Complex.log (u x + b) - Complex.log (u x)) = 1 + b * (u x)⁻¹ := by
    rw [Complex.exp_sub, Complex.exp_log hub0, Complex.exp_log hu0]
    field_simp
  rw [← hexp, Complex.log_exp]
  · rw [Complex.sub_im, Complex.log_im, Complex.log_im]
    have := abs_lt.mp a1; have := abs_lt.mp a2
    linarith
  · rw [Complex.sub_im, Complex.log_im, Complex.log_im]
    have := abs_lt.mp a1; have := abs_lt.mp a2
    linarith

/-- `ψ(a u + b) - log a - log u → 0` along `‖u‖ → ∞` in the right half-plane. -/
private lemma tendsto_digamma_mul_add_sub_log {α : Type*} {l : Filter α} {u : α → ℂ} {a : ℝ}
    (ha : 0 < a)
    (b : ℂ) (hb : 0 ≤ b.re)
    (hu : Filter.Tendsto (fun x => ‖u x‖) l Filter.atTop) (hre : ∀ᶠ x in l, 0 < (u x).re) :
    Filter.Tendsto (fun x => Complex.digamma (a * u x + b) - (Real.log a : ℂ)
      - Complex.log (u x)) l (nhds 0) := by
  have hau : Filter.Tendsto (fun x => ‖(a : ℂ) * u x‖) l Filter.atTop := by
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
    exact hu.const_mul_atTop ha
  have hreab : ∀ᶠ x in l, 0 < ((a : ℂ) * u x).re ∧ 0 < ((a : ℂ) * u x + b).re := by
    filter_upwards [hre] with x hx
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    constructor <;> nlinarith
  have hL := tendsto_log_add_sub_log b hau hreab
  have hnab : Filter.Tendsto (fun x => ‖(a : ℂ) * u x + b‖) l Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun x => ?_) (Filter.tendsto_atTop_add_const_right _ (-‖b‖)
        hau)
    have := norm_sub_le ((a : ℂ) * u x + b) b
    simp only [add_sub_cancel_right] at this
    linarith
  obtain ⟨C, hC⟩ := Complex.exists_norm_digamma_sub_log_le (Real.pi / 2) (by positivity)
  have hD : Filter.Tendsto (fun x => Complex.digamma (a * u x + b) - Complex.log (a * u x + b))
      l (nhds 0) := by
    have hlim : Filter.Tendsto (fun x => C / ‖(a : ℂ) * u x + b‖) l (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hnab
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hreab] with x ⟨_, hx⟩
    have h0 : (a : ℂ) * u x + b ≠ 0 := fun h => by rw [h] at hx; simp at hx
    have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
    exact hC _ h0 (by linarith) (by linarith)
  have hsum := hD.add hL
  simp only [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hre] with x hx
  have hx0 : u x ≠ 0 := fun h => by rw [h] at hx; simp at hx
  rw [Complex.log_ofReal_mul ha hx0]
  ring

private lemma norm_log_le_log_norm_add_pi {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi := by
  calc ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ Real.log ‖z‖ + Real.pi := by
        rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg hz)]
        gcongr
        exact Complex.abs_arg_le_pi z

open Filter in
/-- A polynomial with `‖p(u)‖ ≤ B + B log ‖u‖` along `‖u‖ → ∞` is constant. -/
private lemma degree_le_zero_of_norm_eval_le_log {α : Type*} {l : Filter α} [l.NeBot] {u : α → ℂ}
    (p : Polynomial ℂ) (hu : Tendsto (fun x => ‖u x‖) l atTop) (B : ℝ)
    (hB : ∀ᶠ x in l, ‖p.eval (u x)‖ ≤ B + B * Real.log ‖u x‖) : p.degree ≤ 0 := by
  by_contra hdeg
  push Not at hdeg
  set q := p.divX with hq_def
  have hq0 : q ≠ 0 := by
    intro h
    rw [hq_def, Polynomial.divX_eq_zero_iff] at h
    rw [h] at hdeg
    exact absurd hdeg (not_lt.mpr Polynomial.degree_C_le)
  obtain ⟨c, hc, hcq⟩ : ∃ c > 0, ∀ᶠ x in l, c ≤ ‖q.eval (u x)‖ := by
    by_cases hq : 0 < q.degree
    · exact ⟨1, one_pos, (q.tendsto_norm_atTop hq hu).eventually_ge_atTop 1⟩
    · have hqC := Polynomial.eq_C_of_degree_le_zero (not_lt.mp hq)
      have hc0 : q.coeff 0 ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hqC
        exact hq0 hqC
      refine ⟨‖q.coeff 0‖, norm_pos_iff.mpr hc0, Eventually.of_forall fun x => ?_⟩
      rw [hqC]; simp
  have hp : ∀ z, p.eval z = q.eval z * z + p.coeff 0 := by
    intro z
    conv_lhs => rw [← Polynomial.divX_mul_X_add p]
    simp [hq_def]
  set ε := c / (2 * (|B| + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hlog : ∀ᶠ x in l, ‖Real.log ‖u x‖‖ ≤ ε * ‖‖u x‖‖ :=
    hu.eventually (Real.isLittleO_log_id_atTop.bound hεpos)
  have hbig := hu.eventually_ge_atTop (2 * (|B| + ‖p.coeff 0‖) / c + 1)
  have h1 := hu.eventually_ge_atTop 1
  obtain ⟨x, hx1, hx2, hx3, hx4, hx5⟩ := (hB.and (hcq.and (hlog.and (hbig.and h1)))).exists
  set r := ‖u x‖ with hr
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hx5
  rw [Real.norm_of_nonneg hlogr, Real.norm_of_nonneg (by positivity)] at hx3
  have hlow : c * r - ‖p.coeff 0‖ ≤ ‖p.eval (u x)‖ := by
    rw [hp]
    have := norm_sub_norm_le (q.eval (u x) * u x + p.coeff 0) (-p.coeff 0)
    simp only [sub_neg_eq_add, norm_neg] at this
    have : c * r ≤ ‖q.eval (u x)‖ * r := by gcongr
    have := norm_add_le (q.eval (u x) * u x + p.coeff 0) (-p.coeff 0)
    simp only [add_neg_cancel_right, norm_neg, norm_mul] at this
    linarith
  have hBlog : B * Real.log r ≤ |B| * (ε * r) := by
    calc B * Real.log r ≤ |B| * Real.log r := by gcongr; exact le_abs_self B
      _ ≤ |B| * (ε * r) := by gcongr
  have hεB : |B| * ε ≤ c / 2 := by
    rw [hε, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg B]
  have hcr : c * (2 * (|B| + ‖p.coeff 0‖) / c + 1) ≤ c * r := by gcongr
  rw [mul_add, mul_div_cancel₀ _ hc.ne', mul_one] at hcr
  nlinarith [le_abs_self B, norm_nonneg (p.coeff 0)]

/-- Cesàro means of a continuous function tending to `0` at `±∞` tend to `0`. -/
private lemma tendsto_mean_of_tendsto_zero {h : ℝ → ℂ} (hc : Continuous h) (h1 : Tendsto h atTop
    (𝓝 0))
    (h2 : Tendsto h atBot (𝓝 0)) :
    Tendsto (fun T : ℝ => (1 / (2 * T)) * ∫ t in -T..T, h t) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have e1 : ∀ᶠ t in atTop, ‖h t‖ < ε / 2 := by
    simpa using h1.eventually (Metric.ball_mem_nhds 0 (half_pos hε))
  have e2 : ∀ᶠ t in atBot, ‖h t‖ < ε / 2 := by
    simpa using h2.eventually (Metric.ball_mem_nhds 0 (half_pos hε))
  obtain ⟨R1, hR1⟩ := eventually_atTop.mp e1
  obtain ⟨R2, hR2⟩ := eventually_atBot.mp e2
  set R := max (max R1 (-R2)) 1 with hR
  have hR1' : R1 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hR2' : -R2 ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  have hR0 : 1 ≤ R := le_max_right _ _
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max R (2 * R * |C| / ε + 1), fun T hT => ?_⟩
  have hTR : R ≤ T := le_trans (le_max_left _ _) hT
  have hTC : 2 * R * |C| / ε + 1 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  rw [dist_zero_right]
  have hI : ∀ a b : ℝ, IntervalIntegrable h MeasureTheory.volume a b :=
    fun a b => hc.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI (-T) (-R)) (hI (-R) T),
    ← intervalIntegral.integral_add_adjacent_intervals (hI (-R) R) (hI R T)]
  have b1 : ‖∫ t in -T..-R, h t‖ ≤ ε / 2 * |-R - -T| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le (by linarith)] at hx
    exact (hR2 x (by linarith [hx.2])).le
  have b2 : ‖∫ t in -R..R, h t‖ ≤ |C| * |R - -R| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le (by linarith)] at hx
    exact (hC x ⟨hx.1.le, hx.2⟩).trans (le_abs_self C)
  have b3 : ‖∫ t in R..T, h t‖ ≤ ε / 2 * |T - R| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le hTR] at hx
    exact (hR1 x (by linarith [hx.1])).le
  rw [abs_of_nonneg (by linarith)] at b1
  rw [abs_of_nonneg (by linarith)] at b3
  rw [show |R - -R| = 2 * R by rw [abs_of_nonneg (by linarith)]; ring] at b2
  have hsum : ‖(∫ t in -T..-R, h t) + ((∫ t in -R..R, h t) + ∫ t in R..T, h t)‖ ≤
      ε * T - ε * R + 2 * R * |C| := by
    have := norm_add_le (∫ t in -T..-R, h t) ((∫ t in -R..R, h t) + ∫ t in R..T, h t)
    have := norm_add_le (∫ t in -R..R, h t) (∫ t in R..T, h t)
    nlinarith
  rw [norm_mul]
  have hn : ‖(1 / (2 * (T : ℂ)))‖ = 1 / (2 * T) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hT0.le]
    norm_num
  rw [hn]
  have hRC : 2 * R * |C| < ε * T := by
    have := (div_lt_iff₀ hε).mp (show 2 * R * |C| / ε < T by linarith)
    linarith
  rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)]
  nlinarith [abs_nonneg C]

/-- If `F'(σ + it) → K` as `t → ±∞`, with `σ` beyond the abscissa of `F = ∑ cₙ n^{-s}`, then
`cₙ = 0` for `n ≥ 2`. -/
private lemma coeff_eq_zero_of_tendsto_deriv (c : ℕ → ℂ) (σ₀ σ : ℝ)
    (hab : LSeries.abscissaOfAbsConv c ≤ σ₀)
    (hσ₀σ : σ₀ < σ) (K : ℂ)
    (hLconv : ∀ l : Filter ℝ, Tendsto (fun t : ℝ => ‖(σ : ℂ) + (t : ℂ) * Complex.I‖) l atTop →
      Tendsto (fun t : ℝ => deriv (LSeries c) ((σ : ℂ) + (t : ℂ) * Complex.I)) l (𝓝 K))
    (n : ℕ) (hn : 2 ≤ n) : c n = 0 := by
  have hure : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by intro t; simp
  have hunorm : ∀ t : ℝ, |t| ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
    intro t
    have := Complex.abs_im_le_norm ((σ : ℂ) + (t : ℂ) * Complex.I)
    simpa using this
  have hutop : Tendsto (fun t : ℝ => ‖(σ : ℂ) + (t : ℂ) * Complex.I‖) atTop atTop :=
    tendsto_atTop_mono (fun t => (le_abs_self t).trans (hunorm t)) tendsto_id
  have hubot : Tendsto (fun t : ℝ => ‖(σ : ℂ) + (t : ℂ) * Complex.I‖) atBot atTop :=
    tendsto_atTop_mono (fun t => (neg_le_abs t).trans (hunorm t)) tendsto_neg_atBot_atTop
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℂ, b = fun m => LSeries.logMul c m + if m = 1 then K else 0 :=
    ⟨_, rfl⟩
  have hbsum : ∀ s : ℂ, σ₀ < s.re →
      LSeriesSummable b s ∧ LSeries b s = LSeries (LSeries.logMul c) s + K := by
    intro s hs
    have h1 : LSeriesSummable (LSeries.logMul c) s :=
      LSeriesSummable_logMul_of_lt_re (hab.trans_lt (EReal.coe_lt_coe_iff.mpr hs))
    have hfun : LSeries.term b s =
        fun m => LSeries.term (LSeries.logMul c) s m + if m = 1 then K else 0 := by
      funext m
      rcases eq_or_ne m 0 with rfl | hm0
      · simp
      · rw [LSeries.term_of_ne_zero hm0, LSeries.term_of_ne_zero hm0, hb]
        split_ifs with hm1
        · subst hm1; simp
        · simp [hm1]
    have h2 : Summable (fun m : ℕ => if m = 1 then K else 0) :=
      summable_of_ne_finset_zero (s := {1}) (fun m hm => by
        simp only [Finset.mem_singleton] at hm; simp [hm])
    refine ⟨?_, ?_⟩
    · unfold LSeriesSummable
      rw [hfun]; exact Summable.add (f := LSeries.term (LSeries.logMul c) s) h1 h2
    · rw [LSeries, LSeries, hfun, Summable.tsum_add (f := LSeries.term (LSeries.logMul c) s) h1
        h2, tsum_ite_eq]
  have habs_b : LSeries.abscissaOfAbsConv b < σ := by
    have : LSeries.abscissaOfAbsConv b ≤ σ₀ :=
      LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
        (hbsum y (by simpa using hy)).1
    exact this.trans_lt (EReal.coe_lt_coe_iff.mpr hσ₀σ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h833 := LSeries.tendsto_mean_vertical_mul_cpow b habs_b hnpos
  rw [ite_eq_left ⟨n, by omega, rfl⟩, Nat.floor_natCast] at h833
  have hbl : ∀ l : Filter ℝ, Tendsto (fun t : ℝ => ‖(σ : ℂ) + (t : ℂ) * Complex.I‖) l atTop →
      Tendsto (fun t : ℝ => LSeries b ((σ : ℂ) + (t : ℂ) * Complex.I) *
        ((n : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) l (𝓝 0) := by
    intro l hl
    have h1 : Tendsto (fun t : ℝ => LSeries b ((σ : ℂ) + (t : ℂ) * Complex.I)) l (𝓝 0) := by
      have := ((hLconv l hl).neg).add_const K
      rw [neg_add_cancel] at this
      refine this.congr fun t => ?_
      have hlt : LSeries.abscissaOfAbsConv c < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
        rw [hure]; exact hab.trans_lt (EReal.coe_lt_coe_iff.mpr hσ₀σ)
      rw [(hbsum _ (by rw [hure]; exact hσ₀σ)).2, LSeries_deriv hlt]
      ring
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 := h1.norm.mul_const ((n : ℝ) ^ σ)
    rw [norm_zero, zero_mul] at h2
    refine h2.congr fun t => ?_
    rw [norm_mul, Complex.ofReal_natCast, Complex.norm_natCast_cpow_of_pos (by omega), hure]
  have hcont : Continuous (fun t : ℝ => LSeries b ((σ : ℂ) + (t : ℂ) * Complex.I) *
      ((n : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    have hu : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    refine Continuous.mul ?_ (hu.const_cpow (Or.inl (by exact_mod_cast hnpos.ne')))
    refine (LSeries_differentiableOn b).continuousOn.comp_continuous hu fun t => ?_
    change LSeries.abscissaOfAbsConv b < ((σ : ℂ) + (t : ℂ) * Complex.I).re
    rw [hure]; exact habs_b
  have hzero := tendsto_mean_of_tendsto_zero hcont (hbl atTop hutop) (hbl atBot hubot)
  have hbn := tendsto_nhds_unique h833 hzero
  have hn1 : n ≠ 1 := by omega
  rw [hb] at hbn
  simp only [ite_eq_right hn1, add_zero, LSeries.logMul] at hbn
  have hlog : Complex.log (n : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_ne_zero]
    exact (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  exact (mul_eq_zero.mp hbn).resolve_left hlog

/-- Along a path `‖u‖ → ∞` with `‖log u‖`-controlled error: a bounded `D` with
`D - p(u) - κ log u - K₀ → 0` forces `p` constant and `κ = 0`. -/
private lemma degree_le_zero_and_eq_zero_of_tendsto (D : ℝ → ℂ) (M : ℝ) (hM : ∀ t, ‖D t‖ ≤ M)
    (p : Polynomial ℂ)
    (κ K₀ : ℂ) (u : ℝ → ℂ) (hutop : Tendsto (fun t => ‖u t‖) atTop atTop)
    (hF : Tendsto (fun t => D t - p.eval (u t) - κ * Complex.log (u t) - K₀) atTop (𝓝 0)) :
    p.degree ≤ 0 ∧ κ = 0 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hev1 : ∀ᶠ t in atTop,
      ‖D t - p.eval (u t) - κ * Complex.log (u t) - K₀‖ ≤ 1 := by
    have := hF.norm
    rw [norm_zero] at this
    exact this.eventually (Iic_mem_nhds zero_lt_one)
  have htri : ∀ t, ‖p.eval (u t)‖ ≤ M + ‖κ * Complex.log (u t)‖ + ‖K₀‖ +
      ‖D t - p.eval (u t) - κ * Complex.log (u t) - K₀‖ := by
    intro t
    have e : p.eval (u t) = D t - κ * Complex.log (u t) - K₀ -
        (D t - p.eval (u t) - κ * Complex.log (u t) - K₀) := by ring
    refine (congrArg norm e).trans_le ?_
    have n1 := norm_sub_le (D t - κ * Complex.log (u t) - K₀)
      (D t - p.eval (u t) - κ * Complex.log (u t) - K₀)
    have n2 := norm_sub_le (D t - κ * Complex.log (u t)) K₀
    have n3 := norm_sub_le (D t) (κ * Complex.log (u t))
    have := hM t
    linarith
  have hpdeg : p.degree ≤ 0 := by
    apply degree_le_zero_of_norm_eval_le_log p hutop (M + ‖κ‖ * Real.pi + ‖K₀‖ + 1 + ‖κ‖)
    filter_upwards [hev1, hutop.eventually_ge_atTop 1] with t ht ht1
    have hlog := norm_log_le_log_norm_add_pi ht1
    have hlogpos := Real.log_nonneg ht1
    have h := htri t
    rw [norm_mul] at h
    have hk : ‖κ‖ * ‖Complex.log (u t)‖ ≤ ‖κ‖ * (Real.log ‖u t‖ + Real.pi) :=
      mul_le_mul_of_nonneg_left hlog (norm_nonneg _)
    have hk2 : ‖κ‖ * Real.log ‖u t‖ ≤ (M + ‖κ‖ * Real.pi + ‖K₀‖ + 1 + ‖κ‖) * Real.log ‖u t‖ :=
      mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg κ, norm_nonneg K₀, Real.pi_pos])
        hlogpos
    rw [mul_add] at hk
    have := norm_nonneg κ
    linarith
  have hpC := Polynomial.eq_C_of_degree_le_zero hpdeg
  have hκ : κ = 0 := by
    by_contra hκ
    have hκpos : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
    have hlogtend : Tendsto (fun t => Real.log ‖u t‖) atTop atTop :=
      Real.tendsto_log_atTop.comp hutop
    obtain ⟨t, ht, ht2⟩ := (hev1.and (hlogtend.eventually_gt_atTop
      ((M + ‖p.coeff 0‖ + ‖K₀‖ + 1) / ‖κ‖))).exists
    have h := htri t
    have h' := norm_sub_le (D t - p.eval (u t) - κ * Complex.log (u t) - K₀)
      (D t - p.eval (u t) - K₀)
    have e : D t - p.eval (u t) - κ * Complex.log (u t) - K₀ -
        (D t - p.eval (u t) - K₀) = -(κ * Complex.log (u t)) := by ring
    rw [e, norm_neg] at h'
    have n1 := norm_sub_le (D t - p.eval (u t)) K₀
    have n2 := norm_sub_le (D t) (p.eval (u t))
    have hpe : p.eval (u t) = p.coeff 0 := by rw [hpC, Polynomial.eval_C, Polynomial.coeff_C_zero]
    rw [hpe] at n1 n2 h' ht
    have hM' := hM t
    have hre_le : Real.log ‖u t‖ ≤ ‖Complex.log (u t)‖ := by
      rw [← Complex.log_re]; exact Complex.re_le_norm _
    rw [norm_mul] at h'
    rw [div_lt_iff₀ hκpos] at ht2
    have : ‖κ‖ * Real.log ‖u t‖ ≤ ‖κ‖ * ‖Complex.log (u t)‖ :=
      mul_le_mul_of_nonneg_left hre_le (norm_nonneg _)
    nlinarith
  exact ⟨hpdeg, hκ⟩

/-- **Rigidity under a Gamma-factor functional equation.** Let `f` be holomorphic and nonvanishing
on `Re s ≥ 1/2`, with `log f` a Dirichlet series `∑ c n n^{-s}` for large `Re s`, and let
`H(s) = A^s ∏ Γ(α_i s + β_i) / ∏ Γ(γ_j s + δ_j) · f(s)` with `A, α_i, γ_j > 0`,
`Re β_i, Re δ_j ≥ 0`. If `H(s) = w · conj (H(1 - conj s))` off a discrete set for some `|w| = 1`,
and `H` agrees off a discrete set with an entire function of finite order, then `f` is constant
on `Re s ≥ 1/2`. -/
theorem LSeries.exists_eq_const_of_gamma_functional_equation (f : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ f {s | 1 / 2 ≤ s.re})
    (hne : ∀ s : ℂ, 1 / 2 ≤ s.re → f s ≠ 0)
    (hlog : ∃ (c : ℕ → ℂ) (σ₀ : ℝ), ∀ s : ℂ, σ₀ < s.re →
      LSeriesSummable c s ∧ f s = Complex.exp (LSeries c s))
    (A : ℝ) (hA : 0 < A) (d₁ d₂ : ℕ) (α : Fin d₁ → ℝ) (β : Fin d₁ → ℂ)
    (γ : Fin d₂ → ℝ) (δ : Fin d₂ → ℂ)
    (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 ≤ (β i).re)
    (hγ : ∀ j, 0 < γ j) (hδ : ∀ j, 0 ≤ (δ j).re)
    (w : ℂ) (hw : ‖w‖ = 1)
    (hFE : ∀ᶠ s in Filter.codiscrete ℂ,
      (A : ℂ) ^ s * (∏ i, Complex.Gamma (α i * s + β i)) /
          (∏ j, Complex.Gamma (γ j * s + δ j)) * f s =
        w * starRingEnd ℂ ((A : ℂ) ^ (1 - starRingEnd ℂ s) *
          (∏ i, Complex.Gamma (α i * (1 - starRingEnd ℂ s) + β i)) /
          (∏ j, Complex.Gamma (γ j * (1 - starRingEnd ℂ s) + δ j)) * f (1 - starRingEnd ℂ s)))
    (horder : ∃ (E : ℂ → ℂ) (ρ : ℝ), Differentiable ℂ E ∧ Complex.HasGrowthOrderLE E ρ ∧
      ∀ᶠ s in Filter.codiscrete ℂ, E s = (A : ℂ) ^ s * (∏ i, Complex.Gamma (α i * s + β i)) /
        (∏ j, Complex.Gamma (γ j * s + δ j)) * f s) :
    ∃ C : ℂ, ∀ s : ℂ, 1 / 2 ≤ s.re → f s = C := by
  obtain ⟨c, σ₀, hc⟩ := hlog
  obtain ⟨E, ρ, hEd, hEρ, hEH⟩ := horder
  set G : ℂ → ℂ := fun s => (A : ℂ) ^ s * (∏ i, Complex.Gamma (α i * s + β i)) /
      (∏ j, Complex.Gamma (γ j * s + δ j)) with hG_def
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hreα : ∀ i (s : ℂ), 0 < s.re → 0 < ((α i : ℂ) * s + β i).re := by
    intro i s hs
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    nlinarith [hα i, hβ i]
  have hreγ : ∀ j (s : ℂ), 0 < s.re → 0 < ((γ j : ℂ) * s + δ j).re := by
    intro j s hs
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    nlinarith [hγ j, hδ j]
  have hnp : ∀ z : ℂ, 0 < z.re → ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro z hz m h
    rw [h] at hz
    simp at hz
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hGam : ∀ (a : ℝ) (b : ℂ) (s : ℂ), 0 < ((a : ℂ) * s + b).re →
      HasDerivAt (fun z => Complex.Gamma (a * z + b))
        (deriv Complex.Gamma (a * s + b) * a) s := by
    intro a b s hs
    have h1 : HasDerivAt (fun z : ℂ => (a : ℂ) * z + b) a s := by
      simpa using ((hasDerivAt_id s).const_mul (a : ℂ)).add_const b
    exact (Complex.differentiableAt_Gamma _ (hnp _ hs)).hasDerivAt.comp s h1
  have hNd : ∀ s : ℂ, 0 < s.re →
      DifferentiableAt ℂ (fun s => ∏ i, Complex.Gamma (α i * s + β i)) s := by
    intro s hs
    refine DifferentiableAt.fun_finsetProd fun i _ => ?_
    exact (hGam _ _ s (hreα i s hs)).differentiableAt
  have hDd : ∀ s : ℂ, 0 < s.re →
      DifferentiableAt ℂ (fun s => ∏ j, Complex.Gamma (γ j * s + δ j)) s := by
    intro s hs
    refine DifferentiableAt.fun_finsetProd fun j _ => ?_
    exact (hGam _ _ s (hreγ j s hs)).differentiableAt
  have hN0 : ∀ s : ℂ, 0 < s.re → ∏ i, Complex.Gamma (α i * s + β i) ≠ 0 := fun s hs =>
    Finset.prod_ne_zero_iff.mpr fun i _ => Complex.Gamma_ne_zero_of_re_pos (hreα i s hs)
  have hD0 : ∀ s : ℂ, 0 < s.re → ∏ j, Complex.Gamma (γ j * s + δ j) ≠ 0 := fun s hs =>
    Finset.prod_ne_zero_iff.mpr fun j _ => Complex.Gamma_ne_zero_of_re_pos (hreγ j s hs)
  have hApow : ∀ s : ℂ, HasDerivAt (fun z => (A : ℂ) ^ z) ((A : ℂ) ^ s * Complex.log A) s :=
    fun s => (Complex.hasStrictDerivAt_const_cpow (Or.inl hA0)).hasDerivAt
  have hApow0 : ∀ s : ℂ, (A : ℂ) ^ s ≠ 0 := fun s => by
    rw [Complex.cpow_def_of_ne_zero hA0]; exact Complex.exp_ne_zero _
  have hGd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ G s := fun s hs =>
    (((hApow s).differentiableAt).mul (hNd s hs)).div (hDd s hs) (hD0 s hs)
  have hG0 : ∀ s : ℂ, 0 < s.re → G s ≠ 0 := fun s hs =>
    div_ne_zero (mul_ne_zero (hApow0 s) (hN0 s hs)) (hD0 s hs)
  have hKd : ∀ s : ℂ, 1 / 2 ≤ s.re → DifferentiableAt ℂ (fun s => G s * f s) s :=
    fun s hs => (hGd s (by linarith)).mul (han s hs).differentiableAt
  have hEH' : ∀ s : ℂ, 1 / 2 ≤ s.re → E s = G s * f s := fun s hs =>
    apply_eq_of_eventually_codiscrete (G := fun s => G s * f s) hEd.continuous.continuousAt
      (hKd s hs).continuousAt hEH
  have hE0 : ∀ s, E s ≠ 0 := by
    intro s
    by_cases hs : 1 / 2 ≤ s.re
    · rw [hEH' s hs]; exact mul_ne_zero (hG0 s (by linarith)) (hne s hs)
    · push Not at hs
      have hs' : 1 / 2 ≤ (1 - starRingEnd ℂ s).re := by
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
      have h1 : ContinuousAt (fun z => 1 - starRingEnd ℂ z) s :=
        (continuous_const.sub Complex.continuous_conj).continuousAt
      have h2 : ContinuousAt (fun z => G (1 - starRingEnd ℂ z) * f (1 - starRingEnd ℂ z)) s :=
        ContinuousAt.comp (g := fun s => G s * f s) (hKd _ hs').continuousAt h1
      have hcont : ContinuousAt (fun z => w * starRingEnd ℂ
          (G (1 - starRingEnd ℂ z) * f (1 - starRingEnd ℂ z))) s :=
        continuousAt_const.mul (Complex.continuous_conj.continuousAt.comp h2)
      have heq := apply_eq_of_eventually_codiscrete hEd.continuous.continuousAt hcont
        ((hEH.and hFE).mono fun z ⟨h1, h2⟩ => h1.trans h2)
      rw [heq]
      refine mul_ne_zero (by rintro rfl; simp at hw) ?_
      rw [map_ne_zero]
      exact mul_ne_zero (hG0 _ (by linarith)) (hne _ hs')
  obtain ⟨g, hg⟩ := Complex.exists_polynomial_eq_exp_of_hasGrowthOrderLE hEd hEρ hE0
  have hab : LSeries.abscissaOfAbsConv c ≤ σ₀ :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      (hc y (by simpa using hy)).1
  set σ' := max σ₀ 1 with hσ'
  set σ := σ' + 1 with hσ
  have hσ₀σ' : σ₀ ≤ σ' := le_max_left _ _
  have h1σ' : 1 ≤ σ' := le_max_right _ _
  have hident : ∀ s : ℂ, σ' < s.re →
      Complex.exp (g.eval s) = G s * Complex.exp (LSeries c s) := by
    intro s hs
    rw [← hg, hEH' s (by linarith), (hc s (by linarith)).2]
  set p := Polynomial.derivative g with hp
  have hstar : ∀ s : ℂ, σ' < s.re → deriv (LSeries c) s = p.eval s - Complex.log A
      - (∑ i, (α i : ℂ) * Complex.digamma (α i * s + β i))
      + ∑ j, (γ j : ℂ) * Complex.digamma (γ j * s + δ j) := by
    intro s hs
    have hs0 : 0 < s.re := by linarith
    have hLd : DifferentiableAt ℂ (LSeries c) s :=
      (LSeries_hasDerivAt (hab.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith)))).differentiableAt
    have hev : (fun z => Complex.exp (g.eval z)) =ᶠ[𝓝 s]
        (fun z => G z * Complex.exp (LSeries c z)) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
        using hident z hz
    have hlog_eq : logDeriv (fun z => Complex.exp (g.eval z)) s =
        logDeriv (fun z => G z * Complex.exp (LSeries c z)) s := by
      simp only [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    have hl : logDeriv (fun z => Complex.exp (g.eval z)) s = p.eval s := by
      rw [logDeriv_apply, ((Polynomial.hasDerivAt g s).cexp).deriv, hp]
      field_simp
    have hr : logDeriv (fun z => G z * Complex.exp (LSeries c z)) s =
        logDeriv G s + deriv (LSeries c) s := by
      rw [logDeriv_fun_mul (f := G) (g := fun z => Complex.exp (LSeries c z)) s (hG0 s hs0)
          (Complex.exp_ne_zero _) (hGd s hs0) hLd.cexp]
      congr 1
      rw [logDeriv_apply, hLd.hasDerivAt.cexp.deriv]
      field_simp
    have hGl : logDeriv G s = Complex.log A
        + (∑ i, (α i : ℂ) * Complex.digamma (α i * s + β i))
        - ∑ j, (γ j : ℂ) * Complex.digamma (γ j * s + δ j) := by
      have e1 := logDeriv_fun_div (f := fun z => (A : ℂ) ^ z * ∏ i, Complex.Gamma (α i * z + β i))
        (g := fun z => ∏ j, Complex.Gamma (γ j * z + δ j)) s
        (mul_ne_zero (hApow0 s) (hN0 s hs0)) (hD0 s hs0)
        (((hApow s).differentiableAt).mul (hNd s hs0)) (hDd s hs0)
      have e2 := logDeriv_fun_mul (f := fun z => (A : ℂ) ^ z)
        (g := fun z => ∏ i, Complex.Gamma (α i * z + β i)) s (hApow0 s) (hN0 s hs0)
        (hApow s).differentiableAt (hNd s hs0)
      have e3 := logDeriv_fun_prod (s := Finset.univ)
        (f := fun i z => Complex.Gamma (α i * z + β i)) (x := s)
        (fun i _ => Complex.Gamma_ne_zero_of_re_pos (hreα i s hs0))
        (fun i _ => (hGam _ _ s (hreα i s hs0)).differentiableAt)
      have e4 := logDeriv_fun_prod (s := Finset.univ)
        (f := fun j z => Complex.Gamma (γ j * z + δ j)) (x := s)
        (fun j _ => Complex.Gamma_ne_zero_of_re_pos (hreγ j s hs0))
        (fun j _ => (hGam _ _ s (hreγ j s hs0)).differentiableAt)
      have e5 : logDeriv (fun z => (A : ℂ) ^ z) s = Complex.log A := by
        rw [logDeriv_apply, (hApow s).deriv]; field_simp [hApow0 s]
      have e6 : ∀ (a : ℝ) (b : ℂ), 0 < ((a : ℂ) * s + b).re →
          logDeriv (fun z => Complex.Gamma (a * z + b)) s = a * Complex.digamma (a * s + b) := by
        intro a b hab'
        rw [logDeriv_apply, (hGam a b s hab').deriv, Complex.digamma_def, logDeriv_apply]
        ring
      rw [hG_def, e1, e2, e3, e4, e5]
      rw [Finset.sum_congr rfl (fun i _ => e6 (α i) (β i) (hreα i s hs0)),
        Finset.sum_congr rfl (fun j _ => e6 (γ j) (δ j) (hreγ j s hs0))]
    rw [hl, hr, hGl] at hlog_eq
    linear_combination -hlog_eq
  -- the vertical line `Re s = σ`
  set u : ℝ → ℂ := fun t => (σ : ℂ) + (t : ℂ) * Complex.I with hu_def
  have hure : ∀ t, (u t).re = σ := by intro t; simp [hu_def]
  have hunorm : ∀ t, |t| ≤ ‖u t‖ := by
    intro t
    have := Complex.abs_im_le_norm (u t)
    simpa [hu_def] using this
  have hutop : Tendsto (fun t => ‖u t‖) atTop atTop :=
    tendsto_atTop_mono (fun t => (le_abs_self t).trans (hunorm t)) tendsto_id
  have hubot : Tendsto (fun t => ‖u t‖) atBot atTop :=
    tendsto_atTop_mono (fun t => (neg_le_abs t).trans (hunorm t)) tendsto_neg_atBot_atTop
  set κ : ℂ := (∑ j, (γ j : ℂ)) - ∑ i, (α i : ℂ) with hκ_def
  set K₀ : ℂ := -Complex.log A - (∑ i, (α i : ℂ) * (Real.log (α i) : ℂ))
    + ∑ j, (γ j : ℂ) * (Real.log (γ j) : ℂ) with hK₀_def
  have hF : ∀ l : Filter ℝ, Tendsto (fun t => ‖u t‖) l atTop →
      Tendsto (fun t => deriv (LSeries c) (u t) - p.eval (u t) - κ * Complex.log (u t) - K₀)
        l (𝓝 0) := by
    intro l hl
    have hre : ∀ᶠ t in l, 0 < (u t).re := Eventually.of_forall fun t => by rw [hure]; linarith
    have h1 := tendsto_finsetSum Finset.univ (fun i _ =>
      (tendsto_digamma_mul_add_sub_log (hα i) (β i) (hβ i) hl hre).const_mul (α i : ℂ))
    have h2 := tendsto_finsetSum Finset.univ (fun j _ =>
      (tendsto_digamma_mul_add_sub_log (hγ j) (δ j) (hδ j) hl hre).const_mul (γ j : ℂ))
    have hlim := h1.neg.add h2
    simp only [mul_zero, Finset.sum_const_zero, neg_zero, add_zero] at hlim
    refine hlim.congr fun t => ?_
    rw [hstar (u t) (by rw [hure]; linarith)]
    simp only [hκ_def, hK₀_def, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    ring
  set M := ∑' n, ‖LSeries.term (LSeries.logMul c) σ n‖ with hM_def
  have hM : ∀ t, ‖deriv (LSeries c) (u t)‖ ≤ M := by
    intro t
    have hlt : LSeries.abscissaOfAbsConv c < (u t).re := by
      rw [hure]; exact hab.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
    rw [LSeries_deriv hlt, norm_neg]
    have hsum : LSeriesSummable (LSeries.logMul c) (σ : ℂ) :=
      LSeriesSummable_logMul_of_lt_re (by
        rw [Complex.ofReal_re]; exact hab.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith)))
    have heqn : (fun n => ‖LSeries.term (LSeries.logMul c) (u t) n‖) =
        fun n => ‖LSeries.term (LSeries.logMul c) σ n‖ := by
      funext n; simp only [LSeries.norm_term_eq, hure, Complex.ofReal_re]
    calc ‖LSeries (LSeries.logMul c) (u t)‖
        ≤ ∑' n, ‖LSeries.term (LSeries.logMul c) (u t) n‖ :=
          norm_tsum_le_tsum_norm (heqn ▸ hsum.norm)
      _ = M := by rw [heqn]
  have hM0 : 0 ≤ M := tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨hpdeg, hκ⟩ := degree_le_zero_and_eq_zero_of_tendsto (fun t => deriv (LSeries c) (u t)) M
      hM p κ K₀ u hutop
    (hF atTop hutop)
  have hpC := Polynomial.eq_C_of_degree_le_zero hpdeg
  set K : ℂ := p.coeff 0 + K₀ with hK_def
  have hLconv : ∀ l : Filter ℝ, Tendsto (fun t => ‖u t‖) l atTop →
      Tendsto (fun t => deriv (LSeries c) (u t)) l (𝓝 K) := by
    intro l hl
    have := (hF l hl).add_const K
    rw [zero_add] at this
    refine this.congr fun t => ?_
    rw [hpC, Polynomial.eval_C, hκ, hK_def]
    ring
  have hσ₀σ : σ₀ < σ := by linarith
  have hcoef : ∀ n : ℕ, 2 ≤ n → c n = 0 := coeff_eq_zero_of_tendsto_deriv c σ₀ σ hab hσ₀σ K hLconv
  have hLconst : ∀ s : ℂ, σ₀ < s.re → LSeries c s = c 1 := by
    intro s _
    rw [LSeries, tsum_eq_single 1]
    · simp
    · intro m hm
      rcases eq_or_ne m 0 with rfl | hm0
      · simp
      · rw [LSeries.term_of_ne_zero hm0, hcoef m (by omega), zero_div]
  refine ⟨Complex.exp (c 1), fun s hs => ?_⟩
  have hU : IsPreconnected {s : ℂ | 1 / 2 ≤ s.re} :=
    (convex_halfSpace_re_ge (1 / 2)).isPreconnected
  have hEq := han.eqOn_of_preconnected_of_eventuallyEq (g := fun _ => Complex.exp (c 1))
    analyticOnNhd_const hU (z₀ := (σ : ℂ))
    (show (1 : ℝ) / 2 ≤ ((σ : ℂ)).re by rw [Complex.ofReal_re]; linarith) ?_
  · exact hEq hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show σ₀ < ((σ : ℂ)).re by rw [Complex.ofReal_re]; exact hσ₀σ)] with z hz
  rw [(hc z hz).2, hLconst z hz]

