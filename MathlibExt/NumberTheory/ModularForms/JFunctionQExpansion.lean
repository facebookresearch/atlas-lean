/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.LevelNAlgebra
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The integral q-expansion of the j-function

For $\tau$ in the upper half-plane and $q = e^{2\pi i\tau}$, the level-one $j$-function
$j = E_4^3/\Delta$ (`WLight.jFunction`) has the expansion

$$j(\tau) = \frac{1}{q} + 744 + \sum_{n \ge 1} c_n q^n$$

with integers $c_n$, the series converging absolutely, and $c_1 = 196884$
(`WLight.jFunction_qExpansion_int`).

The proof writes $E_4$, $E_6$ as power series in $q$ with integer coefficients, gets
$\Delta = (E_4^3 - E_6^2)/1728 = q\,P(q)$ with $P$ an integral power series with constant term
$1$ (the divisibility by $1728$ comes from $12 \mid 5\sigma_3(n) + 7\sigma_5(n)$), and reads off
the Taylor coefficients of the holomorphic function $E_4^3/P$ on the unit disc, which are integers
because those of $P$ are and $P(0) = 1$.

The source is Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT
OpenCourseWare, Fall 2025, Lecture 19, Lemma 19.5 and Corollary 19.6.
-/

@[expose] public section

set_option autoImplicit false

open Complex UpperHalfPlane Filter Topology PowerSeries ArithmeticFunction

namespace WLight

/-! ### Taylor coefficients at the origin -/

/-- The `n`-th Taylor coefficient of `f` at `0`. -/
private noncomputable def tc (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / n.factorial

/-- The Taylor series of `f` at `0`, as a formal power series. -/
private noncomputable def ser (f : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk (tc f)

private theorem tc_eq_of_hasFPowerSeriesAt {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) 0) (n : ℕ) :
    tc f n = c n := by
  have h := HasFPowerSeriesAt.eq_formalMultilinearSeries hf.analyticAt.hasFPowerSeriesAt hf
  have := congrArg (fun p => FormalMultilinearSeries.coeff p n) h
  simpa [FormalMultilinearSeries.coeff_ofScalars, tc] using this

private theorem tc_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    tc (f * g) n = ∑ kl ∈ Finset.antidiagonal n, tc f kl.1 * tc g kl.2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, tc,
    iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [tc]
  rw [Nat.cast_choose ℂ hk']
  have h1 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h2 : ((n - k).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - k).factorial_ne_zero
  have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

private theorem ser_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    ser (f * g) = ser f * ser g := by
  ext n
  simp [ser, coeff_mul, tc_mul hf hg]

private theorem ser_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    ser (f ^ (n + 1)) = ser f ^ (n + 1) := by
  induction n with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ n ih => rw [pow_succ, ser_mul (hf.pow (n + 1)) hf, ih, ← pow_succ]

private theorem ser_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) : ser f = ser g := by
  ext n
  simp [ser, tc, h.iteratedDeriv_eq n]

private theorem ser_eq_map_of_mul {f g h : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (hfg : f * g =ᶠ[𝓝 0] h) {G H : PowerSeries ℤ}
    (hG : ser g = map (Int.castRingHom ℂ) G) (hH : ser h = map (Int.castRingHom ℂ) H)
    (hG0 : constantCoeff G = 1) :
    ser f = map (Int.castRingHom ℂ) (H * G.invOfUnit 1) := by
  have hmul : ser f * map (Int.castRingHom ℂ) G = map (Int.castRingHom ℂ) H := by
    rw [← hG, ← ser_mul hf hg, ser_congr hfg, hH]
  have hinv : G * G.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit G 1 (by simpa using hG0)
  calc ser f = ser f * map (Int.castRingHom ℂ) (G * G.invOfUnit 1) := by
        rw [hinv, map_one, mul_one]
    _ = _ := by rw [map_mul, ← mul_assoc, hmul, map_mul]

/-! ### Power series on the unit disc -/

/-- The sum of the power series with coefficients `c` at `q`. -/
private noncomputable def ps (c : ℕ → ℂ) (q : ℂ) : ℂ := ∑' n, c n * q ^ n

private theorem mem_eball_iff {y : ℂ} {R : NNReal} :
    y ∈ Metric.eball (0 : ℂ) R ↔ ‖y‖ < R := by
  simp

private theorem norm_lt_one_of_mem_eball {y : ℂ} (hy : y ∈ Metric.eball (0 : ℂ) 1) :
    ‖y‖ < 1 := by
  have h : y ∈ Metric.eball (0 : ℂ) ((1 : NNReal) : ENNReal) := by simpa using hy
  simpa using mem_eball_iff.mp h

private theorem mem_eball_of_norm_lt {y : ℂ} {R : NNReal} (hy : ‖y‖ < R) :
    y ∈ Metric.eball (0 : ℂ) R :=
  mem_eball_iff.mpr hy

private theorem ps_hasFPowerSeriesOnBall {c : ℕ → ℂ}
    (hc : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun n => ‖c n‖ * r ^ n) :
    HasFPowerSeriesOnBall (ps c) (FormalMultilinearSeries.ofScalars ℂ c) 0 1 where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
    refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
    simpa [FormalMultilinearSeries.ofScalars_norm] using hc r r.2 hr1
  r_pos := one_pos
  hasSum := by
    intro y hy
    have hy' := norm_lt_one_of_mem_eball hy
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, ps, smul_eq_mul]
    refine (Summable.of_norm ?_).hasSum
    simpa [norm_mul, norm_pow] using hc ‖y‖ (norm_nonneg y) hy'

private theorem exists_nnreal_between {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    ∃ R : NNReal, x < R ∧ (R : ℝ) < 1 := by
  refine ⟨Real.toNNReal ((x + 1) / 2), ?_, ?_⟩ <;>
    rw [Real.coe_toNNReal _ (by positivity)] <;> linarith

private theorem hasFPowerSeriesOnBall_tc {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) {R : NNReal} (hR0 : 0 < R)
    (hR : (R : ℝ) < 1) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ (tc f)) 0 R := by
  have hsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 1 := Metric.closedBall_subset_ball hR
  have h := (hf.mono hsub).hasFPowerSeriesOnBall hR0
  have he := HasFPowerSeriesAt.eq_formalMultilinearSeries h.hasFPowerSeriesAt
    h.analyticAt.hasFPowerSeriesAt
  rw [he] at h
  exact h

private theorem hasSum_tc {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) {q : ℂ}
    (hq : ‖q‖ < 1) : HasSum (fun n => tc f n * q ^ n) (f q) := by
  obtain ⟨R, hqR, hR1⟩ := exists_nnreal_between (norm_nonneg q) hq
  have hR0 : 0 < R := by exact_mod_cast (lt_of_le_of_lt (norm_nonneg q) hqR)
  have h := (hasFPowerSeriesOnBall_tc hf hR0 hR1).hasSum (mem_eball_of_norm_lt hqR)
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using h

private theorem summable_tc {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) : Summable fun n => ‖tc f n‖ * r ^ n := by
  obtain ⟨R, hrR, hR1⟩ := exists_nnreal_between hr0 hr
  have hR0 : 0 < R := by exact_mod_cast (lt_of_le_of_lt hr0 hrR)
  have h := hasFPowerSeriesOnBall_tc hf hR0 hR1
  have hlt : ((Real.toNNReal r : NNReal) : ENNReal) <
      (FormalMultilinearSeries.ofScalars ℂ (tc f)).radius := by
    refine lt_of_lt_of_le ?_ h.r_le
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]
    exact hrR
  have hs := FormalMultilinearSeries.summable_norm_mul_pow _ hlt
  rw [Real.coe_toNNReal _ hr0] at hs
  simpa [FormalMultilinearSeries.ofScalars_norm] using hs

private theorem differentiableOn_of_hasFPowerSeriesOnBall {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hf : HasFPowerSeriesOnBall f p 0 1) :
    DifferentiableOn ℂ f (Metric.ball 0 1) := by
  have h := hf.differentiableOn
  have he : Metric.eball (0 : ℂ) 1 = Metric.ball 0 1 := by
    ext y
    refine ⟨fun hy => mem_ball_zero_iff.mpr (norm_lt_one_of_mem_eball hy), fun hy => ?_⟩
    have h1 : y ∈ Metric.eball (0 : ℂ) ((1 : NNReal) : ENNReal) :=
      mem_eball_of_norm_lt (by simpa using mem_ball_zero_iff.mp hy)
    simpa using h1
  rwa [he] at h

private theorem analyticAt_zero {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) :
    AnalyticAt ℂ f 0 :=
  hf.analyticAt (Metric.ball_mem_nhds 0 one_pos)

/-! ### The Eisenstein series as power series in `q` -/

private theorem sigma_le_pow (k n : ℕ) : sigma k n ≤ n ^ (k + 1) := by
  rw [sigma_apply, pow_succ]
  calc ∑ d ∈ n.divisors, d ^ k ≤ ∑ _d ∈ n.divisors, n ^ k :=
        Finset.sum_le_sum fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) k
    _ = n.divisors.card * n ^ k := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * n ^ k := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self n)
    _ = n ^ k * n := mul_comm _ _

/-- The coefficients `1, m σ_k(1), m σ_k(2), …`. -/
private def eisCoeff (m : ℤ) (k n : ℕ) : ℤ := if n = 0 then 1 else m * sigma k n

private theorem norm_eisCoeff_le (m : ℤ) {k : ℕ} (hk : k ≤ 5) (n : ℕ) :
    ‖((eisCoeff m k n : ℤ) : ℂ)‖ ≤ |(m : ℝ)| * (n : ℝ) ^ 6 + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eisCoeff]
  · have h1 : (sigma k n : ℝ) ≤ (n : ℝ) ^ 6 := by
      have : sigma k n ≤ n ^ 6 := (sigma_le_pow k n).trans (Nat.pow_le_pow_right hn (by omega))
      exact_mod_cast this
    have h2 : ‖((eisCoeff m k n : ℤ) : ℂ)‖ = |(m : ℝ)| * (sigma k n : ℝ) := by
      simp [eisCoeff, hn.ne']
    rw [h2]
    nlinarith [abs_nonneg (m : ℝ)]

private theorem summable_eisCoeff (m : ℤ) {k : ℕ} (hk : k ≤ 5) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) : Summable fun n => ‖((eisCoeff m k n : ℤ) : ℂ)‖ * r ^ n := by
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ 6 * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 6 (by rwa [Real.norm_of_nonneg hr0])
  have h2 : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((h1.mul_left |(m : ℝ)|).add h2)
  calc ‖((eisCoeff m k n : ℤ) : ℂ)‖ * r ^ n ≤ (|(m : ℝ)| * (n : ℝ) ^ 6 + 1) * r ^ n :=
        mul_le_mul_of_nonneg_right (norm_eisCoeff_le m hk n) (by positivity)
    _ = |(m : ℝ)| * ((n : ℝ) ^ 6 * r ^ n) + r ^ n := by ring

private theorem hasFPS_eis (m : ℤ) {k : ℕ} (hk : k ≤ 5) :
    HasFPowerSeriesOnBall (ps fun n => ((eisCoeff m k n : ℤ) : ℂ))
      (FormalMultilinearSeries.ofScalars ℂ fun n => ((eisCoeff m k n : ℤ) : ℂ)) 0 1 :=
  ps_hasFPowerSeriesOnBall fun _ hr0 hr => summable_eisCoeff m hk hr0 hr

private theorem norm_qParam_lt (τ : ℍ) : ‖Function.Periodic.qParam 1 τ‖ < 1 := by
  simpa using norm_qParam_lt_one 1 τ

private theorem E_eq_ps {k : ℕ} (hk : 3 ≤ k) (hke : Even k) (hk5 : k - 1 ≤ 5) (m : ℤ)
    (hm : -(2 * k / bernoulli k : ℚ) = m) (τ : ℍ) :
    ModularForm.E hk τ =
      ps (fun n => ((eisCoeff m (k - 1) n : ℤ) : ℂ)) (Function.Periodic.qParam 1 τ) := by
  set q := Function.Periodic.qParam 1 τ with hqdef
  have hq : ‖q‖ < 1 := norm_qParam_lt τ
  have hs0 := summable_eisCoeff m hk5 (norm_nonneg q) hq
  have hs : Summable fun n => ((eisCoeff m (k - 1) n : ℤ) : ℂ) * q ^ n :=
    Summable.of_norm (by simpa [norm_mul, norm_pow] using hs0)
  have hexp : cexp (2 * Real.pi * Complex.I * τ) = q := by simp [hqdef, Function.Periodic.qParam]
  have hc : (2 * k / (bernoulli k : ℂ)) = -(m : ℂ) := by
    rw [neg_eq_iff_eq_neg] at hm
    exact_mod_cast hm
  rw [EisensteinSeries.q_expansion_bernoulli hk hke τ]
  simp only [zpow_natCast]
  rw [ps, hs.tsum_eq_zero_add, tsum_pnat_eq_tsum_succ
      (f := fun n => ((sigma (k - 1) n : ℕ) : ℂ) * cexp (2 * Real.pi * Complex.I * τ) ^ n),
    hexp, hc]
  have hterm : ∀ n : ℕ, ((eisCoeff m (k - 1) (n + 1) : ℤ) : ℂ) * q ^ (n + 1) =
      (m : ℂ) * (((sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1)) := by
    intro n
    simp [eisCoeff]
    ring
  simp only [hterm, tsum_mul_left]
  simp [eisCoeff]

private theorem bernoulli_four' : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]

private theorem bernoulli_six' : bernoulli 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, h5, Nat.choose]

/-- `E₄` as a function of `q`. -/
private noncomputable def fA : ℂ → ℂ := ps fun n => ((eisCoeff 240 3 n : ℤ) : ℂ)

/-- `E₆` as a function of `q`. -/
private noncomputable def fB : ℂ → ℂ := ps fun n => ((eisCoeff (-504) 5 n : ℤ) : ℂ)

private theorem E₄_eq (τ : ℍ) : ModularForm.E₄ τ = fA (Function.Periodic.qParam 1 τ) :=
  E_eq_ps (k := 4) (by norm_num) (by decide) (by norm_num) 240
    (by rw [bernoulli_four']; norm_num) τ

private theorem E₆_eq (τ : ℍ) : ModularForm.E₆ τ = fB (Function.Periodic.qParam 1 τ) :=
  E_eq_ps (k := 6) (by norm_num) (by decide) (by norm_num) (-504)
    (by rw [bernoulli_six']; norm_num) τ

/-! ### Integer power series -/

private noncomputable def serA : PowerSeries ℤ := PowerSeries.mk (eisCoeff 240 3)
private noncomputable def serB : PowerSeries ℤ := PowerSeries.mk (eisCoeff (-504) 5)
private noncomputable def serU : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (sigma 3 n : ℤ)
private noncomputable def serV : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (sigma 5 n : ℤ)
private noncomputable def serW : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (5 * sigma 3 n + 7 * sigma 5 n : ℤ) / 12
/-- `Δ` as a power series in `q`. -/
private noncomputable def serD : PowerSeries ℤ :=
  serW + 100 * serU ^ 2 + 8000 * serU ^ 3 - 147 * serV ^ 2
/-- `Δ / q` as a power series in `q`. -/
private noncomputable def serP : PowerSeries ℤ := PowerSeries.mk fun n => coeff (n + 1) serD

private theorem twelve_dvd (n : ℕ) : (12 : ℤ) ∣ 5 * sigma 3 n + 7 * sigma 5 n := by
  have key : ∀ d : ℕ, (12 : ℤ) ∣ 5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5 := by
    intro d
    have h : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
    have := h d
    have hc : ((5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5 : ℤ) : ZMod 12) = 0 := by
      push_cast; exact this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp hc
  simp only [sigma_apply]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _ => key d

private theorem serW_rel : 12 * serW = 5 * serU + 7 * serV := by
  ext n
  rcases n with _ | n
  · simp [serW, serU, serV]
  · have h := Int.mul_ediv_cancel' (twelve_dvd (n + 1))
    simp [serW, serU, serV, h]

private theorem serA_eq : serA = 1 + 240 * serU := by
  ext n
  rcases n with _ | n
  · simp [serA, serU, eisCoeff]
  · simp [serA, serU, eisCoeff]

private theorem serB_eq : serB = 1 - 504 * serV := by
  ext n
  rcases n with _ | n
  · simp [serB, serV, eisCoeff]
  · simp [serB, serV, eisCoeff]

private theorem serD_rel : serA ^ 3 - serB ^ 2 = 1728 * serD := by
  rw [serA_eq, serB_eq, serD]
  linear_combination (-144) * serW_rel

/-! ### The Taylor series of the functions of `q` -/

/-- Base change of integer power series to `ℂ`. -/
private noncomputable abbrev toC : PowerSeries ℤ →+* PowerSeries ℂ :=
  PowerSeries.map (Int.castRingHom ℂ)

private theorem ser_fA : ser fA = toC serA := by
  ext n
  simp [ser, serA, fA,
    tc_eq_of_hasFPowerSeriesAt (hasFPS_eis 240 (k := 3) (by norm_num)).hasFPowerSeriesAt]

private theorem ser_fB : ser fB = toC serB := by
  ext n
  simp [ser, serB, fB,
    tc_eq_of_hasFPowerSeriesAt (hasFPS_eis (-504) (k := 5) (by norm_num)).hasFPowerSeriesAt]

private theorem diff_fA : DifferentiableOn ℂ fA (Metric.ball 0 1) :=
  differentiableOn_of_hasFPowerSeriesOnBall (hasFPS_eis 240 (k := 3) (by norm_num))

private theorem diff_fB : DifferentiableOn ℂ fB (Metric.ball 0 1) :=
  differentiableOn_of_hasFPowerSeriesOnBall (hasFPS_eis (-504) (k := 5) (by norm_num))

/-- `Δ` as a function of `q`. -/
private noncomputable def fD (q : ℂ) : ℂ := (fA q ^ 3 - fB q ^ 2) / 1728

private theorem diff_fD : DifferentiableOn ℂ fD (Metric.ball 0 1) :=
  ((diff_fA.pow 3).sub (diff_fB.pow 2)).div_const _

private theorem discriminant_eq (τ : ℍ) :
    ModularForm.discriminant τ = fD (Function.Periodic.qParam 1 τ) := by
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, E₄_eq, E₆_eq, fD]

private theorem ser_fD : ser fD = toC serD := by
  have hA := analyticAt_zero diff_fA
  have hB := analyticAt_zero diff_fB
  have h3 : ser (fA ^ 3) = toC serA ^ 3 := by rw [ser_pow hA 2, ser_fA]
  have h2 : ser (fB ^ 2) = toC serB ^ 2 := by rw [ser_pow hB 1, ser_fB]
  have e : toC serA ^ 3 - toC serB ^ 2 = 1728 * toC serD := by
    rw [← map_pow, ← map_pow, ← map_sub, serD_rel, map_mul, map_ofNat]
  ext n
  have key : tc fD n = (tc (fA ^ 3) n - tc (fB ^ 2) n) / 1728 := by
    simp only [tc]
    rw [show fD = fun q => (fA ^ 3 - fB ^ 2) q / 1728 from rfl, iteratedDeriv_div_const,
      iteratedDeriv_sub (hA.pow 3).contDiffAt (hB.pow 2).contDiffAt]
    ring
  calc coeff n (ser fD) = tc fD n := coeff_mk _ _
    _ = (coeff n (ser (fA ^ 3)) - coeff n (ser (fB ^ 2))) / 1728 := by
        rw [key]; simp [ser]
    _ = coeff n (toC serA ^ 3 - toC serB ^ 2) / 1728 := by rw [h3, h2, map_sub]
    _ = coeff n (toC serD) := by
        rw [e]
        simp

private theorem tc_fD (n : ℕ) : tc fD n = ((coeff n serD : ℤ) : ℂ) := by
  have := congrArg (coeff n) ser_fD
  simpa [ser] using this

/-! ### Explicit coefficients -/

private theorem sigma_vals : sigma 3 1 = 1 ∧ sigma 3 2 = 9 ∧ sigma 3 3 = 28 ∧
    sigma 5 1 = 1 ∧ sigma 5 2 = 33 ∧ sigma 5 3 = 244 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem coeff_serD : coeff 0 serD = 0 ∧ coeff 1 serD = 1 ∧ coeff 2 serD = -24 ∧
    coeff 3 serD = 252 := by
  obtain ⟨h31, h32, h33, h51, h52, h53⟩ := sigma_vals
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [serD, serW, serU, serV, pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_succ,
      h31, h32, h33, h51, h52, h53]

/-! ### `Δ / q` -/

/-- `Δ / q` as a function of `q`. -/
private noncomputable def fP : ℂ → ℂ := ps fun n => ((coeff (n + 1) serD : ℤ) : ℂ)

private theorem summable_P {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun n => ‖((coeff (n + 1) serD : ℤ) : ℂ)‖ * r ^ n := by
  set R := (r + 1) / 2 with hR
  have hR0 : 0 < R := by positivity
  have hrR : r ≤ R := by linarith
  have hR1 : R < 1 := by linarith
  have hs := summable_tc diff_fD hR0.le hR1
  have hs' : Summable fun n => ‖tc fD (n + 1)‖ * R ^ (n + 1) := (summable_nat_add_iff 1).mpr hs
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hs'.mul_left R⁻¹)
  rw [tc_fD]
  have h1 : r ^ n ≤ R ^ n := pow_le_pow_left₀ hr0 hrR n
  calc ‖((coeff (n + 1) serD : ℤ) : ℂ)‖ * r ^ n
        ≤ ‖((coeff (n + 1) serD : ℤ) : ℂ)‖ * R ^ n :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = R⁻¹ * (‖((coeff (n + 1) serD : ℤ) : ℂ)‖ * R ^ (n + 1)) := by
          field_simp
          ring

private theorem hasFPS_P :
    HasFPowerSeriesOnBall fP
      (FormalMultilinearSeries.ofScalars ℂ fun n => ((coeff (n + 1) serD : ℤ) : ℂ)) 0 1 :=
  ps_hasFPowerSeriesOnBall fun _ hr0 hr => summable_P hr0 hr

private theorem diff_fP : DifferentiableOn ℂ fP (Metric.ball 0 1) :=
  differentiableOn_of_hasFPowerSeriesOnBall hasFPS_P

private theorem ser_fP : ser fP = toC serP := by
  ext n
  simp [ser, serP, tc_eq_of_hasFPowerSeriesAt hasFPS_P.hasFPowerSeriesAt]

private theorem fP_zero : fP 0 = 1 := by
  simp only [fP, ps]
  rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp [coeff_serD.2.1]

private theorem mul_fP (q : ℂ) (hq : ‖q‖ < 1) : q * fP q = fD q := by
  have h1 := hasSum_tc diff_fD hq
  have h2 := (hasSum_nat_add_iff' 1).mpr h1
  simp only [Finset.sum_range_one, tc_fD, coeff_serD.1, pow_zero, Int.cast_zero, zero_mul,
    sub_zero] at h2
  have hs0 := summable_P (norm_nonneg q) hq
  have h3 : HasSum (fun n => ((coeff (n + 1) serD : ℤ) : ℂ) * q ^ n) (fP q) :=
    (Summable.of_norm (by simpa [norm_mul, norm_pow] using hs0)).hasSum
  have h4 := h3.mul_left q
  have h2' : HasSum (fun n => q * (((coeff (n + 1) serD : ℤ) : ℂ) * q ^ n)) (fD q) := by
    convert h2 using 1
    funext n
    ring
  exact h4.unique h2'

private theorem fP_ne_zero (q : ℂ) (hq : ‖q‖ < 1) : fP q ≠ 0 := by
  by_cases hq0 : q = 0
  · rw [hq0, fP_zero]
    exact one_ne_zero
  · intro hP
    let τ : ℍ := UpperHalfPlane.mk (Function.Periodic.invQParam 1 q)
      (Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hq0)
    have hτ : Function.Periodic.qParam 1 τ = q := by
      rw [UpperHalfPlane.coe_mk]
      exact Function.Periodic.qParam_right_inv one_ne_zero hq0
    have h := ModularForm.discriminant_ne_zero τ
    rw [discriminant_eq, hτ, ← mul_fP q hq, hP, mul_zero] at h
    exact h rfl

/-! ### `q j` -/

/-- `q j` as a function of `q`. -/
private noncomputable def fG (q : ℂ) : ℂ := fA q ^ 3 / fP q

private theorem diff_fG : DifferentiableOn ℂ fG (Metric.ball 0 1) :=
  (diff_fA.pow 3).div diff_fP fun q hq => fP_ne_zero q (mem_ball_zero_iff.mp hq)

private noncomputable def serG : PowerSeries ℤ := serA ^ 3 * serP.invOfUnit 1

private theorem constantCoeff_serP : constantCoeff serP = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, serP, coeff_mk]
  exact coeff_serD.2.1

private theorem ser_fG : ser fG = toC serG := by
  have hA := analyticAt_zero diff_fA
  have hev : fG * fP =ᶠ[𝓝 0] fA ^ 3 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    simp only [Pi.mul_apply, Pi.pow_apply, fG]
    exact div_mul_cancel₀ _ (fP_ne_zero q (mem_ball_zero_iff.mp hq))
  have h3 : ser (fA ^ 3) = toC (serA ^ 3) := by rw [ser_pow hA 2, ser_fA, map_pow]
  exact ser_eq_map_of_mul (analyticAt_zero diff_fG) (analyticAt_zero diff_fP) hev ser_fP h3
    constantCoeff_serP

private theorem tc_fG (n : ℕ) : tc fG n = ((coeff n serG : ℤ) : ℂ) := by
  have := congrArg (coeff n) ser_fG
  simpa [ser] using this

private theorem coeff_serG : coeff 0 serG = 1 ∧ coeff 1 serG = 744 ∧
    coeff 2 serG = 196884 := by
  obtain ⟨-, h32, -, -, -, -⟩ := sigma_vals
  obtain ⟨-, d1, d2, d3⟩ := coeff_serD
  have hrel : serG * serP = serA ^ 3 := by
    rw [serG, mul_assoc, mul_comm (serP.invOfUnit 1),
      PowerSeries.mul_invOfUnit serP 1 (by simpa using constantCoeff_serP), mul_one]
  have hP0 : coeff 0 serP = 1 := by rw [serP, coeff_mk]; exact d1
  have hP1 : coeff 1 serP = -24 := by rw [serP, coeff_mk]; exact d2
  have hP2 : coeff 2 serP = 252 := by rw [serP, coeff_mk]; exact d3
  have hA0 : coeff 0 (serA ^ 3) = 1 := by
    simp [serA, eisCoeff, pow_succ, coeff_mul]
  have hA1 : coeff 1 (serA ^ 3) = 720 := by
    simp [serA, eisCoeff, pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  have hA2 : coeff 2 (serA ^ 3) = 179280 := by
    simp [serA, eisCoeff, pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_succ, h32]
  have e0 := congrArg (coeff 0) hrel
  have e1 := congrArg (coeff 1) hrel
  have e2 := congrArg (coeff 2) hrel
  rw [hA0] at e0
  rw [hA1] at e1
  rw [hA2] at e2
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, hP0, hP1, hP2] at e0 e1 e2
  refine ⟨?_, by omega, by omega⟩
  rw [coeff_zero_eq_constantCoeff_apply]
  omega

/-! ### The expansion -/

/-- **The integral `q`-expansion of the `j`-function.** For `τ` in the upper half-plane let
`q = e^{2πiτ}` (`Function.Periodic.qParam 1 τ`). There are integers `c₀, c₁, …` with
`c₀ = 196884` such that, for every `τ`, the series `∑ cₙ q^{n+1}` converges absolutely and

$$j(\tau) = \frac{1}{q} + 744 + \sum_{n \ge 0} c_n q^{n+1},$$

where `j = E₄³ / Δ` is `WLight.jFunction`. So `cₙ` is the coefficient of `q^{n+1}`; in the
source's indexing `a_{n+1} = cₙ`. That `j` is also `1728 g₂³ / (g₂³ - 27 g₃²)` for the
lattice `ℤ + ℤτ` is not proved here.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 19, Corollary 19.6, p. 3: "With q = e^{2πiτ} we have
j(τ) = 1/q + 744 + ∑_{n=1}^∞ aₙqⁿ, where the aₙ are integers", proved from Lemma 19.5; the
value `196884` of the first coefficient is in J. S. Milne, *Modular Functions and Modular Forms*,
version 1.31 (2017), Theorem 4.22. -/
theorem jFunction_qExpansion_int :
    ∃ c : ℕ → ℤ, c 0 = 196884 ∧ ∀ τ : ℍ,
      Summable (fun n : ℕ => ‖(c n : ℂ) * Function.Periodic.qParam 1 τ ^ (n + 1)‖) ∧
      jFunction τ = (Function.Periodic.qParam 1 τ)⁻¹ + 744 +
        ∑' n : ℕ, (c n : ℂ) * Function.Periodic.qParam 1 τ ^ (n + 1) := by
  obtain ⟨g0, g1, g2⟩ := coeff_serG
  refine ⟨fun n => coeff (n + 2) serG, g2, fun τ => ?_⟩
  set q := Function.Periodic.qParam 1 τ with hqdef
  have hq : ‖q‖ < 1 := norm_qParam_lt τ
  have hq0 : q ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hqn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq0
  have hP := fP_ne_zero q hq
  have hj : jFunction τ = fG q / q := by
    change ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ = _
    rw [E₄_eq, discriminant_eq, ← hqdef, ← mul_fP q hq, fG]
    field_simp
  have h1 := hasSum_tc diff_fG hq
  have h2 := (hasSum_nat_add_iff' 2).mpr h1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tc_fG, g0, g1, pow_zero, pow_one,
    zero_add, Int.cast_one, one_mul] at h2
  have h3 := h2.div_const q
  have hterm : ∀ n : ℕ, ((coeff (n + 2) serG : ℤ) : ℂ) * q ^ (n + 2) / q =
      ((coeff (n + 2) serG : ℤ) : ℂ) * q ^ (n + 1) := by
    intro n
    field_simp
    ring
  simp only [hterm] at h3
  have hsn : Summable fun n => ‖((coeff (n + 2) serG : ℤ) : ℂ) * q ^ (n + 1)‖ := by
    have hs := summable_tc diff_fG (norm_nonneg q) hq
    have hs' := ((summable_nat_add_iff 2).mpr hs).div_const ‖q‖
    refine hs'.congr fun n => ?_
    rw [tc_fG, norm_mul, norm_pow]
    field_simp
    ring
  refine ⟨hsn, ?_⟩
  rw [h3.tsum_eq, hj]
  field_simp
  push_cast
  ring

end WLight
