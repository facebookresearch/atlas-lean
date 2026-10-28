/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Recovering Dirichlet coefficients from vertical mean values at real points

For a Dirichlet series `L(a, s) = ∑ a n n^{-s}` and `σ` beyond the abscissa of absolute
convergence, the mean value of `L(a, σ + it) y^{σ + it}` over `t ∈ [-T, T]` tends to the
coefficient `a y` when `y` is a positive integer, and to `0` for every other real `y > 0`.
Expanding the series, the mean of `n^{-it} y^{it} = e^{i t log (y/n)}` is `1` if `n = y` and
tends to `0` otherwise; dominated convergence passes the limit through the sum.

## Main statements

* `LSeries.tendsto_mean_vertical_mul_cpow`: the coefficient-recovery formula
  `(1/2T) ∫_{-T}^{T} L(a, σ + it) y^{σ + it} dt → a y` (or `0`).
-/

open Filter Topology Complex

@[expose] public section

namespace LSeries

/-- On the line `Re s = σ`, the term `a n n^{-s} y^s` is `a n n^{-σ} y^σ e^{i t log (y/n)}`. -/
private lemma term_mul_cpow_vertical (a : ℕ → ℂ) (σ t y : ℝ) (hy : 0 < y) (n : ℕ) :
    term a ((σ : ℂ) + (t : ℂ) * I) n * (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)
      = term a σ n * (y : ℂ) ^ (σ : ℂ) *
        exp ((((Real.log y - Real.log n) * t : ℝ) : ℂ) * I) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero hn, term_of_ne_zero hn]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [cpow_add _ _ hn', cpow_add _ _ hy', cpow_def_of_ne_zero hn' ((t : ℂ) * I),
    cpow_def_of_ne_zero hy' ((t : ℂ) * I), ← natCast_log, ← ofReal_log hy.le]
  have h1 := exp_ne_zero (↑(Real.log ↑n) * (↑t * I))
  have h2 : (n : ℂ) ^ (σ : ℂ) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  have : exp ((((Real.log y - Real.log n) * t : ℝ) : ℂ) * I) *
      exp (↑(Real.log ↑n) * (↑t * I)) = exp (↑(Real.log y) * (↑t * I)) := by
    rw [← exp_add]; congr 1; push_cast; ring
  rw [← this]
  field_simp

/-- The mean of `t ↦ e^{i l t}` over `[-T, T]` has norm at most one. -/
private lemma norm_mean_exp_mul_I_le (l T : ℝ) (hT : 0 < T) :
    ‖(1 / (2 * T) : ℂ) * ∫ t in -T..T, exp (((l * t : ℝ) : ℂ) * I)‖ ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T) (C := 1)
    (f := fun t : ℝ => exp (((l * t : ℝ) : ℂ) * I))
    (fun x _ => by rw [norm_exp_ofReal_mul_I])
  rw [norm_mul]
  have h2 : ‖(1 / (2 * T) : ℂ)‖ = 1 / (2 * T) := by
    rw [norm_div, norm_one]; norm_cast; rw [Real.norm_of_nonneg (by positivity)]
  rw [h2]
  have h3 : |T - -T| = 2 * T := by rw [abs_of_pos (by linarith)]; ring
  rw [h3, one_mul] at h
  calc 1 / (2 * T) * _ ≤ 1 / (2 * T) * (2 * T) := by gcongr
    _ = 1 := by field_simp

/-- The mean of the constant `1 = e^{i 0 t}` over `[-T, T]` is `1`. -/
private lemma tendsto_mean_exp_zero :
    Tendsto (fun T : ℝ => (1 / (2 * T) : ℂ) *
      ∫ t in -T..T, exp ((((0 : ℝ) * t : ℝ) : ℂ) * I)) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  simp only [zero_mul, ofReal_zero, exp_zero, intervalIntegral.integral_const, real_smul,
    mul_one]
  have : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  push_cast
  field_simp
  norm_num

/-- For `l ≠ 0`, the mean of `t ↦ e^{i l t}` over `[-T, T]` tends to `0`. -/
private lemma tendsto_mean_exp_mul_I (l : ℝ) (hl : l ≠ 0) :
    Tendsto (fun T : ℝ => (1 / (2 * T) : ℂ) *
      ∫ t in -T..T, exp (((l * t : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  have hc : (l : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hl) I_ne_zero
  have hlim : Tendsto (fun T : ℝ => 1 / |l| * T⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (1 / |l|)
    rw [mul_zero] at this
    exact this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with T hT
  have he : ∀ t : ℝ, exp (((l * t : ℝ) : ℂ) * I) = exp ((l : ℂ) * I * (t : ℂ)) := fun t => by
    congr 1; push_cast; ring
  simp_rw [he]
  rw [integral_exp_mul_complex hc, norm_mul]
  have h2 : ‖(1 / (2 * T) : ℂ)‖ = 1 / (2 * T) := by
    rw [norm_div, norm_one]; norm_cast; rw [Real.norm_of_nonneg (by positivity)]
  have hn : ‖(l : ℂ) * I‖ = |l| := by simp
  have hnum : ‖exp ((l : ℂ) * I * (T : ℂ)) - exp ((l : ℂ) * I * ((-T : ℝ) : ℂ))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have e1 : ∀ u : ℝ, ‖exp ((l : ℂ) * I * (u : ℂ))‖ = 1 := fun u => by
      rw [show (l : ℂ) * I * (u : ℂ) = ((l * u : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I]
    rw [e1, e1]; norm_num
  rw [h2, norm_div, hn]
  have hl' : 0 < |l| := abs_pos.mpr hl
  calc 1 / (2 * T) * (_ / |l|) ≤ 1 / (2 * T) * (2 / |l|) := by gcongr
    _ = 1 / |l| * T⁻¹ := by field_simp

open Classical in
/-- **Coefficient recovery by vertical mean values.** For `σ` beyond the abscissa of absolute
convergence of `L(a, s) = ∑ a n n^{-s}` and real `y > 0`, the mean value
`(1/2T) ∫_{-T}^{T} L(a, σ + it) y^{σ + it} dt` tends to `a y` if `y` is a positive integer and
to `0` otherwise. -/
theorem tendsto_mean_vertical_mul_cpow (a : ℕ → ℂ) {σ : ℝ} (hσ : abscissaOfAbsConv a < σ)
    {y : ℝ} (hy : 0 < y) :
    Tendsto
      (fun T : ℝ => (1 / (2 * T)) * ∫ t in -T..T,
        LSeries a ((σ : ℂ) + (t : ℂ) * I) * (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I))
      atTop (𝓝 (if ∃ n : ℕ, 0 < n ∧ (n : ℝ) = y then a ⌊y⌋₊ else 0)) := by
  -- the mean of `e^{i l t}` over `[-T, T]`
  set M : ℝ → ℝ → ℂ := fun l T => (1 / (2 * T) : ℂ) *
    ∫ t in -T..T, exp (((l * t : ℝ) : ℂ) * I) with hM
  set g : ℕ → ℂ := fun n => term a σ n * (y : ℂ) ^ (σ : ℂ) with hg
  set L : ℕ → ℝ := fun n => Real.log y - Real.log n with hL
  have hsσ : LSeriesSummable a σ :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hσ)
  have hgs : Summable (fun n => ‖g n‖) := by
    simp only [hg, norm_mul]; exact hsσ.norm.mul_right _
  -- expansion of the mean as a series
  have hrepr : ∀ T : ℝ, (1 / (2 * T)) * ∫ t in -T..T,
      LSeries a ((σ : ℂ) + (t : ℂ) * I) * (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)
        = ∑' n, g n * M (L n) T := by
    intro T
    have hH := intervalIntegral.hasSum_integral_of_dominated_convergence (a := -T) (b := T)
      (μ := MeasureTheory.volume)
      (F := fun n t => g n * exp (((L n * t : ℝ) : ℂ) * I))
      (f := fun t => LSeries a ((σ : ℂ) + (t : ℂ) * I) * (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I))
      (fun n _ => ‖g n‖)
      (fun n => by
        apply Continuous.aestronglyMeasurable
        fun_prop)
      (fun n => Eventually.of_forall fun t _ => by
        rw [norm_mul, norm_exp_ofReal_mul_I, mul_one])
      (Eventually.of_forall fun t _ => hgs)
      intervalIntegrable_const
      (Eventually.of_forall fun t _ => by
        have hs : LSeriesSummable a ((σ : ℂ) + (t : ℂ) * I) :=
          LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hσ)
        have := hs.hasSum.mul_right ((y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I))
        have hfun : (fun n => g n * exp (((L n * t : ℝ) : ℂ) * I)) =
            fun n => term a ((σ : ℂ) + (t : ℂ) * I) n * (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) := by
          funext n
          simp only [hg, hL]
          rw [term_mul_cpow_vertical a σ t y hy n]
        rw [hfun]
        exact this)
    rw [← hH.tsum_eq, ← tsum_mul_left]
    congr 1
    funext n
    simp only [hM, intervalIntegral.integral_const_mul]
    ring
  have hlimit : Tendsto (fun T : ℝ => ∑' n, g n * M (L n) T) atTop
      (𝓝 (∑' n : ℕ, if (n : ℝ) = y then g n else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hgs (fun n => ?_) ?_
    · by_cases hny : (n : ℝ) = y
      · have hL0 : L n = 0 := by simp [hL, hny]
        simp only [hny, ite_true, hL0]
        have := tendsto_mean_exp_zero.const_mul (g n)
        rw [mul_one] at this
        exact this
      · simp only [hny, ite_false]
        rcases eq_or_ne n 0 with rfl | hn0
        · simp [hg]
        have hLn : L n ≠ 0 := by
          simp only [hL, sub_ne_zero]
          intro h
          apply hny
          have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
          exact (Real.log_injOn_pos (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr hnpos) h).symm
        have := (tendsto_mean_exp_mul_I (L n) hLn).const_mul (g n)
        rw [mul_zero] at this
        exact this
    · filter_upwards [eventually_gt_atTop 0] with T hT n
      rw [norm_mul]
      calc ‖g n‖ * ‖M (L n) T‖ ≤ ‖g n‖ * 1 := by
            gcongr; exact norm_mean_exp_mul_I_le (L n) T hT
        _ = ‖g n‖ := mul_one _
  simp_rw [hrepr]
  convert hlimit using 2
  split_ifs with hex
  · obtain ⟨n₀, hn₀, hn₀y⟩ := hex
    have hfl : ⌊y⌋₊ = n₀ := by rw [← hn₀y, Nat.floor_natCast]
    rw [hfl]
    have : (fun n : ℕ => if (n : ℝ) = y then g n else 0) =
        fun n => if n = n₀ then g n₀ else 0 := by
      funext n
      simp only [← hn₀y, Nat.cast_inj]
      split_ifs with h <;> simp [h]
    rw [this, tsum_ite_eq]
    simp only [hg]
    rw [term_of_ne_zero hn₀.ne', ← hn₀y]
    have hn₀C : ((n₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn₀.ne'
    have h2 : ((n₀ : ℝ) : ℂ) ^ (σ : ℂ) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
    push_cast at h2 ⊢
    field_simp
  · symm
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [ite_eq_right]
    intro h
    apply hex
    refine ⟨n, ?_, h⟩
    rcases Nat.eq_zero_or_pos n with rfl | h'
    · simp at h; linarith
    · exact h'

end LSeries
