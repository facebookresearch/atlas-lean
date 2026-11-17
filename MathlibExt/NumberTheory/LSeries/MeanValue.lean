/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Mean values of Dirichlet series on vertical lines

Let `f(s) = ∑ aₙ n⁻ˢ` converge absolutely on the line `re s = σ`. Integrating term by term,
`∫_{-T}^{T} u^{it} dt = 2T sinc(T log u)` shows that the averages
`(1 / 2T) ∫_{-T}^{T} (⋯) dt` pick out the "diagonal" terms as `T → ∞`. This recovers the
coefficients from the values on the line, and gives the mean square of `f` on the line.

## Main statements

* `Real.abs_sinc_le_inv_abs`, `Real.tendsto_sinc_mul_atTop_nhds_zero`: `sinc (T L) → 0`.
* `Complex.integral_ofReal_cpow_mul_I`: `∫_{-T}^{T} u^{it} dt = 2T sinc(T log u)`.
* `Complex.integral_tsum_mul_ofReal_cpow_mul_I`: the same, summed over an absolutely
  summable family.
* `LSeriesSummable.tendsto_integral_LSeries_mul_cpow_atTop`: for `m ≠ 0`,
  `(1 / 2T) ∫_{-T}^{T} f(σ + it) m^{σ + it} dt → aₘ`.
* `LSeriesSummable.tendsto_integral_norm_LSeries_sq_atTop`:
  `(1 / 2T) ∫_{-T}^{T} |f(σ + it)|² dt → ∑ |aₙ|² n^{-2σ}`.
-/

@[expose] public section

open Filter MeasureTheory Complex
open scoped Topology

namespace Real

/-- `|sinc x| ≤ |x|⁻¹` for `x ≠ 0`. -/
theorem abs_sinc_le_inv_abs {x : ℝ} (hx : x ≠ 0) : |sinc x| ≤ |x|⁻¹ := by
  have hx' : (0 : ℝ) < |x| := abs_pos.mpr hx
  rw [sinc_of_ne_zero hx, abs_div, div_le_iff₀ hx', inv_mul_cancel₀ hx'.ne']
  exact abs_sin_le_one x

/-- `sinc (T L) → 0` as `T → ∞`, for `L ≠ 0`. -/
theorem tendsto_sinc_mul_atTop_nhds_zero {L : ℝ} (hL : L ≠ 0) :
    Tendsto (fun T : ℝ => sinc (T * L)) atTop (𝓝 0) := by
  have hginv : Tendsto (fun T : ℝ => |L|⁻¹ * T⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (|L|⁻¹)
  refine squeeze_zero_norm' ?_ hginv
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  calc ‖sinc (T * L)‖ = |sinc (T * L)| := norm_eq_abs _
    _ ≤ |T * L|⁻¹ := abs_sinc_le_inv_abs (mul_ne_zero hT.ne' hL)
    _ = |L|⁻¹ * T⁻¹ := by rw [abs_mul, abs_of_pos hT, mul_inv]; ring

end Real

namespace Complex

/-- `x ^ (it) = exp (i t log x)` for a positive real base. -/
theorem ofReal_cpow_mul_I_eq_exp {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (x : ℂ) ^ ((t : ℂ) * I) = exp ((Real.log x : ℂ) * I * t) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← ofReal_log hx.le]
  ring_nf

theorem ofReal_cpow_mul_I_ne_zero {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (x : ℂ) ^ ((t : ℂ) * I) ≠ 0 := by
  rw [ofReal_cpow_mul_I_eq_exp hx t]
  exact exp_ne_zero _

/-- `x ^ (it)` has modulus one, so conjugation inverts it. -/
theorem conj_ofReal_cpow_mul_I {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (starRingEnd ℂ) ((x : ℂ) ^ ((t : ℂ) * I)) = ((x : ℂ) ^ ((t : ℂ) * I))⁻¹ := by
  rw [ofReal_cpow_mul_I_eq_exp hx t, ← exp_conj, ← exp_neg]
  congr 1
  simp [conj_I]

theorem continuous_ofReal_cpow_mul_I {x : ℝ} (hx : 0 < x) :
    Continuous fun t : ℝ => (x : ℂ) ^ ((t : ℂ) * I) := by
  simp only [ofReal_cpow_mul_I_eq_exp hx]
  fun_prop

/-- **The orthogonality integral.** For `u > 0` and `T > 0`,
`∫_{-T}^{T} u ^ (it) dt = 2 T sinc (T log u)`. -/
theorem integral_ofReal_cpow_mul_I {u T : ℝ} (hu : 0 < u) (hT : 0 < T) :
    (∫ t in (-T)..T, (u : ℂ) ^ ((t : ℂ) * I)) =
      ((2 * T * Real.sinc (T * Real.log u) : ℝ) : ℂ) := by
  have hrw := ofReal_cpow_mul_I_eq_exp hu
  by_cases hL : Real.log u = 0
  · simp only [hrw, hL, ofReal_zero, zero_mul, exp_zero, intervalIntegral.integral_const,
      mul_zero, Real.sinc_zero, mul_one, real_smul]
    push_cast
    ring
  · have hcne : ((Real.log u : ℝ) : ℂ) * I ≠ 0 :=
      mul_ne_zero (ofReal_ne_zero.mpr hL) I_ne_zero
    have hTc : ((T : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hT.ne'
    have hLc : ((Real.log u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hL
    simp only [hrw]
    rw [integral_exp_mul_complex hcne, Real.sinc_of_ne_zero (mul_ne_zero hT.ne' hL)]
    push_cast
    rw [show ((Real.log u : ℝ) : ℂ) * I * (T : ℂ)
          = (((T : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ)) * I by ring,
      show ((Real.log u : ℝ) : ℂ) * I * (-(T : ℂ))
          = (-(((T : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ))) * I by ring,
      exp_mul_I, exp_mul_I, cos_neg, sin_neg]
    field_simp
    ring

/-- **The orthogonality integral for an absolutely summable family.** For a countable family
with `∑ ‖gᵢ‖ < ∞` and positive bases `uᵢ`,
`∫_{-T}^{T} ∑ᵢ gᵢ uᵢ ^ (it) dt = ∑ᵢ gᵢ · 2 T sinc (T log uᵢ)`. -/
theorem integral_tsum_mul_ofReal_cpow_mul_I {ι : Type*} [Countable ι] {g : ι → ℂ}
    {u : ι → ℝ} (hu : ∀ i, 0 < u i) (hg : Summable fun i => ‖g i‖) {T : ℝ} (hT : 0 < T) :
    ∫ t in (-T)..T, ∑' i, g i * ((u i : ℝ) : ℂ) ^ ((t : ℂ) * I)
      = ∑' i, g i * ((2 * T * Real.sinc (T * Real.log (u i)) : ℝ) : ℂ) := by
  have hTle : -T ≤ T := by linarith
  have hcont : ∀ i, Continuous fun t : ℝ => g i * ((u i : ℝ) : ℂ) ^ ((t : ℂ) * I) :=
    fun i => continuous_const.mul (continuous_ofReal_cpow_mul_I (hu i))
  have hIint : ∀ i, IntegrableOn
      (fun t : ℝ => g i * ((u i : ℝ) : ℂ) ^ ((t : ℂ) * I)) (Set.Ioc (-T) T) :=
    fun i => (intervalIntegrable_iff_integrableOn_Ioc_of_le hTle).mp
      ((hcont i).intervalIntegrable (-T) T)
  have hnorm : ∀ i (t : ℝ), ‖g i * ((u i : ℝ) : ℂ) ^ ((t : ℂ) * I)‖ = ‖g i‖ := by
    intro i t
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hu i)]
    simp
  have hIsum : Summable fun i =>
      ∫ t in Set.Ioc (-T) T, ‖g i * ((u i : ℝ) : ℂ) ^ ((t : ℂ) * I)‖ := by
    have h2 : ∀ i, (∫ t in Set.Ioc (-T) T, ‖g i * ((u i : ℝ) : ℂ) ^ ((t : ℂ) * I)‖)
        = 2 * T * ‖g i‖ := by
      intro i
      simp only [hnorm i]
      rw [setIntegral_const, Real.volume_real_Ioc_of_le hTle, smul_eq_mul]
      ring
    simp only [h2]
    exact hg.mul_left _
  have hI : ∀ i, (∫ t in Set.Ioc (-T) T, g i * ((u i : ℝ) : ℂ) ^ ((t : ℂ) * I))
      = g i * ((2 * T * Real.sinc (T * Real.log (u i)) : ℝ) : ℂ) := by
    intro i
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hTle,
      integral_ofReal_cpow_mul_I (hu i) hT]
  rw [intervalIntegral.integral_of_le hTle, ← integral_tsum_of_summable_integral_norm hIint hIsum]
  exact tsum_congr hI

end Complex

/-- The complex-valued form of `Real.tendsto_sinc_mul_atTop_nhds_zero`. -/
private theorem tendsto_ofReal_sinc_mul_atTop_nhds_zero {L : ℝ} (hL : L ≠ 0) :
    Tendsto (fun T : ℝ => ((Real.sinc (T * L) : ℝ) : ℂ)) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    (continuous_ofReal.tendsto 0).comp (Real.tendsto_sinc_mul_atTop_nhds_zero hL)

namespace LSeriesSummable

variable {a : ℕ → ℂ} {σ : ℝ}

/-- **Recovering a coefficient from a Dirichlet series.** If `f(s) = ∑ aₙ n⁻ˢ` converges
absolutely on the line `re s = σ`, then for every `m ≠ 0`,
`(1 / 2T) ∫_{-T}^{T} f(σ + it) m^{σ + it} dt → aₘ` as `T → ∞`. -/
theorem tendsto_integral_LSeries_mul_cpow_atTop (ha : LSeriesSummable a σ) {m : ℕ}
    (hm : m ≠ 0) :
    Tendsto
      (fun T : ℝ => (1 / (2 * (T : ℂ))) *
        ∫ t in (-T)..T, LSeries a (σ + t * I) * (m : ℂ) ^ ((σ : ℂ) + t * I))
      atTop (𝓝 (a m)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have ha' : Summable (LSeries.term a (σ : ℂ)) := ha
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ n, u n = if n = 0 then 1 else (m : ℝ) / (n : ℝ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ → ℂ, ∀ n, C n = LSeries.term a (σ : ℂ) n * (m : ℂ) ^ (σ : ℂ) :=
    ⟨_, fun _ => rfl⟩
  have hupos : ∀ n, 0 < u n := by
    intro n
    rw [hu]
    split_ifs with h
    · norm_num
    · exact div_pos hm0 (by exact_mod_cast Nat.pos_of_ne_zero h)
  have hC0 : C 0 = 0 := by rw [hC]; simp
  have hCm : C m = a m := by
    have hne : (m : ℂ) ^ (σ : ℂ) ≠ 0 := fun h =>
      (Nat.cast_ne_zero.mpr hm) ((cpow_eq_zero_iff _ _).mp h).1
    rw [hC, LSeries.term_of_ne_zero hm a (σ : ℂ)]
    field_simp
  have hCsum : Summable fun n => ‖C n‖ := by
    have h1 : ∀ n, ‖C n‖ = ‖LSeries.term a (σ : ℂ) n‖ * ‖(m : ℂ) ^ (σ : ℂ)‖ := by
      intro n; rw [hC, norm_mul]
    simp only [h1]
    exact ha'.norm.mul_right _
  -- The integrand, split term by term: `a n / n ^ s * m ^ s = C n * (m / n) ^ (i t)`.
  have hterm : ∀ (n : ℕ) (t : ℝ),
      LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n * (m : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)
        = C n * ((u n : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
    intro n t
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hC0]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hun : u n = (m : ℝ) / (n : ℝ) := by rw [hu, ite_eq_right hn]
      have hune : ((u n : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hupos n).ne'
      have h1 : ∀ s : ℂ, (m : ℂ) ^ s / (n : ℂ) ^ s = ((u n : ℝ) : ℂ) ^ s := by
        intro s
        rw [hun, ofReal_div, div_cpow_ofReal_nonneg hm0.le hn0.le]
        push_cast
        ring
      rw [hC, LSeries.term_of_ne_zero hn a ((σ : ℂ) + (t : ℂ) * I),
        LSeries.term_of_ne_zero hn a (σ : ℂ),
        show a n / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) * (m : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)
            = a n * ((m : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) /
              (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)) from by ring,
        show a n / (n : ℂ) ^ (σ : ℂ) * (m : ℂ) ^ (σ : ℂ) * ((u n : ℝ) : ℂ) ^ ((t : ℂ) * I)
            = a n * (((m : ℂ) ^ (σ : ℂ) / (n : ℂ) ^ (σ : ℂ)) *
              ((u n : ℝ) : ℂ) ^ ((t : ℂ) * I)) from by ring,
        h1, h1, ← cpow_add _ _ hune]
  -- The mean value over `[-T, T]`, evaluated by the orthogonality integral.
  have key : ∀ T : ℝ, 0 < T →
      (1 / (2 * (T : ℂ))) * (∫ t in (-T)..T, LSeries a ((σ : ℂ) + (t : ℂ) * I) *
          (m : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I))
        = ∑' n : ℕ, C n * ((Real.sinc (T * Real.log (u n)) : ℝ) : ℂ) := by
    intro T hT
    have hTne : (T : ℂ) ≠ 0 := ofReal_ne_zero.mpr hT.ne'
    have hsplit : ∀ t : ℝ, LSeries a ((σ : ℂ) + (t : ℂ) * I) *
        (m : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)
          = ∑' n : ℕ, C n * ((u n : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
      intro t
      simp only [LSeries]
      rw [← tsum_mul_right]
      exact tsum_congr fun n => hterm n t
    simp only [hsplit]
    rw [integral_tsum_mul_ofReal_cpow_mul_I hupos hCsum hT, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    push_cast
    field_simp
  -- Tannery's theorem: `sinc (T log (m / n)) → 0` for `n ≠ m`, and `= 1` for `n = m`.
  have hlim : Tendsto (fun T : ℝ => ∑' n : ℕ, C n * ((Real.sinc (T * Real.log (u n)) : ℝ) : ℂ))
      atTop (𝓝 (∑' n : ℕ, if n = m then a m else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hCsum ?_ ?_
    · intro n
      by_cases hnm : n = m
      · have hn0 : n ≠ 0 := hnm ▸ hm
        have hu1 : u n = 1 := by rw [hu, ite_eq_right hn0, hnm]; exact div_self hm0.ne'
        have hval : ∀ T : ℝ, C n * ((Real.sinc (T * Real.log (u n)) : ℝ) : ℂ) = a m := by
          intro T
          rw [hu1, Real.log_one, mul_zero, Real.sinc_zero, ofReal_one, mul_one, hnm, hCm]
        simp only [hval, ite_eq_left hnm]
        exact tendsto_const_nhds
      · simp only [ite_eq_right hnm]
        rcases eq_or_ne n 0 with rfl | hn0
        · simp only [hC0, zero_mul]
          exact tendsto_const_nhds
        · have hun : u n = (m : ℝ) / (n : ℝ) := by rw [hu, ite_eq_right hn0]
          have hune : u n ≠ 1 := by
            rw [hun]
            intro h
            have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
            have hmn : (m : ℝ) = (n : ℝ) := by field_simp at h; linarith
            exact hnm (by exact_mod_cast hmn.symm)
          have hL : Real.log (u n) ≠ 0 := fun h =>
            hune (by rw [← Real.exp_log (hupos n), h, Real.exp_zero])
          simpa using (tendsto_ofReal_sinc_mul_atTop_nhds_zero hL).const_mul (C n)
    · refine Eventually.of_forall fun T n => ?_
      have h1 : ‖((Real.sinc (T * Real.log (u n)) : ℝ) : ℂ)‖ ≤ 1 := by
        simpa using Real.abs_sinc_le_one (T * Real.log (u n))
      calc ‖C n * ((Real.sinc (T * Real.log (u n)) : ℝ) : ℂ)‖
          = ‖C n‖ * ‖((Real.sinc (T * Real.log (u n)) : ℝ) : ℂ)‖ := norm_mul _ _
        _ ≤ ‖C n‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = ‖C n‖ := mul_one _
  rw [tsum_ite_eq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact (key T hT).symm

/-- **The mean square of a Dirichlet series on a vertical line.** If `f(s) = ∑ aₙ n⁻ˢ`
converges absolutely on the line `re s = σ`, then
`(1 / 2T) ∫_{-T}^{T} |f(σ + it)|² dt → ∑ |aₙ|² n^{-2σ}` as `T → ∞`. -/
theorem tendsto_integral_norm_LSeries_sq_atTop (ha : LSeriesSummable a σ) :
    Tendsto
      (fun T : ℝ => (1 / (2 * T)) * ∫ t in (-T)..T, ‖LSeries a (σ + t * I)‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, ‖LSeries.term a σ n‖ ^ 2)) := by
  have ha' : Summable (LSeries.term a (σ : ℂ)) := ha
  obtain ⟨c, hcd⟩ : ∃ c : ℕ → ℂ, c = LSeries.term a (σ : ℂ) := ⟨_, rfl⟩
  have hc0 : c 0 = 0 := by rw [hcd]; exact LSeries.term_zero _ _
  have hcsum : Summable fun n : ℕ => ‖c n‖ := by rw [hcd]; exact ha'.norm
  -- `w n = n`, with the harmless value `1` at `n = 0`, so that all bases are positive.
  obtain ⟨w, hwd⟩ : ∃ w : ℕ → ℝ, ∀ n, w n = if n = 0 then 1 else (n : ℝ) := ⟨_, fun _ => rfl⟩
  have hwpos : ∀ n, 0 < w n := by
    intro n
    rw [hwd]
    split_ifs with h
    · norm_num
    · exact_mod_cast Nat.pos_of_ne_zero h
  -- The terms of the Dirichlet series on the line `re s = σ`.
  have hterm : ∀ (t : ℝ) (n : ℕ),
      LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n = c n * (((w n : ℝ) : ℂ) ^ ((t : ℂ) * I))⁻¹ := by
    intro t n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero, hc0, zero_mul]
    · have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hwn : ((w n : ℝ) : ℂ) = (n : ℂ) := by rw [hwd, ite_eq_right hn]; push_cast; ring
      rw [hcd, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, hwn,
        cpow_add _ _ hne, div_mul_eq_div_div, div_eq_mul_inv]
  have hnormterm : ∀ (t : ℝ) (n : ℕ), ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n‖ = ‖c n‖ := by
    intro t n
    rw [hterm t n, norm_mul, norm_inv, norm_cpow_eq_rpow_re_of_pos (hwpos n)]
    simp
  -- The double-series data: `g (m, n) = c m * conj (c n)` and `u (m, n) = n / m`.
  obtain ⟨g, hgd⟩ : ∃ g : ℕ × ℕ → ℂ, ∀ p, g p = c p.1 * (starRingEnd ℂ) (c p.2) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨u, hud⟩ : ∃ u : ℕ × ℕ → ℝ, ∀ p, u p = w p.2 / w p.1 := ⟨_, fun _ => rfl⟩
  have hupos : ∀ p, 0 < u p := fun p => by rw [hud]; exact div_pos (hwpos _) (hwpos _)
  have hgnorm : ∀ p, ‖g p‖ = ‖c p.1‖ * ‖c p.2‖ := by
    intro p; rw [hgd, norm_mul, RCLike.norm_conj]
  have hgsum : Summable fun p : ℕ × ℕ => ‖g p‖ := by
    simp only [hgnorm]
    exact hcsum.mul_of_nonneg hcsum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  -- The product of a term and a conjugated term.
  have hprod : ∀ (t : ℝ) (m n : ℕ),
      LSeries.term a ((σ : ℂ) + (t : ℂ) * I) m *
          (starRingEnd ℂ) (LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n)
        = g (m, n) * ((u (m, n) : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
    intro t m n
    have hXm := ofReal_cpow_mul_I_ne_zero (hwpos m) t
    have hXn := ofReal_cpow_mul_I_ne_zero (hwpos n) t
    rw [hterm t m, hterm t n, map_mul, map_inv₀, conj_ofReal_cpow_mul_I (hwpos n) t, inv_inv,
      hgd, hud, ofReal_div, div_cpow_ofReal_nonneg (hwpos n).le (hwpos m).le]
    field_simp
  -- Pointwise expansion of `|f (σ + i t)| ^ 2` as a double series.
  have hsq : ∀ t : ℝ, ((‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ)
      = ∑' p : ℕ × ℕ, g p * ((u p : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
    intro t
    have hns : Summable fun n : ℕ => ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n‖ := by
      simpa only [hnormterm t] using hcsum
    have hnc : Summable fun n : ℕ =>
        ‖(starRingEnd ℂ) (LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n)‖ := by
      simpa only [RCLike.norm_conj] using hns
    have hcj : HasSum (fun n : ℕ => (starRingEnd ℂ) (LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n))
        ((starRingEnd ℂ) (LSeries a ((σ : ℂ) + (t : ℂ) * I))) := by
      have := hns.of_norm.hasSum.map (starRingEnd ℂ).toAddMonoidHom continuous_conj
      simpa [LSeries, Function.comp_def] using this
    have h1 : ((‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ)
        = LSeries a ((σ : ℂ) + (t : ℂ) * I) *
            (starRingEnd ℂ) (LSeries a ((σ : ℂ) + (t : ℂ) * I)) := by
      rw [mul_conj]
      norm_cast
      rw [normSq_eq_norm_sq]
    rw [h1, ← hcj.tsum_eq]
    conv_lhs => rw [LSeries]
    rw [tsum_mul_tsum_of_summable_norm hns hnc]
    exact tsum_congr fun p => hprod t p.1 p.2
  -- The mean value over `[-T, T]`, evaluated by the orthogonality integral.
  have key : ∀ T : ℝ, 0 < T →
      (((1 / (2 * T)) * ∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ)
        = ∑' p : ℕ × ℕ, g p * ((Real.sinc (T * Real.log (u p)) : ℝ) : ℂ) := by
    intro T hT
    have hTne : (T : ℂ) ≠ 0 := ofReal_ne_zero.mpr hT.ne'
    have hmain : ((∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ)
          = ∑' p : ℕ × ℕ, g p * ((2 * T * Real.sinc (T * Real.log (u p)) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
        ∑' p : ℕ × ℕ, g p * ((u p : ℝ) : ℂ) ^ ((t : ℂ) * I)) (fun t _ => hsq t)]
      exact integral_tsum_mul_ofReal_cpow_mul_I hupos hgsum hT
    rw [ofReal_mul, hmain, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    push_cast
    field_simp
  -- Tannery's theorem: the off-diagonal terms die.
  have hlim : Tendsto
      (fun T : ℝ => ∑' p : ℕ × ℕ, g p * ((Real.sinc (T * Real.log (u p)) : ℝ) : ℂ))
      atTop (𝓝 (∑' p : ℕ × ℕ, if p.1 = p.2 then g p else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hgsum ?_ ?_
    · rintro ⟨m, n⟩
      by_cases hmn : m = n
      · subst hmn
        have hu1 : u (m, m) = 1 := by rw [hud]; exact div_self (hwpos m).ne'
        simp only [hu1, Real.log_one, mul_zero, Real.sinc_zero, ofReal_one, mul_one]
        exact tendsto_const_nhds
      · simp only [ite_eq_right hmn]
        by_cases hz : m = 0 ∨ n = 0
        · have hgz : g (m, n) = 0 := by
            rcases hz with h | h <;> simp [hgd, h, hc0]
          simp only [hgz, zero_mul]
          exact tendsto_const_nhds
        · rw [not_or] at hz
          have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hz.1
          have hwm : w m = (m : ℝ) := by rw [hwd, ite_eq_right hz.1]
          have hwn : w n = (n : ℝ) := by rw [hwd, ite_eq_right hz.2]
          have hune : u (m, n) ≠ 1 := by
            rw [hud, hwm, hwn]
            intro h
            have hnm : (n : ℝ) = (m : ℝ) := by field_simp at h; linarith
            exact hmn (by exact_mod_cast hnm.symm)
          have hL : Real.log (u (m, n)) ≠ 0 := fun h =>
            hune (by rw [← Real.exp_log (hupos (m, n)), h, Real.exp_zero])
          simpa using (tendsto_ofReal_sinc_mul_atTop_nhds_zero hL).const_mul (g (m, n))
    · refine Eventually.of_forall fun T p => ?_
      have h1 : ‖((Real.sinc (T * Real.log (u p)) : ℝ) : ℂ)‖ ≤ 1 := by
        simpa using Real.abs_sinc_le_one (T * Real.log (u p))
      calc ‖g p * ((Real.sinc (T * Real.log (u p)) : ℝ) : ℂ)‖
          = ‖g p‖ * ‖((Real.sinc (T * Real.log (u p)) : ℝ) : ℂ)‖ := norm_mul _ _
        _ ≤ ‖g p‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = ‖g p‖ := mul_one _
  -- The surviving diagonal is `∑ ‖c n‖ ^ 2`.
  have hinj : Function.Injective (fun n : ℕ => (n, n)) := by
    intro x y h
    exact (Prod.mk.injEq _ _ _ _ ▸ h : x = y ∧ x = y).1
  have hsq2 : Summable fun n : ℕ => ‖c n‖ ^ 2 := by
    have h := (hcsum.mul_of_nonneg hcsum (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)).comp_injective hinj
    simpa [Function.comp_def, sq] using h
  have hdiag : (∑' p : ℕ × ℕ, if p.1 = p.2 then g p else 0)
      = ((∑' n : ℕ, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
    have hd : HasSum (fun n : ℕ => ((‖c n‖ ^ 2 : ℝ) : ℂ)) ((∑' n : ℕ, ‖c n‖ ^ 2 : ℝ) : ℂ) :=
      ofRealCLM.hasSum hsq2.hasSum
    have heq : ((fun p : ℕ × ℕ => if p.1 = p.2 then g p else 0) ∘ fun n : ℕ => (n, n))
        = fun n : ℕ => ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
      funext n
      change (if n = n then g (n, n) else 0) = ((‖c n‖ ^ 2 : ℝ) : ℂ)
      rw [ite_eq_left rfl, hgd, mul_conj, normSq_eq_norm_sq]
    have hcomp : HasSum ((fun p : ℕ × ℕ => if p.1 = p.2 then g p else 0) ∘ fun n : ℕ => (n, n))
        ((∑' n : ℕ, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
      rw [heq]; exact hd
    have hzero : ∀ p : ℕ × ℕ, p ∉ Set.range (fun n : ℕ => (n, n)) →
        (if p.1 = p.2 then g p else 0) = 0 := by
      rintro ⟨m, n⟩ hp
      have hmn : m ≠ n := by rintro rfl; exact hp ⟨m, rfl⟩
      simp [hmn]
    exact ((hinj.hasSum_iff hzero).mp hcomp).tsum_eq
  -- Assemble: take the limit in `ℂ` and read off the real part.
  have hlim' : Tendsto
      (fun T : ℝ => (((1 / (2 * T)) * ∫ t in (-T)..T,
        ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ))
      atTop (𝓝 ((∑' n : ℕ, ‖c n‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← hdiag]
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (key T hT).symm
  have hre := (continuous_re.tendsto _).comp hlim'
  simp only [Function.comp_def, ofReal_re] at hre
  rw [hcd] at hre
  exact hre

end LSeriesSummable
