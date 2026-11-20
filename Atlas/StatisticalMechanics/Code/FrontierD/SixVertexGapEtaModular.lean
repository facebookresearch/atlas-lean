/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexGapEulerLogs
import Mathlib.NumberTheory.ModularForms.Discriminant

open Filter Topology Complex UpperHalfPlane
open scoped Real ModularForm

namespace StatMech.FrontierD

noncomputable section

private def etaImaginaryPoint (t : ℝ) (ht : 0 < t) : UpperHalfPlane :=
  ⟨Complex.I * t, by simpa using ht⟩

private theorem etaImaginaryPoint_coe (t : ℝ) (ht : 0 < t) :
    ((etaImaginaryPoint t ht : UpperHalfPlane) : ℂ) = Complex.I * t := rfl



theorem eta_imaginary_pow_twentyFour {t : ℝ} (ht : 0 < t) :
    ModularForm.eta (Complex.I * t) ^ 24 =
      (Real.exp (24 * (sixVertexEulerLog t - Real.pi * t / 12)) : ℝ) := by
  let f : ℕ → ℝ := fun n =>
    1 - Real.exp (-2 * Real.pi * t * (n + 1 : ℝ))
  have hfpos : ∀ n, 0 < f n := by
    intro n
    dsimp [f]
    rw [sub_pos, Real.exp_lt_one_iff]
    have hn : 0 < (n + 1 : ℝ) := by positivity
    have hp : 0 < 2 * Real.pi * t * (n + 1 : ℝ) := by positivity
    nlinarith
  have hflog : Summable (fun n => Real.log (f n)) := by
    simpa [f] using summable_sixVertexEulerLog ht
  have hfmul : Multipliable f := Real.multipliable_of_summable_log hfpos hflog
  have hfprod : (∏' n, f n) = Real.exp (sixVertexEulerLog t) := by
    symm
    simpa [sixVertexEulerLog, f] using Real.rexp_tsum_eq_tprod hfpos hflog
  let z := etaImaginaryPoint t ht
  have hdisc := ModularForm.discriminant_eq_q_prod z
  change ModularForm.eta (Complex.I * t) ^ 24 =
    Function.Periodic.qParam 1 (Complex.I * t) *
      ∏' n : ℕ, (1 - ModularForm.eta_q n (Complex.I * t)) ^ 24 at hdisc
  rw [hdisc]
  have hq : Function.Periodic.qParam 1 (Complex.I * t) =
      (Real.exp (-2 * Real.pi * t) : ℝ) := by
    rw [Function.Periodic.qParam]
    have hexp : 2 * (↑Real.pi : ℂ) * Complex.I * (Complex.I * t) / 1 =
        ((-2 * Real.pi * t : ℝ) : ℂ) := by
      calc
        2 * (↑Real.pi : ℂ) * Complex.I * (Complex.I * ↑t) / 1 =
            2 * (↑Real.pi : ℂ) * (Complex.I * Complex.I) * ↑t := by ring
        _ = (-2 : ℂ) * ↑Real.pi * ↑t := by
          rw [Complex.I_mul_I]
          ring
        _ = ((-2 * Real.pi * t : ℝ) : ℂ) := by norm_num
    simp only [Complex.ofReal_one, div_one]
    have hexp' : 2 * (↑Real.pi : ℂ) * Complex.I * (Complex.I * t) =
        ((-2 * Real.pi * t : ℝ) : ℂ) := by simpa using hexp
    rw [hexp']
    exact (Complex.ofReal_exp _).symm
  rw [hq]
  have hterm : ∀ n : ℕ,
      (1 - ModularForm.eta_q n (Complex.I * t)) ^ 24 =
        ((f n ^ 24 : ℝ) : ℂ) := by
    intro n
    have hqn : ModularForm.eta_q n (Complex.I * t) =
        (Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)) : ℝ) := by
      rw [ModularForm.eta_q_eq_cexp]
      have hexp : 2 * (↑Real.pi : ℂ) * Complex.I * (n + 1) * (Complex.I * t) =
          ((-2 * Real.pi * t * (n + 1 : ℝ) : ℝ) : ℂ) := by
        calc
          2 * (↑Real.pi : ℂ) * Complex.I * (↑n + 1) *
                (Complex.I * ↑t) =
              2 * (↑Real.pi : ℂ) * (Complex.I * Complex.I) *
                ↑t * (↑n + 1) := by ring
          _ = (-2 : ℂ) * ↑Real.pi * ↑t * (↑n + 1) := by
            rw [Complex.I_mul_I]
            ring
          _ = ((-2 * Real.pi * t * (n + 1 : ℝ) : ℝ) : ℂ) := by norm_num
      rw [hexp]
      exact (Complex.ofReal_exp _).symm
    rw [hqn]
    simp [f]
  rw [tprod_congr hterm]
  have hmap := (hfmul.pow 24).map_tprod Complex.ofRealHom Complex.continuous_ofReal
  change ((∏' n, f n ^ 24 : ℝ) : ℂ) =
      ∏' n, ((f n ^ 24 : ℝ) : ℂ) at hmap
  rw [← hmap, hfmul.tprod_pow, hfprod]
  norm_cast
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  norm_num
  ring



theorem eta_imaginary_recip_pow_twentyFour {t : ℝ} (ht : 0 < t) :
    ModularForm.eta (Complex.I * (1 / t : ℝ)) ^ 24 =
      (t : ℂ) ^ 12 * ModularForm.eta (Complex.I * t) ^ 24 := by
  let z := etaImaginaryPoint t ht
  have h := congrFun ModularForm.discriminant_S_invariant z
  rw [ModularForm.SL_slash_apply, UpperHalfPlane.modular_S_smul] at h
  simp [UpperHalfPlane.denom, ModularGroup.S] at h
  change ModularForm.eta (-((z : ℂ))⁻¹) ^ 24 * ((((z : ℂ) ^ 12))⁻¹) =
    ModularForm.eta z ^ 24 at h
  field_simp [z.ne_zero] at h
  have hinv : -((1 : ℂ) / (Complex.I * (t : ℂ))) =
      Complex.I * ((1 / t : ℝ) : ℂ) := by
    field_simp [Complex.I_ne_zero, ht.ne']
    rw [show Complex.I ^ 2 = (-1 : ℂ) by norm_num]
    norm_cast
    field_simp
  have hpow : (Complex.I * (t : ℂ)) ^ 12 = (t : ℂ) ^ 12 := by
    rw [mul_pow, show (12 : ℕ) = 4 * 3 by omega, pow_mul,
      Complex.I_pow_four, one_pow, one_mul]
  change ModularForm.eta (-((1 : ℂ) / (Complex.I * (t : ℂ)))) ^ 24 =
    (Complex.I * (t : ℂ)) ^ 12 * ModularForm.eta (Complex.I * t) ^ 24 at h
  rw [hinv, hpow] at h
  exact h


theorem sixVertexEulerLog_reciprocal {t : ℝ} (ht : 0 < t) :
    sixVertexEulerLog (1 / t) =
      sixVertexEulerLog t + Real.log t / 2 +
        Real.pi / 12 * (1 / t - t) := by
  have htinv : 0 < 1 / t := one_div_pos.mpr ht
  have hS := eta_imaginary_recip_pow_twentyFour ht
  rw [eta_imaginary_pow_twentyFour htinv,
    eta_imaginary_pow_twentyFour ht] at hS
  norm_cast at hS
  have htpow : t ^ 12 = Real.exp (12 * Real.log t) := by
    calc
      t ^ 12 = Real.exp (Real.log t) ^ 12 := by rw [Real.exp_log ht]
      _ = Real.exp ((12 : ℕ) * Real.log t) := (Real.exp_nat_mul _ 12).symm
      _ = Real.exp (12 * Real.log t) := by norm_num
  rw [htpow, ← Real.exp_add] at hS
  have hexp := Real.exp_injective hS
  field_simp [ht.ne'] at hexp ⊢
  nlinarith



theorem sixVertexOddEulerRatioLog_reciprocal_four {t : ℝ} (ht : 0 < t) :
    sixVertexOddEulerRatioLog (1 / (4 * t)) =
      sixVertexAlternatingPlusEulerLog t + Real.pi * t / 4 - Real.log 2 / 2 := by
  have ht2 : 0 < 2 * t := by positivity
  have ht4 : 0 < 4 * t := by positivity
  have hu : 0 < 1 / (4 * t) := one_div_pos.mpr ht4
  have h1 := sixVertexEulerLog_reciprocal ht
  have h2 := sixVertexEulerLog_reciprocal ht2
  have h4 := sixVertexEulerLog_reciprocal ht4
  have harg2 : 2 * (1 / (4 * t)) = 1 / (2 * t) := by
    field_simp [ht.ne']
    ring
  have harg4 : 4 * (1 / (4 * t)) = 1 / t := by
    field_simp [ht.ne']
  have hlog2t : Real.log (2 * t) = Real.log 2 + Real.log t := by
    exact Real.log_mul (by norm_num) ht.ne'
  have hlog4t : Real.log (4 * t) =
      Real.log 2 + Real.log 2 + Real.log t := by
    calc
      Real.log (4 * t) = Real.log (2 * (2 * t)) := by ring_nf
      _ = Real.log 2 + Real.log (2 * t) :=
        Real.log_mul (by norm_num) (mul_ne_zero (by norm_num) ht.ne')
      _ = Real.log 2 + Real.log 2 + Real.log t := by rw [hlog2t]; ring
  rw [sixVertexOddEulerRatioLog_eq_euler hu, harg2, harg4,
    h2, h4, h1, hlog2t, hlog4t,
    sixVertexAlternatingPlusEulerLog_eq_euler ht]
  field_simp [ht.ne']
  ring



theorem sixVertexAntiferroelectricGapRate_eq_dualGapRate
    {lam : ℝ} (hlam : 0 < lam) :
    sixVertexAntiferroelectricGapRate lam = sixVertexDualGapRate lam := by
  let t : ℝ := lam / Real.pi
  have ht : 0 < t := div_pos hlam Real.pi_pos
  let u : ℝ := 1 / (4 * t)
  have hu : 0 < u := one_div_pos.mpr (by positivity)
  have harg : Real.exp (-(Real.pi ^ 2) / (2 * lam)) =
      Real.exp (-2 * Real.pi * u) := by
    congr 1
    dsimp [u, t]
    field_simp [hlam.ne', Real.pi_ne_zero]
    norm_num
  have hA : sixVertexGapAlternatingLogSeries lam =
      sixVertexAlternatingPlusEulerLog t := by
    rw [sixVertexGapAlternatingLogSeries_eq_euler hlam,
      sixVertexAlternatingPlusEulerLog_eq_euler ht]
  rw [sixVertexAntiferroelectricGapRate_eq_logProduct hlam, hA,
    sixVertexDualGapRate, harg,
    sixVertexDualGapPowerSeries_exp_eq_oddEuler u,
    sixVertexOddEulerRatioLog_reciprocal_four ht]
  dsimp [t]
  field_simp [Real.pi_ne_zero]
  ring

end

end StatMech.FrontierD
