/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.IdentDistrib

import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Probability.Independence.Integration

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal NNReal

namespace MathlibExt.Probability.LawIteratedLogarithmWanted

/-!
# Law of the iterated logarithm

This file proves the Hartman–Wintner law of the iterated logarithm for i.i.d. real random variables.
-/

private lemma lil_integral_sq_eq_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hMeas : Measurable (X 0))
    (hMean : μ[X 0] = 0) (hVar : Var[X 0; μ] = 1) :
    μ[fun ω ↦ X 0 ω ^ 2] = 1 := by
  rw [← hVar, variance_eq_integral hMeas.aemeasurable, hMean]
  simp

private noncomputable def lilLog (n : ℕ) : ℝ :=
  max 1 (Real.log (Real.log ((n ⊔ 3 : ℕ) : ℝ)))

private noncomputable def lilScale (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) * lilLog n)

private lemma lilScale_nonneg (n : ℕ) : 0 ≤ lilScale n := by
  exact Real.sqrt_nonneg _

private lemma lil_eventually_log_eq :
    ∀ᶠ n : ℕ in Filter.atTop,
      lilLog n = Real.log (Real.log (n : ℝ)) := by
  have hloglog : Filter.Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [(Filter.tendsto_atTop.1 hloglog 1), Filter.Ici_mem_atTop 3] with n hn h3
  have h3' : 3 ≤ n := h3
  rw [lilLog, Nat.max_eq_left h3', max_eq_right hn]

private lemma lil_eventually_scale_eq :
    ∀ᶠ n : ℕ in Filter.atTop,
      lilScale n = Real.sqrt
        (2 * (n : ℝ) * Real.log (Real.log (n : ℝ))) := by
  filter_upwards [lil_eventually_log_eq] with n hn
  rw [lilScale, hn]

private lemma lilLog_one_le (n : ℕ) : 1 ≤ lilLog n := by
  exact le_max_left _ _

private lemma lil_tendsto_scale :
    Filter.Tendsto lilScale Filter.atTop Filter.atTop := by
  apply Real.tendsto_sqrt_atTop.comp
  apply Filter.tendsto_atTop_mono
    (f := fun n : ℕ ↦ 2 * (n : ℝ))
  · intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [lilLog_one_le n]
  · exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)

private lemma lilLog_monotone : Monotone lilLog := by
  intro m n hmn
  have hm : (1 : ℝ) < ((m ⊔ 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < m ⊔ 3 from lt_of_lt_of_le (by omega) (Nat.le_max_right _ _))
  have hlog : 0 < Real.log ((m ⊔ 3 : ℕ) : ℝ) := Real.log_pos hm
  dsimp only [lilLog]
  gcongr

private lemma lilScale_monotone : Monotone lilScale := by
  intro m n hmn
  rw [lilScale, lilScale]
  apply Real.sqrt_le_sqrt
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) (by positivity)
  · exact lilLog_monotone hmn
  · exact le_trans (by positivity) (lilLog_one_le m)
  · positivity

private lemma lil_scale_div_tendsto_zero :
    Filter.Tendsto (fun n : ℕ ↦ lilScale n / (n : ℝ)) Filter.atTop (nhds 0) := by
  have hlogdiv : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
    convert Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop using 1
    funext n
    rfl
  have hsqrt : Filter.Tendsto
      (fun n : ℕ ↦ Real.sqrt (2 * (Real.log (n : ℝ) / (n : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa using (hlogdiv.const_mul 2).sqrt
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n ↦ div_nonneg (lilScale_nonneg n) (Nat.cast_nonneg n)
  · filter_upwards [lil_eventually_log_eq, Filter.eventually_gt_atTop 0,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
      with n hlog hn hlogone
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hll : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) :=
      Real.log_le_self (zero_le_one.trans hlogone)
    have hleft : 0 ≤ lilScale n / (n : ℝ) := div_nonneg (lilScale_nonneg n) hn0.le
    have hright : 0 ≤ Real.sqrt (2 * (Real.log (n : ℝ) / (n : ℝ))) := Real.sqrt_nonneg _
    have harg : 0 ≤ 2 * (Real.log (n : ℝ) / (n : ℝ)) := by positivity
    have hscaleArg : 0 ≤ 2 * (n : ℝ) * lilLog n := by
      exact mul_nonneg (mul_nonneg (by positivity) hn0.le) (zero_le_one.trans (lilLog_one_le n))
    rw [← (sq_le_sq₀ hleft hright)]
    rw [div_pow, lilScale, Real.sq_sqrt hscaleArg, Real.sq_sqrt harg, hlog]
    field_simp [hn0.ne']
    nlinarith
  · exact hsqrt

private lemma lil_div_log_log_monotone :
    MonotoneOn (fun x : ℝ ↦ x / Real.log (Real.log x))
      (Set.Ici (Real.exp (Real.exp 1))) := by
  apply StrictMonoOn.monotoneOn
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x hx
    have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
    have hlogx : Real.exp 1 ≤ Real.log x :=
      (Real.le_log_iff_exp_le hx0).2 hx
    have hx1 : 1 < x := (Real.one_lt_exp_iff.2 (Real.exp_pos 1)).trans_le hx
    have hll : 0 < Real.log (Real.log x) := zero_lt_one.trans_le <|
      (Real.le_log_iff_exp_le (Real.log_pos hx1)).2 hlogx
    have hcomp := (Real.hasDerivAt_log (Real.log_pos hx1).ne').comp x
      (Real.hasDerivAt_log hx0.ne')
    convert ((hasDerivAt_id x).div hcomp hll.ne').continuousAt.continuousWithinAt using 1
    ext y
    rfl
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := (Real.exp_pos _).trans hx
    have hx1 : 1 < x := (Real.one_lt_exp_iff.2 (Real.exp_pos 1)).trans hx
    have hlogx : Real.exp 1 < Real.log x :=
      (Real.lt_log_iff_exp_lt hx0).2 hx
    have hloglogx : 1 < Real.log (Real.log x) :=
      (Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hlogx)).2 hlogx
    have hcomp := (Real.hasDerivAt_log (Real.log_pos hx1).ne').comp x
      (Real.hasDerivAt_log hx0.ne')
    have hfun : (fun y : ℝ ↦ y / Real.log (Real.log y)) =
        id / (Real.log ∘ Real.log) := by
      ext y
      rfl
    rw [hfun, ((hasDerivAt_id x).div hcomp
      (ne_of_gt (zero_lt_one.trans hloglogx))).deriv]
    simp only [Function.comp_apply, id_eq, one_mul]
    have hinv : (Real.log x)⁻¹ < 1 := (inv_lt_one₀ (Real.log_pos hx1)).2 <|
      (Real.one_lt_exp_iff.2 zero_lt_one).trans hlogx
    have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0.ne'
    have hprod : x * ((Real.log x)⁻¹ * x⁻¹) = (Real.log x)⁻¹ := by
      calc
        x * ((Real.log x)⁻¹ * x⁻¹) = (Real.log x)⁻¹ * (x * x⁻¹) := by ring
        _ = (Real.log x)⁻¹ := by rw [hxinv, mul_one]
    rw [hprod]
    exact div_pos (sub_pos.2 (hinv.trans hloglogx))
      (sq_pos_of_pos (zero_lt_one.trans hloglogx))

private noncomputable def lilCut (δ : ℝ) (n : ℕ) : ℝ :=
  δ * Real.sqrt (((n + 1 : ℕ) : ℝ) / lilLog (n + 1))

private lemma lil_scale_div_mul_cut_pred {δ : ℝ} {n : ℕ} (hn : 0 < n) :
    lilScale n / (n : ℝ) * lilCut δ (n - 1) = δ * Real.sqrt 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < lilLog n := zero_lt_one.trans_le (lilLog_one_le n)
  rw [lilScale, lilCut, Nat.sub_add_cancel hn]
  calc
    Real.sqrt (2 * (n : ℝ) * lilLog n) / (n : ℝ) *
        (δ * Real.sqrt ((n : ℝ) / lilLog n)) =
        δ / (n : ℝ) * (Real.sqrt (2 * (n : ℝ) * lilLog n) *
          Real.sqrt ((n : ℝ) / lilLog n)) := by ring
    _ = δ / (n : ℝ) * Real.sqrt
        ((2 * (n : ℝ) * lilLog n) * ((n : ℝ) / lilLog n)) := by
      congr 1
      exact (Real.sqrt_mul (show 0 ≤ 2 * (n : ℝ) * lilLog n by positivity)
        ((n : ℝ) / lilLog n)).symm
    _ = δ / (n : ℝ) * Real.sqrt (2 * (n : ℝ) ^ 2) := by
      congr 2
      field_simp [hL.ne']
    _ = δ / (n : ℝ) * (Real.sqrt 2 * (n : ℝ)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hn0]
    _ = δ * Real.sqrt 2 := by field_simp [hn0.ne']

private lemma lilCut_eventually_mono {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ n, m ≤ n → lilCut δ m ≤ lilCut δ n := by
  have hloglog : Filter.Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [(Filter.tendsto_atTop.1 hloglog 1),
    (Filter.tendsto_atTop.1 tendsto_natCast_atTop_atTop (Real.exp (Real.exp 1))),
    Filter.Ici_mem_atTop 3] with m hmL hmE hm3
  intro n hmn
  have hm3nat : 3 ≤ m := hm3
  have hmn' : ((m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hm3' : 3 ≤ m + 1 := by omega
  have hn3 : 3 ≤ n + 1 := hm3'.trans (Nat.add_le_add_right hmn 1)
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hm3)
  have hmm1 : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < m + 1 by omega)
  have hlogm : Real.log (Real.log (m : ℝ)) ≤
      Real.log (Real.log ((m + 1 : ℕ) : ℝ)) := by
    gcongr
    · exact Real.log_pos hm1
    · exact_mod_cast Nat.le_succ m
  have hmL' : 1 ≤ Real.log (Real.log ((m + 1 : ℕ) : ℝ)) := hmL.trans hlogm
  have hlogmono : Real.log (Real.log ((m + 1 : ℕ) : ℝ)) ≤
      Real.log (Real.log ((n + 1 : ℕ) : ℝ)) := by
    gcongr
    exact Real.log_pos hmm1
  have hnL : 1 ≤ Real.log (Real.log ((n + 1 : ℕ) : ℝ)) := hmL'.trans hlogmono
  have hmdef : lilLog (m + 1) = Real.log (Real.log ((m + 1 : ℕ) : ℝ)) := by
    rw [lilLog, Nat.max_eq_left hm3', max_eq_right hmL']
  have hndef : lilLog (n + 1) = Real.log (Real.log ((n + 1 : ℕ) : ℝ)) := by
    rw [lilLog, Nat.max_eq_left hn3, max_eq_right hnL]
  rw [lilCut, lilCut, hmdef, hndef]
  apply mul_le_mul_of_nonneg_left _ hδ
  apply Real.sqrt_le_sqrt
  exact lil_div_log_log_monotone (hmE.trans (by norm_num))
    ((hmE.trans (by norm_num)).trans hmn') hmn'

private lemma lil_inv_sqrt_le_three_sub_sqrt {j : ℕ} (hj : 1 ≤ j) :
    (Real.sqrt (j : ℝ))⁻¹ ≤ 3 * (Real.sqrt (j + 1 : ℕ) - Real.sqrt j) := by
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hj)
  have hj1 : (j + 1 : ℕ) ≤ 4 * j := by omega
  have ha0 : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.2 hj0
  have hab : Real.sqrt (j : ℝ) ≤ Real.sqrt (j + 1 : ℕ) := by
    gcongr
    omega
  have hj1r : ((j + 1 : ℕ) : ℝ) ≤ 4 * (j : ℝ) := by exact_mod_cast hj1
  have hb : Real.sqrt (j + 1 : ℕ) ≤ 2 * Real.sqrt j := by
    nlinarith [hj1r, Real.sq_sqrt (show 0 ≤ (j : ℝ) by positivity),
      Real.sq_sqrt (show 0 ≤ ((j + 1 : ℕ) : ℝ) by positivity)]
  have hprod : (Real.sqrt (j + 1 : ℕ) - Real.sqrt j) *
      (Real.sqrt (j + 1 : ℕ) + Real.sqrt j) = 1 := by
    calc
      _ = Real.sqrt (j + 1 : ℕ) ^ 2 - Real.sqrt j ^ 2 := by ring
      _ = 1 := by
        rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        norm_num
  rw [inv_le_iff_one_le_mul₀ ha0]
  calc
    1 = (Real.sqrt (j + 1 : ℕ) - Real.sqrt j) *
        (Real.sqrt (j + 1 : ℕ) + Real.sqrt j) := hprod.symm
    _ ≤ (Real.sqrt (j + 1 : ℕ) - Real.sqrt j) * (3 * Real.sqrt j) := by
      gcongr
      linarith
    _ = 3 * (Real.sqrt (j + 1 : ℕ) - Real.sqrt j) * Real.sqrt j := by ring

private lemma lil_sum_range_inv_sqrt_le (n : ℕ) :
    ∑ j ∈ Finset.range n, (Real.sqrt (j : ℝ))⁻¹ ≤ 3 * Real.sqrt n := by
  obtain rfl | hn := n
  · simp
  have hn1 : 1 ≤ hn + 1 := by omega
  have hrange : ∑ j ∈ Finset.range (hn + 1), (Real.sqrt (j : ℝ))⁻¹ =
      ∑ j ∈ Finset.Ico 1 (hn + 1), (Real.sqrt (j : ℝ))⁻¹ := by
    rw [Finset.sum_Ico_eq_sub _ hn1]
    simp
  rw [hrange]
  calc
    ∑ j ∈ Finset.Ico 1 (hn + 1), (Real.sqrt (j : ℝ))⁻¹ ≤
        ∑ j ∈ Finset.Ico 1 (hn + 1),
          3 * (Real.sqrt (j + 1 : ℕ) - Real.sqrt j) := by
      gcongr with j hj
      exact lil_inv_sqrt_le_three_sub_sqrt (Finset.mem_Ico.1 hj).1
    _ = 3 * (Real.sqrt (hn + 1 : ℕ) - Real.sqrt 1) := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Finset.sum_Ico_sub (fun i : ℕ ↦ Real.sqrt (i : ℝ)) hn1)
    _ ≤ 3 * Real.sqrt (hn + 1 : ℕ) := by
      nlinarith [Real.sqrt_nonneg (hn + 1 : ℕ), Real.sqrt_nonneg 1]

private lemma lil_eventually_log_le_quarter_sqrt :
    ∀ᶠ n : ℕ in Filter.atTop, lilLog n ≤ Real.sqrt n / 4 := by
  have hsqrt : (fun n : ℕ ↦ Real.log (n : ℝ)) =o[Filter.atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
    have h := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by positivity)).comp_tendsto
      tendsto_natCast_atTop_atTop
    change (fun n : ℕ ↦ Real.log (n : ℝ)) =o[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 2)) at h
    simpa only [Real.sqrt_eq_rpow] using h
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [lil_eventually_log_eq,
    (Asymptotics.isLittleO_iff.1 hsqrt (show 0 < (4 : ℝ)⁻¹ by positivity)),
    (Filter.tendsto_atTop.1 hlog 1)] with n hn hbound hlogn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero fun hn0 ↦ by
      subst n
      norm_num at hlogn
  have hlogpos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by positivity) hlogn
  have hlog_le_n : Real.log (n : ℝ) ≤ (n : ℝ) :=
    (Real.log_le_sub_one_of_pos hnpos).trans (by linarith)
  rw [hn]
  calc
    Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hlogpos hnpos hlog_le_n
    _ ≤ Real.sqrt n / 4 := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hlogpos.le,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_mul_eq_div] using hbound

private lemma lil_inv_scale_le_inv_sqrt (j : ℕ) :
    (lilScale j)⁻¹ ≤ (Real.sqrt (j : ℝ))⁻¹ := by
  obtain rfl | j := j
  · simp [lilScale]
  have hj : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have hs : 0 < lilScale (j + 1) := by
    rw [lilScale]
    exact Real.sqrt_pos.2 <| mul_pos (mul_pos (by positivity) hj)
      (lt_of_lt_of_le zero_lt_one (lilLog_one_le _))
  apply (inv_le_inv₀ hs (Real.sqrt_pos.2 hj)).2
  rw [lilScale]
  apply Real.sqrt_le_sqrt
  nlinarith [lilLog_one_le (j + 1)]

private lemma lil_inv_scale_le_inv_sqrt_mul {j n : ℕ} (hj : 0 < j)
    (hnL : 0 < lilLog n) (hL : lilLog n ≤ 2 * lilLog j) :
    (lilScale j)⁻¹ ≤ (Real.sqrt (j : ℝ))⁻¹ * (Real.sqrt (lilLog n))⁻¹ := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hs : 0 < lilScale j := by
    rw [lilScale]
    exact Real.sqrt_pos.2 <| mul_pos (mul_pos (by positivity) hjr)
      (lt_of_lt_of_le zero_lt_one (lilLog_one_le _))
  have hp : 0 < Real.sqrt ((j : ℝ) * lilLog n) :=
    Real.sqrt_pos.2 (mul_pos hjr hnL)
  rw [← mul_inv, ← Real.sqrt_mul (Nat.cast_nonneg j)]
  apply (inv_le_inv₀ hs hp).2
  rw [lilScale]
  apply Real.sqrt_le_sqrt
  nlinarith

private lemma lil_eventually_log_le_two_log_after_sqrt :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ j,
      ⌈Real.sqrt (n : ℝ)⌉₊ ≤ j → lilLog n ≤ 2 * lilLog j := by
  have hloglog : Filter.Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hsqrt : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [lil_eventually_log_eq,
    (Filter.tendsto_atTop.1 hloglog (2 * (Real.log 2 + 1))),
    (Filter.tendsto_atTop.1 hsqrt 3)] with n hn hnL hsqrt3
  intro j hj
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℝ) < Real.sqrt n := lt_of_lt_of_le (by positivity) hsqrt3
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hlognpos : 0 < Real.log (n : ℝ) := Real.log_pos <| by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hsj : Real.sqrt (n : ℝ) ≤ (j : ℝ) :=
    (Nat.le_ceil (Real.sqrt (n : ℝ))).trans <| by exact_mod_cast hj
  have hj3 : 3 ≤ j := by exact_mod_cast hsqrt3.trans hsj
  have hlogsqrtpos : 0 < Real.log (Real.sqrt (n : ℝ)) := Real.log_pos <| by
    nlinarith
  have hlogsqrt : Real.log (Real.log (Real.sqrt (n : ℝ))) =
      Real.log (Real.log (n : ℝ)) - Real.log 2 := by
    rw [Real.log_sqrt hnpos.le, Real.log_div hlognpos.ne' (by norm_num)]
  have hmono : Real.log (Real.log (Real.sqrt (n : ℝ))) ≤
      Real.log (Real.log (j : ℝ)) := by
    gcongr
  have hjL : 1 ≤ Real.log (Real.log (j : ℝ)) := by
    rw [hlogsqrt] at hmono
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hjdef : lilLog j = Real.log (Real.log (j : ℝ)) := by
    rw [lilLog, Nat.max_eq_left hj3, max_eq_right hjL]
  rw [hlogsqrt] at hmono
  rw [hn, hjdef]
  nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

private lemma lil_eventually_sum_inv_scale_le :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∑ j ∈ Finset.range n, (lilScale j)⁻¹ ≤
        6 * Real.sqrt ((n : ℝ) / lilLog n) := by
  have hsqrt : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [lil_eventually_log_le_quarter_sqrt,
    lil_eventually_log_le_two_log_after_sqrt,
    (Filter.tendsto_atTop.1 hsqrt 1)] with n hlog hlogAfter hsqrt1
  let k : ℕ := ⌈Real.sqrt (n : ℝ)⌉₊
  have hklt : (k : ℝ) < Real.sqrt n + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hk2 : (k : ℝ) ≤ 2 * Real.sqrt n := by linarith
  have hLpos : 0 < lilLog n := lt_of_lt_of_le zero_lt_one (lilLog_one_le n)
  have hmul : (k : ℝ) * lilLog n ≤ (n : ℝ) := by
    calc
      (k : ℝ) * lilLog n ≤ (2 * Real.sqrt n) * (Real.sqrt n / 4) :=
        mul_le_mul hk2 hlog (by positivity) (by positivity)
      _ = (n : ℝ) / 2 := by
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
      _ ≤ (n : ℝ) := div_le_self (Nat.cast_nonneg n) (by norm_num)
  have hkdiv : (k : ℝ) ≤ (n : ℝ) / lilLog n := (le_div_iff₀ hLpos).2 hmul
  have hkcast : (k : ℝ) ≤ (n : ℝ) := by
    calc
      (k : ℝ) = (k : ℝ) * 1 := by ring
      _ ≤ (k : ℝ) * lilLog n :=
        mul_le_mul_of_nonneg_left (lilLog_one_le n) (Nat.cast_nonneg k)
      _ ≤ (n : ℝ) := hmul
  have hkn : k ≤ n := by exact_mod_cast hkcast
  have hkpos : 0 < k := by
    have : (1 : ℝ) ≤ (k : ℝ) := hsqrt1.trans (Nat.le_ceil (Real.sqrt (n : ℝ)))
    exact_mod_cast this
  have hfirst : ∑ j ∈ Finset.range k, (lilScale j)⁻¹ ≤
      3 * Real.sqrt ((n : ℝ) / lilLog n) := by
    calc
      ∑ j ∈ Finset.range k, (lilScale j)⁻¹ ≤
          ∑ j ∈ Finset.range k, (Real.sqrt (j : ℝ))⁻¹ := by
        apply Finset.sum_le_sum
        intro j _
        exact lil_inv_scale_le_inv_sqrt j
      _ ≤ 3 * Real.sqrt k := lil_sum_range_inv_sqrt_le k
      _ ≤ 3 * Real.sqrt ((n : ℝ) / lilLog n) := by
        gcongr
  have hsecond : ∑ j ∈ Finset.Ico k n, (lilScale j)⁻¹ ≤
      3 * Real.sqrt ((n : ℝ) / lilLog n) := by
    calc
      ∑ j ∈ Finset.Ico k n, (lilScale j)⁻¹ ≤
          ∑ j ∈ Finset.Ico k n,
            (Real.sqrt (j : ℝ))⁻¹ * (Real.sqrt (lilLog n))⁻¹ := by
        gcongr with j hj
        exact lil_inv_scale_le_inv_sqrt_mul
          (hkpos.trans_le (Finset.mem_Ico.1 hj).1) hLpos
          (hlogAfter j (Finset.mem_Ico.1 hj).1)
      _ = (∑ j ∈ Finset.Ico k n, (Real.sqrt (j : ℝ))⁻¹) *
          (Real.sqrt (lilLog n))⁻¹ := by rw [Finset.sum_mul]
      _ ≤ (∑ j ∈ Finset.range n, (Real.sqrt (j : ℝ))⁻¹) *
          (Real.sqrt (lilLog n))⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact Finset.mem_range.2 (Finset.mem_Ico.1 hj).2
        · intro j _ _
          positivity
      _ ≤ (3 * Real.sqrt n) * (Real.sqrt (lilLog n))⁻¹ := by
        gcongr
        exact lil_sum_range_inv_sqrt_le n
      _ = 3 * Real.sqrt ((n : ℝ) / lilLog n) := by
        rw [Real.sqrt_div (Nat.cast_nonneg n)]
        simp only [div_eq_mul_inv]
        ring
  rw [← Finset.sum_range_add_sum_Ico _ hkn]
  linarith

private lemma lil_abs_sub_truncation_le (x A : ℝ) :
    |x - truncation id A x| ≤ |x| := by
  simp only [truncation, Set.indicator, Function.comp_apply, id_eq]
  split_ifs
  · simp
  · simp

private lemma lil_sum_truncation_tail_le {δ : ℝ} (hδ : 0 < δ) {N n : ℕ}
    (hsum : ∀ m, N ≤ m →
      ∑ j ∈ Finset.range m, (lilScale j)⁻¹ ≤
        6 * Real.sqrt ((m : ℝ) / lilLog m)) (x : ℝ) :
    ∑ j ∈ Finset.range n,
        |x - truncation id (lilCut δ j) x| / lilScale j ≤
      |x| * (∑ j ∈ Finset.range N, (lilScale j)⁻¹) + 6 * x ^ 2 / δ := by
  have hterm_nonneg : ∀ j,
      0 ≤ |x - truncation id (lilCut δ j) x| / lilScale j := fun j ↦
    div_nonneg (abs_nonneg _) (lilScale_nonneg j)
  have hinv_nonneg : ∀ j, 0 ≤ (lilScale j)⁻¹ := fun j ↦ inv_nonneg.2 (lilScale_nonneg j)
  by_cases hn : n ≤ N
  · calc
      ∑ j ∈ Finset.range n, |x - truncation id (lilCut δ j) x| / lilScale j ≤
          ∑ j ∈ Finset.range N,
            |x - truncation id (lilCut δ j) x| / lilScale j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono hn
        · intro j _ _
          exact hterm_nonneg j
      _ ≤ |x| * (∑ j ∈ Finset.range N, (lilScale j)⁻¹) := by
        rw [Finset.mul_sum]
        gcongr with j hj
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (lil_abs_sub_truncation_le x _) (hinv_nonneg j)
      _ ≤ |x| * (∑ j ∈ Finset.range N, (lilScale j)⁻¹) + 6 * x ^ 2 / δ := by
        exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg x)) hδ.le)
  · have hNn : N ≤ n := le_of_not_ge hn
    rw [← Finset.sum_range_add_sum_Ico _ hNn]
    have hsuffix : ∑ j ∈ Finset.Ico N n,
        |x - truncation id (lilCut δ j) x| / lilScale j ≤ 6 * x ^ 2 / δ := by
      let A := (Finset.Ico N n).filter fun j ↦ lilCut δ j ≤ |x|
      have hreduce : ∑ j ∈ Finset.Ico N n,
          |x - truncation id (lilCut δ j) x| / lilScale j ≤
          |x| * ∑ j ∈ A, (lilScale j)⁻¹ := by
        rw [Finset.mul_sum]
        calc
          ∑ j ∈ Finset.Ico N n,
              |x - truncation id (lilCut δ j) x| / lilScale j ≤
              ∑ j ∈ Finset.Ico N n,
                if lilCut δ j ≤ |x| then |x| * (lilScale j)⁻¹ else 0 := by
            gcongr with j hj
            split_ifs with hcut
            · rw [div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right (lil_abs_sub_truncation_le x _)
                (hinv_nonneg j)
            · have hx : |x| < lilCut δ j := lt_of_not_ge hcut
              rw [truncation_eq_self hx, id_eq, sub_self, abs_zero, zero_div]
          _ = ∑ j ∈ A, |x| * (lilScale j)⁻¹ := by
            simp only [A, Finset.sum_filter]
      by_cases hA : A.Nonempty
      · let k := A.max' hA
        have hkA : k ∈ A := Finset.max'_mem A hA
        have hkIco : k ∈ Finset.Ico N n := (Finset.mem_filter.1 hkA).1
        have hkcut : lilCut δ k ≤ |x| := (Finset.mem_filter.1 hkA).2
        have hAsub : A ⊆ Finset.range (k + 1) := by
          intro j hj
          exact Finset.mem_range.2 <| Nat.lt_succ_iff.2 (Finset.le_max' A j hj)
        have hAsum : ∑ j ∈ A, (lilScale j)⁻¹ ≤
            6 * Real.sqrt (((k + 1 : ℕ) : ℝ) / lilLog (k + 1)) := by
          calc
            ∑ j ∈ A, (lilScale j)⁻¹ ≤
                ∑ j ∈ Finset.range (k + 1), (lilScale j)⁻¹ := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hAsub
              intro j _ _
              exact hinv_nonneg j
            _ ≤ 6 * Real.sqrt (((k + 1 : ℕ) : ℝ) / lilLog (k + 1)) :=
              hsum (k + 1) ((Finset.mem_Ico.1 hkIco).1.trans (Nat.le_succ k))
        have hroot : Real.sqrt (((k + 1 : ℕ) : ℝ) / lilLog (k + 1)) ≤ |x| / δ := by
          apply (le_div_iff₀ hδ).2
          simpa only [lilCut, mul_comm] using hkcut
        calc
          ∑ j ∈ Finset.Ico N n,
              |x - truncation id (lilCut δ j) x| / lilScale j ≤
              |x| * ∑ j ∈ A, (lilScale j)⁻¹ := hreduce
          _ ≤ |x| * (6 * Real.sqrt (((k + 1 : ℕ) : ℝ) / lilLog (k + 1))) := by
            gcongr
          _ ≤ |x| * (6 * (|x| / δ)) := by
            gcongr
          _ = 6 * |x| ^ 2 / δ := by ring
          _ = 6 * x ^ 2 / δ := by rw [sq_abs]
      · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hA
        rw [hAempty, Finset.sum_empty, mul_zero] at hreduce
        exact hreduce.trans <| div_nonneg (mul_nonneg (by norm_num) (sq_nonneg x)) hδ.le
    calc
      (∑ j ∈ Finset.range N, |x - truncation id (lilCut δ j) x| / lilScale j) +
          ∑ j ∈ Finset.Ico N n, |x - truncation id (lilCut δ j) x| / lilScale j ≤
          |x| * (∑ j ∈ Finset.range N, (lilScale j)⁻¹) + 6 * x ^ 2 / δ := by
        apply add_le_add
        · rw [Finset.mul_sum]
          gcongr with j hj
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (lil_abs_sub_truncation_le x _)
            (hinv_nonneg j)
        · exact hsuffix

private noncomputable def lilTailTerm (δ : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  |x - truncation id (lilCut δ j) x| / lilScale j

private lemma lilTailTerm_nonneg (δ : ℝ) (j : ℕ) (x : ℝ) :
    0 ≤ lilTailTerm δ j x := by
  exact div_nonneg (abs_nonneg _) (lilScale_nonneg j)

private lemma lilTailTerm_measurable (δ : ℝ) (j : ℕ) :
    Measurable (lilTailTerm δ j) := by
  have htrunc : Measurable (truncation id (lilCut δ j)) := by
    unfold truncation
    simpa only [Function.comp_id] using
      (measurable_id.indicator (measurableSet_Ioc : MeasurableSet (Set.Ioc (-lilCut δ j) _)))
  unfold lilTailTerm
  simpa only [Real.norm_eq_abs, Pi.sub_apply, id_eq] using
    (measurable_id.sub htrunc).norm.div_const (lilScale j)

private lemma lilTailTerm_le (δ : ℝ) (j : ℕ) (x : ℝ) :
    lilTailTerm δ j x ≤ |x| * (lilScale j)⁻¹ := by
  rw [lilTailTerm, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (lil_abs_sub_truncation_le x _)
    (inv_nonneg.2 (lilScale_nonneg j))

private lemma lil_summable_tailTerm {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    Summable (fun j ↦ lilTailTerm δ j x) := by
  have hEventually := lil_eventually_sum_inv_scale_le
  rw [Filter.eventually_atTop] at hEventually
  obtain ⟨N, hN⟩ := hEventually
  refine summable_of_sum_range_le
    (c := |x| * (∑ j ∈ Finset.range N, (lilScale j)⁻¹) + 6 * x ^ 2 / δ)
    (fun j ↦ lilTailTerm_nonneg δ j x) ?_
  intro n
  simpa only [lilTailTerm] using lil_sum_truncation_tail_le hδ hN x (n := n)

private lemma lil_tailTerm_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfMeas : Measurable f) (hfInt : Integrable f μ)
    (δ : ℝ) (j : ℕ) :
    Integrable (fun ω ↦ lilTailTerm δ j (f ω)) μ := by
  have hdom : Integrable (fun ω ↦ |f ω| * (lilScale j)⁻¹) μ := by
    simpa only [Real.norm_eq_abs] using hfInt.norm.mul_const (lilScale j)⁻¹
  apply hdom.mono' ((lilTailTerm_measurable δ j).comp hfMeas).aestronglyMeasurable
  filter_upwards with ω
  change |lilTailTerm δ j (f ω)| ≤ |f ω| * (lilScale j)⁻¹
  rw [abs_of_nonneg (lilTailTerm_nonneg δ j (f ω))]
  exact lilTailTerm_le δ j (f ω)

private lemma lil_summable_integral_tailTerm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hInt : Integrable (X 0) μ) (hMemLp : MemLp (X 0) 2 μ)
    {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun j ↦ ∫ ω, lilTailTerm δ j (X j ω) ∂μ) := by
  have hsq : Integrable (fun ω ↦ X 0 ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq (hMeas 0).aestronglyMeasurable).1 hMemLp
  have hEventually := lil_eventually_sum_inv_scale_le
  rw [Filter.eventually_atTop] at hEventually
  obtain ⟨N, hN⟩ := hEventually
  let C := ∑ j ∈ Finset.range N, (lilScale j)⁻¹
  let bound := fun ω ↦ |X 0 ω| * C + 6 * X 0 ω ^ 2 / δ
  have hbound : Integrable bound μ := by
    have hfirst : Integrable (fun ω ↦ |X 0 ω| * C) μ := by
      simpa only [Real.norm_eq_abs] using hInt.norm.mul_const C
    have hsecond : Integrable (fun ω ↦ 6 * X 0 ω ^ 2 / δ) μ := by
      convert hsq.mul_const (6 / δ) using 1
      ext ω
      ring
    exact hfirst.add hsecond
  refine summable_of_sum_range_le
    (c := ∫ ω, bound ω ∂μ)
    (fun j ↦ integral_nonneg fun ω ↦ lilTailTerm_nonneg δ j (X j ω)) ?_
  intro n
  have htermInt : ∀ j ∈ Finset.range n,
      Integrable (fun ω ↦ lilTailTerm δ j (X 0 ω)) μ := by
    intro j _
    exact lil_tailTerm_integrable (hMeas 0) hInt δ j
  calc
    ∑ j ∈ Finset.range n, ∫ ω, lilTailTerm δ j (X j ω) ∂μ =
        ∑ j ∈ Finset.range n, ∫ ω, lilTailTerm δ j (X 0 ω) ∂μ := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [Function.comp_apply] using
        ((hIdent j).comp (lilTailTerm_measurable δ j)).integral_eq
    _ = ∫ ω, ∑ j ∈ Finset.range n, lilTailTerm δ j (X 0 ω) ∂μ := by
      exact (integral_finsetSum (Finset.range n) htermInt).symm
    _ ≤ ∫ ω, bound ω ∂μ := by
      apply integral_mono_ae (integrable_finsetSum (Finset.range n) htermInt) hbound
      filter_upwards with ω
      simpa only [lilTailTerm, bound, C] using
        lil_sum_truncation_tail_le hδ hN (X 0 ω) (n := n)

private lemma lil_ae_summable_tailTerm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hInt : Integrable (X 0) μ) (hMemLp : MemLp (X 0) 2 μ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂μ, Summable (fun j ↦ lilTailTerm δ j (X j ω)) := by
  have hIntegral := lil_summable_integral_tailTerm X hMeas hIdent hInt hMemLp hδ
  let f := fun j ω ↦ lilTailTerm δ j (X j ω)
  have hfInt : ∀ j, Integrable (f j) μ := by
    intro j
    exact lil_tailTerm_integrable (hMeas j) ((hIdent j).integrable_iff.mpr hInt) δ j
  have hnorm : ∀ j, eLpNorm (f j) 1 μ = ENNReal.ofReal (∫ ω, f j ω ∂μ) := by
    intro j
    rw [eLpNorm_one_eq_lintegral_enorm (hfInt j).aestronglyMeasurable]
    calc
      ∫⁻ ω, ‖f j ω‖ₑ ∂μ = ∫⁻ ω, ENNReal.ofReal (f j ω) ∂μ := by
        apply lintegral_congr
        intro ω
        rw [← ofReal_norm, Real.norm_eq_abs,
          abs_of_nonneg (lilTailTerm_nonneg δ j (X j ω))]
      _ = ENNReal.ofReal (∫ ω, f j ω ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (hfInt j)
          (Filter.Eventually.of_forall fun ω ↦ lilTailTerm_nonneg δ j (X j ω))).symm
  have hLp : ∑' j, eLpNorm (f j) 1 μ ≠ ∞ := by
    simp_rw [hnorm]
    exact hIntegral.tsum_ofReal_ne_top
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top (p := (1 : ℝ≥0∞)) le_rfl hLp] with ω hω
  simpa only [f, Real.norm_eq_abs, abs_of_nonneg (lilTailTerm_nonneg δ _ _)] using hω

private lemma lil_kronecker (a : ℕ → ℝ)
    (h : Summable (fun j ↦ |a j| / lilScale j)) :
    Filter.Tendsto (fun n ↦ (∑ j ∈ Finset.range n, a j) / lilScale n)
      Filter.atTop (nhds 0) := by
  let f := fun j ↦ |a j| / lilScale j
  have hf_nonneg : ∀ j, 0 ≤ f j := fun j ↦
    div_nonneg (abs_nonneg _) (lilScale_nonneg j)
  have hpartial := h.tendsto_sum_tsum_nat
  have htail : Filter.Tendsto (fun N ↦ ∑' i, f (i + N)) Filter.atTop (nhds 0) := by
    have hpartial' : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n, f i)
        Filter.atTop (nhds (∑' i, f i)) := by
      simpa only [f] using hpartial
    have hsub : Filter.Tendsto
        (fun n ↦ (∑' i, f i) - ∑ i ∈ Finset.range n, f i)
        Filter.atTop (nhds ((∑' i, f i) - ∑' i, f i)) :=
      tendsto_const_nhds.sub hpartial'
    convert hsub using 1
    · ext N
      have hsplit : ∑ i ∈ Finset.range N, f i + ∑' i, f (i + N) = ∑' i, f i := by
        simpa only [f] using h.sum_add_tsum_nat_add N
      linarith
    · simp
  rw [Metric.tendsto_atTop] at htail ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := htail (ε / 2) (by positivity)
  let N' := N ⊔ 1
  have htailN : ∑' i, f (i + N') < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun _ ↦ hf_nonneg _)] using
      hN N' (Nat.le_max_left _ _)
  have hearly : Filter.Tendsto
      (fun n ↦ |∑ j ∈ Finset.range N', a j| / lilScale n)
      Filter.atTop (nhds 0) :=
    lil_tendsto_scale.const_div_atTop _
  rw [Metric.tendsto_atTop] at hearly
  obtain ⟨M, hM⟩ := hearly (ε / 2) (by positivity)
  refine ⟨M ⊔ N', fun n hn ↦ ?_⟩
  have hMn : M ≤ n := (Nat.le_max_left M N').trans hn
  have hNn : N' ≤ n := (Nat.le_max_right M N').trans hn
  have hN'pos : 0 < N' := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right N 1)
  have hnpos : 0 < n := hN'pos.trans_le hNn
  have hscale : 0 < lilScale n := by
    rw [lilScale]
    exact Real.sqrt_pos.2 <| mul_pos (mul_pos (by positivity) (by exact_mod_cast hnpos))
      (lt_of_lt_of_le zero_lt_one (lilLog_one_le n))
  have hearlyN : |∑ j ∈ Finset.range N', a j| / lilScale n < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg (abs_nonneg _) hscale.le)] using hM n hMn
  have hshift : Summable (fun i ↦ f (i + N')) :=
    (summable_nat_add_iff N').2 h
  have hfiniteTail : ∑ j ∈ Finset.Ico N' n, f j ≤ ∑' i, f (i + N') := by
    rw [Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm] using
      hshift.sum_le_tsum (Finset.range (n - N')) (fun i _ ↦ hf_nonneg (i + N'))
  have hweighted : (∑ j ∈ Finset.Ico N' n, |a j|) / lilScale n ≤
      ∑ j ∈ Finset.Ico N' n, f j := by
    apply (div_le_iff₀ hscale).2
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := (Finset.mem_Ico.1 hj).2.le
    have hsj : 0 < lilScale j := by
      have hjpos : 0 < j := hN'pos.trans_le (Finset.mem_Ico.1 hj).1
      rw [lilScale]
      exact Real.sqrt_pos.2 <| mul_pos (mul_pos (by positivity) (by exact_mod_cast hjpos))
        (lt_of_lt_of_le zero_lt_one (lilLog_one_le j))
    calc
      |a j| = f j * lilScale j := by
        dsimp only [f]
        rw [div_mul_cancel₀ _ hsj.ne']
      _ ≤ f j * lilScale n := by
        exact mul_le_mul_of_nonneg_left (lilScale_monotone hjn) (hf_nonneg j)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hscale,
    ← Finset.sum_range_add_sum_Ico _ hNn]
  calc
    |(∑ j ∈ Finset.range N', a j) + ∑ j ∈ Finset.Ico N' n, a j| / lilScale n ≤
        (|∑ j ∈ Finset.range N', a j| +
          ∑ j ∈ Finset.Ico N' n, |a j|) / lilScale n := by
      apply div_le_div_of_nonneg_right _ hscale.le
      exact (abs_add_le _ _).trans <| add_le_add_right
        (Finset.abs_sum_le_sum_abs a (Finset.Ico N' n)) _
    _ = |∑ j ∈ Finset.range N', a j| / lilScale n +
        (∑ j ∈ Finset.Ico N' n, |a j|) / lilScale n := by rw [add_div]
    _ ≤ |∑ j ∈ Finset.range N', a j| / lilScale n +
        ∑ j ∈ Finset.Ico N' n, f j := add_le_add le_rfl hweighted
    _ ≤ |∑ j ∈ Finset.range N', a j| / lilScale n + ∑' i, f (i + N') :=
      add_le_add le_rfl hfiniteTail
    _ < ε / 2 + ε / 2 := add_lt_add hearlyN htailN
    _ = ε := by ring

private noncomputable def lilTruncated
    {Ω : Type*} (X : ℕ → Ω → ℝ) (δ : ℝ) (j : ℕ) : Ω → ℝ :=
  truncation (X j) (lilCut δ j)

private noncomputable def lilRemainder
    {Ω : Type*} (X : ℕ → Ω → ℝ) (δ : ℝ) (j : ℕ) : Ω → ℝ :=
  X j - lilTruncated X δ j

private noncomputable def lilCentered
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (δ : ℝ) (j : ℕ) : Ω → ℝ :=
  fun ω ↦ lilTruncated X δ j ω - ∫ x, lilTruncated X δ j x ∂μ

private lemma lil_tailTerm_eq
    {Ω : Type*} (X : ℕ → Ω → ℝ) (δ : ℝ) (j : ℕ) (ω : Ω) :
    lilTailTerm δ j (X j ω) = |lilRemainder X δ j ω| / lilScale j := by
  rfl

private lemma lil_ae_remainder_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hInt : Integrable (X 0) μ) (hMemLp : MemLp (X 0) 2 μ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n ↦ (∑ j ∈ Finset.range n, lilRemainder X δ j ω) / lilScale n)
      Filter.atTop (nhds 0) := by
  filter_upwards [lil_ae_summable_tailTerm X hMeas hIdent hInt hMemLp hδ] with ω hω
  apply lil_kronecker
  simpa only [lil_tailTerm_eq] using hω

private lemma lil_summable_mean_remainder
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hInt : Integrable (X 0) μ) (hMemLp : MemLp (X 0) 2 μ)
    {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun j ↦ |∫ ω, lilRemainder X δ j ω ∂μ| / lilScale j) := by
  have hIntegral := lil_summable_integral_tailTerm X hMeas hIdent hInt hMemLp hδ
  apply Summable.of_nonneg_of_le
  · intro j
    exact div_nonneg (abs_nonneg _) (lilScale_nonneg j)
  · intro j
    have hinv : 0 ≤ (lilScale j)⁻¹ := inv_nonneg.2 (lilScale_nonneg j)
    calc
      |∫ ω, lilRemainder X δ j ω ∂μ| / lilScale j =
          ‖∫ ω, lilRemainder X δ j ω ∂μ‖ * (lilScale j)⁻¹ := by
        rw [Real.norm_eq_abs, div_eq_mul_inv]
      _ ≤ (∫ ω, ‖lilRemainder X δ j ω‖ ∂μ) * (lilScale j)⁻¹ :=
        mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) hinv
      _ = ∫ ω, lilTailTerm δ j (X j ω) ∂μ := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with ω
        rw [Real.norm_eq_abs, lil_tailTerm_eq, div_eq_mul_inv]
  · exact hIntegral

private lemma lil_mean_remainder_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hInt : Integrable (X 0) μ) (hMemLp : MemLp (X 0) 2 μ)
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun n ↦ (∑ j ∈ Finset.range n, ∫ ω, lilRemainder X δ j ω ∂μ) / lilScale n)
      Filter.atTop (nhds 0) := by
  exact lil_kronecker _ (lil_summable_mean_remainder X hMeas hIdent hInt hMemLp hδ)

private lemma lil_exp_le_quadratic {x ρ : ℝ} (hρ1 : ρ ≤ 1)
    (hx : |x| ≤ ρ) :
    Real.exp x ≤ 1 + x + ((1 : ℝ) / 2 + 2 * ρ / 9) * x ^ 2 := by
  have hx1 : |x| ≤ 1 := hx.trans hρ1
  have hbound := Real.exp_bound hx1 (n := 3) (by norm_num)
  have hrem : Real.exp x - (1 + x + x ^ 2 / 2) ≤ 2 * |x| ^ 3 / 9 := by
    have := (le_abs_self (Real.exp x - ∑ m ∈ Finset.range 3, x ^ m / m.factorial)).trans hbound
    norm_num [Finset.sum_range_succ, pow_succ] at this ⊢
    linarith
  have habs : |x| ^ 3 ≤ ρ * x ^ 2 := by
    calc
      |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, sq_abs]; ring
      _ ≤ ρ * x ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
  nlinarith

private lemma lil_mgf_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hfMeas : Measurable f) (hfInt : Integrable f μ)
    (hfsqInt : Integrable (fun ω ↦ f ω ^ 2) μ)
    (hmean : ∫ ω, f ω ∂μ = 0) (hsecond : ∫ ω, f ω ^ 2 ∂μ ≤ 1)
    {C t ρ : ℝ} (ht : 0 ≤ t) (hC : ∀ ω, |f ω| ≤ C)
    (htC : t * C ≤ ρ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∫ ω, Real.exp (t * f ω) ∂μ ≤
      Real.exp (((1 : ℝ) / 2 + 2 * ρ / 9) * t ^ 2) := by
  let A : ℝ := (1 : ℝ) / 2 + 2 * ρ / 9
  have htf : ∀ ω, |t * f ω| ≤ ρ := by
    intro ω
    rw [abs_mul, abs_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_left (hC ω) ht).trans htC
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hmu : μ.real Set.univ = 1 := by
    rw [Measure.real, measure_univ]
    norm_num
  have hexpInt : Integrable (fun ω ↦ Real.exp (t * f ω)) μ := by
    apply (integrable_const (c := Real.exp ρ)).mono'
      ((Real.continuous_exp.measurable.comp (measurable_const.mul hfMeas)).aestronglyMeasurable)
    filter_upwards with ω
    change |Real.exp (t * f ω)| ≤ Real.exp ρ
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp_of_le <| (le_abs_self _).trans (htf ω)
  have htfInt : Integrable (fun ω ↦ t * f ω) μ := hfInt.const_mul t
  have htfsqInt : Integrable (fun ω ↦ (t * f ω) ^ 2) μ := by
    convert hfsqInt.const_mul (t ^ 2) using 1
    ext ω
    ring
  have hconstInt : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ := integrable_const (c := 1)
  have hpolyInt : Integrable (fun ω ↦ 1 + t * f ω + A * (t * f ω) ^ 2) μ := by
    exact (hconstInt.add htfInt).add (htfsqInt.const_mul A)
  calc
    ∫ ω, Real.exp (t * f ω) ∂μ ≤
        ∫ ω, (1 + t * f ω + A * (t * f ω) ^ 2) ∂μ := by
      apply integral_mono_ae hexpInt hpolyInt
      filter_upwards with ω
      exact lil_exp_le_quadratic hρ1 (htf ω)
    _ = 1 + A * t ^ 2 * (∫ ω, f ω ^ 2 ∂μ) := by
      have hfun : (fun ω ↦ 1 + t * f ω + A * (t * f ω) ^ 2) =
          (fun _ : Ω ↦ (1 : ℝ)) + (fun ω ↦ t * f ω) +
            (fun ω ↦ A * (t * f ω) ^ 2) := rfl
      rw [hfun]
      have houter := integral_add (μ := μ) (hconstInt.add htfInt) (htfsqInt.const_mul A)
      change (∫ a, ((fun _ : Ω ↦ (1 : ℝ)) + (fun ω ↦ t * f ω)) a +
        A * (t * f a) ^ 2 ∂μ) = _
      rw [houter]
      have hinner := integral_add (μ := μ) hconstInt htfInt
      change (∫ a, 1 + t * f a ∂μ) + (∫ a, A * (t * f a) ^ 2 ∂μ) = _
      rw [hinner, integral_const_mul]
      have hsquare : (fun ω ↦ (t * f ω) ^ 2) = fun ω ↦ t ^ 2 * f ω ^ 2 := by
        funext ω
        ring
      rw [integral_const_mul A (fun ω ↦ (t * f ω) ^ 2), hsquare,
        integral_const_mul (t ^ 2) (fun ω ↦ f ω ^ 2)]
      simp only [integral_const, hmu, one_smul, hmean, mul_zero, add_zero]
      ring
    _ ≤ 1 + A * t ^ 2 := by
      exact add_le_add le_rfl <| by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hsecond (mul_nonneg hA (sq_nonneg t))
    _ ≤ Real.exp (A * t ^ 2) := by simpa [add_comm] using Real.add_one_le_exp (A * t ^ 2)

private lemma lilTruncated_measurable
    {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hMeas : ∀ j, Measurable (X j)) (δ : ℝ) (j : ℕ) :
    Measurable (lilTruncated X δ j) := by
  unfold lilTruncated truncation
  exact (measurable_id.indicator measurableSet_Ioc).comp (hMeas j)

private lemma lilTruncated_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j)) (δ : ℝ) (j : ℕ) :
    Integrable (lilTruncated X δ j) μ := by
  exact (hMeas j).aestronglyMeasurable.integrable_truncation

private lemma lilCentered_measurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j)) (δ : ℝ) (j : ℕ) :
    Measurable (lilCentered μ X δ j) := by
  exact (lilTruncated_measurable X hMeas δ j).sub_const _

private lemma lilCentered_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j)) (δ : ℝ) (j : ℕ) :
    Integrable (lilCentered μ X δ j) μ := by
  exact (lilTruncated_integrable X hMeas δ j).sub (integrable_const (c := _))

private lemma lilCentered_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j)) (δ : ℝ) (j : ℕ) :
    ∫ ω, lilCentered μ X δ j ω ∂μ = 0 := by
  change (∫ ω, lilTruncated X δ j ω - ∫ x, lilTruncated X δ j x ∂μ ∂μ) = 0
  rw [integral_sub (lilTruncated_integrable X hMeas δ j)
    (integrable_const (c := _)), integral_const]
  simp [Measure.real, measure_univ]

private lemma lilCentered_sq_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j)) (δ : ℝ) (j : ℕ) :
    Integrable (fun ω ↦ lilCentered μ X δ j ω ^ 2) μ := by
  have hYlp : MemLp (lilTruncated X δ j) 2 μ := by
    simpa only [lilTruncated] using
      (hMeas j).aestronglyMeasurable.memLp_truncation (A := lilCut δ j) (p := 2)
  have hcenterLp : MemLp (lilCentered μ X δ j) 2 μ := by
    change MemLp (fun ω ↦ lilTruncated X δ j ω -
      ∫ x, lilTruncated X δ j x ∂μ) 2 μ
    exact hYlp.sub (memLp_const _)
  exact (memLp_two_iff_integrable_sq
    (lilCentered_measurable X hMeas δ j).aestronglyMeasurable).1 hcenterLp

private lemma lilCentered_second_le_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ) (hMean : ∫ ω, X 0 ω ∂μ = 0)
    (hVar : Var[X 0; μ] = 1) (δ : ℝ) (j : ℕ) :
    ∫ ω, lilCentered μ X δ j ω ^ 2 ∂μ ≤ 1 := by
  have hXjLp : MemLp (X j) 2 μ := (hIdent j).memLp_iff.mpr hMemLp
  have hYlp : MemLp (lilTruncated X δ j) 2 μ := by
    simpa only [lilTruncated] using
      (hMeas j).aestronglyMeasurable.memLp_truncation (A := lilCut δ j) (p := 2)
  have hYsq : Integrable (fun ω ↦ lilTruncated X δ j ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq
      (lilTruncated_measurable X hMeas δ j).aestronglyMeasurable).1 hYlp
  have hXjsq : Integrable (fun ω ↦ X j ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq (hMeas j).aestronglyMeasurable).1 hXjLp
  have hYX : ∫ ω, lilTruncated X δ j ω ^ 2 ∂μ ≤ ∫ ω, X j ω ^ 2 ∂μ := by
    apply integral_mono hYsq hXjsq
    intro ω
    calc
      lilTruncated X δ j ω ^ 2 = |lilTruncated X δ j ω| ^ 2 := (sq_abs _).symm
      _ ≤ |X j ω| ^ 2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2
        (abs_truncation_le_abs_self (X j) (lilCut δ j) ω)
      _ = X j ω ^ 2 := sq_abs _
  have hXj : ∫ ω, X j ω ^ 2 ∂μ = 1 := by
    calc
      ∫ ω, X j ω ^ 2 ∂μ = ∫ ω, X 0 ω ^ 2 ∂μ := by
        simpa only [Function.comp_apply, id_eq] using
          ((hIdent j).comp (measurable_id.pow_const 2)).integral_eq
      _ = 1 := lil_integral_sq_eq_one X (hMeas 0) hMean hVar
  change (∫ ω, (lilTruncated X δ j ω - ∫ x, lilTruncated X δ j x ∂μ) ^ 2 ∂μ) ≤ 1
  rw [← variance_eq_integral (lilTruncated_measurable X hMeas δ j).aemeasurable,
    variance_eq_sub hYlp]
  exact (sub_le_self _ (sq_nonneg _)).trans (hYX.trans_eq hXj)

private lemma lilCentered_abs_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) (ω : Ω) :
    |lilCentered μ X δ j ω| ≤ 2 * lilCut δ j := by
  have hcut : 0 ≤ lilCut δ j := by
    rw [lilCut]
    positivity
  have hY : |lilTruncated X δ j ω| ≤ lilCut δ j := by
    exact (abs_truncation_le_bound (X j) (lilCut δ j) ω).trans_eq (abs_of_nonneg hcut)
  have hmean : |∫ x, lilTruncated X δ j x ∂μ| ≤ lilCut δ j := by
    rw [← Real.norm_eq_abs]
    have h := norm_integral_le_of_norm_le_const
      (μ := μ) (f := lilTruncated X δ j)
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs]
        exact (abs_truncation_le_bound (X j) (lilCut δ j) x).trans_eq (abs_of_nonneg hcut))
    simpa [Measure.real, measure_univ] using h
  rw [lilCentered]
  exact (abs_sub _ _).trans (by linarith)

private lemma lilCentered_iIndep
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X μ) (δ : ℝ) :
    iIndepFun (lilCentered μ X δ) μ := by
  let g := fun j (x : ℝ) ↦ truncation id (lilCut δ j) x -
    ∫ ω, lilTruncated X δ j ω ∂μ
  have hg : ∀ j, Measurable (g j) := by
    intro j
    exact ((measurable_id.indicator measurableSet_Ioc).comp measurable_id).sub_const _
  have heq : (fun i ↦ g i ∘ X i) = lilCentered μ X δ := by
    funext i ω
    rfl
  rw [← heq]
  exact hIndep.comp g hg

private lemma lil_centered_sum_mgf_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ) (hMean : ∫ ω, X 0 ω ∂μ = 0)
    (hVar : Var[X 0; μ] = 1) {δ t ρ : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {n : ℕ}
    (htCut : ∀ j ∈ Finset.range n, t * (2 * lilCut δ j) ≤ ρ) :
    ∫ ω, Real.exp (t * ∑ j ∈ Finset.range n, lilCentered μ X δ j ω) ∂μ ≤
      Real.exp ((n : ℝ) * ((1 : ℝ) / 2 + 2 * ρ / 9) * t ^ 2) := by
  let W := lilCentered μ X δ
  let E : Fin n → Ω → ℝ := fun j ω ↦ Real.exp (t * W j ω)
  have hWindep : iIndepFun W μ := lilCentered_iIndep X hIndep δ
  have hEindep : iIndepFun E μ := by
    exact (hWindep.precomp fun _ _ h ↦ Fin.ext h).comp
      (fun _ x ↦ Real.exp (t * x)) (fun _ ↦ Real.continuous_exp.measurable.comp <|
        measurable_const.mul measurable_id)
  have hEmeas : ∀ j, AEStronglyMeasurable (E j) μ := by
    intro j
    exact (Real.continuous_exp.measurable.comp <| measurable_const.mul <|
      lilCentered_measurable X hMeas δ j).aestronglyMeasurable
  have hprod := hEindep.integral_fun_prod_eq_prod_integral hEmeas
  have hsingle : ∀ j : Fin n,
      ∫ ω, E j ω ∂μ ≤ Real.exp (((1 : ℝ) / 2 + 2 * ρ / 9) * t ^ 2) := by
    intro j
    apply lil_mgf_le (lilCentered_measurable X hMeas δ j)
      (lilCentered_integrable X hMeas δ j)
      (lilCentered_sq_integrable X hMeas δ j)
      (lilCentered_mean_zero X hMeas δ j)
      (lilCentered_second_le_one X hMeas hIdent hMemLp hMean hVar δ j)
      ht (fun ω ↦ lilCentered_abs_le X hδ j ω)
      (htCut j (Finset.mem_range.2 j.isLt)) hρ hρ1
  calc
    ∫ ω, Real.exp (t * ∑ j ∈ Finset.range n, lilCentered μ X δ j ω) ∂μ =
        ∫ ω, ∏ j : Fin n, E j ω ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [← Real.exp_sum]
      congr 1
      calc
        t * ∑ j ∈ Finset.range n, lilCentered μ X δ j ω =
            ∑ j ∈ Finset.range n, t * lilCentered μ X δ j ω := by
          rw [Finset.mul_sum]
        _ = ∑ j : Fin n, t * W j ω := by
          simpa only [W] using
            (Fin.sum_univ_eq_sum_range (fun j ↦ t * lilCentered μ X δ j ω) n).symm
    _ = ∏ j : Fin n, ∫ ω, E j ω ∂μ := hprod
    _ ≤ ∏ _j : Fin n, Real.exp (((1 : ℝ) / 2 + 2 * ρ / 9) * t ^ 2) :=
      Finset.prod_le_prod₀
        (fun j _ ↦ integral_nonneg fun ω ↦ (Real.exp_pos (t * W j ω)).le)
        (fun j _ ↦ hsingle j)
    _ = Real.exp ((n : ℝ) * ((1 : ℝ) / 2 + 2 * ρ / 9) * t ^ 2) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
      congr 1
      ring

private lemma lil_exp_integrable_of_abs_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ ω, |f ω| ≤ B) :
    Integrable (fun ω ↦ Real.exp (f ω)) μ := by
  apply (integrable_const (c := Real.exp B)).mono'
    ((Real.continuous_exp.measurable.comp hf).aestronglyMeasurable)
  filter_upwards with ω
  change |Real.exp (f ω)| ≤ Real.exp B
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp_of_le <| (le_abs_self _).trans (hB ω)

private lemma lil_one_le_centered_mgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t) (j : ℕ) :
    1 ≤ ∫ ω, Real.exp (t * lilCentered μ X δ j ω) ∂μ := by
  have hexp : Integrable (fun ω ↦ Real.exp (t * lilCentered μ X δ j ω)) μ := by
    refine lil_exp_integrable_of_abs_le (B := t * (2 * lilCut δ j))
      (measurable_const.mul <| lilCentered_measurable X hMeas δ j) ?_
    intro ω
    rw [abs_mul, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left (lilCentered_abs_le X hδ j ω) ht
  have hlin : Integrable (fun ω ↦ 1 + t * lilCentered μ X δ j ω) μ :=
    (integrable_const (c := 1)).add ((lilCentered_integrable X hMeas δ j).const_mul t)
  calc
    1 = ∫ _ω : Ω, (1 : ℝ) ∂μ := by simp
    _ = ∫ ω, 1 + t * lilCentered μ X δ j ω ∂μ := by
      rw [integral_add (integrable_const (c := 1))
        ((lilCentered_integrable X hMeas δ j).const_mul t), integral_const_mul,
        lilCentered_mean_zero X hMeas δ j]
      simp
    _ ≤ ∫ ω, Real.exp (t * lilCentered μ X δ j ω) ∂μ := by
      apply integral_mono hlin hexp
      intro ω
      simpa [add_comm] using Real.add_one_le_exp (t * lilCentered μ X δ j ω)

private lemma lil_exp_partial_sum_submartingale
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : ℕ → Ω → ℝ} (hWsm : ∀ j, StronglyMeasurable (W j))
    (hWindep : iIndepFun W μ) {C : ℕ → ℝ} (hC : ∀ j ω, |W j ω| ≤ C j)
    {t : ℝ} (ht : 0 ≤ t) (hlower : ∀ j, 1 ≤ ∫ ω, Real.exp (t * W j ω) ∂μ) :
    Submartingale
      (fun i ω ↦ Real.exp (t * ∑ j ∈ Finset.range (i + 1), W j ω))
      (Filtration.natural W hWsm) μ := by
  let 𝒢 := Filtration.natural W hWsm
  let M := fun i ω ↦ Real.exp (t * ∑ j ∈ Finset.range (i + 1), W j ω)
  have hWadp : StronglyAdapted 𝒢 W := Filtration.stronglyAdapted_natural hWsm
  have hMsm : ∀ i, StronglyMeasurable[𝒢 i] (M i) := by
    intro i
    have hsum : StronglyMeasurable[𝒢 i]
        (fun ω ↦ ∑ j ∈ Finset.range (i + 1), W j ω) := by
      exact Finset.stronglyMeasurable_fun_sum (Finset.range (i + 1)) fun j hj ↦
        (hWadp j).mono (𝒢.mono (Nat.le_of_lt_succ (Finset.mem_range.1 hj)))
    exact Real.continuous_exp.comp_stronglyMeasurable (hsum.const_mul t)
  have hMint : ∀ i, Integrable (M i) μ := by
    intro i
    refine lil_exp_integrable_of_abs_le
      (B := t * ∑ j ∈ Finset.range (i + 1), C j)
      (measurable_const.mul <| Finset.measurable_fun_sum _ fun j _ ↦ (hWsm j).measurable)
      ?_
    intro ω
    rw [abs_mul, abs_of_nonneg ht]
    apply mul_le_mul_of_nonneg_left _ ht
    exact (Finset.abs_sum_le_sum_abs (fun j ↦ W j ω) _).trans <|
      Finset.sum_le_sum fun j _ ↦ hC j ω
  change Submartingale M 𝒢 μ
  apply submartingale_of_setIntegral_le_succ hMsm hMint
  intro i s hs
  have hs0 : MeasurableSet s := 𝒢.le i s hs
  let P := M i
  let Q := fun ω ↦ Real.exp (t * W (i + 1) ω)
  let G := s.indicator P
  have hPsm : StronglyMeasurable[𝒢 i] P := hMsm i
  have hQmeas : Measurable Q :=
    Real.continuous_exp.measurable.comp (measurable_const.mul (hWsm (i + 1)).measurable)
  have hGsm : StronglyMeasurable[𝒢 i] G := hPsm.indicator hs
  have hGmeas : Measurable G := (hGsm.mono (𝒢.le i)).measurable
  have hQG : Q ⟂ᵢ[μ] G := by
    have hbase := hWindep.indep_comap_natural_of_lt hWsm (Nat.lt_succ_self i)
    apply indep_of_indep_of_le hbase
    · exact measurable_iff_comap_le.1 <|
        (Real.continuous_exp.measurable.comp (measurable_const.mul (comap_measurable _)))
    · exact measurable_iff_comap_le.1 hGsm.measurable
  have hfactor : ∫ ω, Q ω * G ω ∂μ = (∫ ω, Q ω ∂μ) * ∫ ω, G ω ∂μ :=
    hQG.integral_fun_mul_eq_mul_integral hQmeas.aestronglyMeasurable
      hGmeas.aestronglyMeasurable
  have hGnonneg : 0 ≤ ∫ ω, G ω ∂μ := by
    apply integral_nonneg
    intro ω
    exact Set.indicator_nonneg (fun _ _ ↦ (Real.exp_pos _).le) _
  have hnext : s.indicator (M (i + 1)) = fun ω ↦ G ω * Q ω := by
    funext ω
    by_cases hω : ω ∈ s
    · simp only [G, Q, P, M, Set.indicator_of_mem hω, Finset.sum_range_succ]
      rw [← Real.exp_add]
      congr 1
      ring
    · simp [G, hω]
  calc
    ∫ ω in s, M i ω ∂μ = ∫ ω, G ω ∂μ := by
      simpa only [G, P] using (integral_indicator (μ := μ) hs0).symm
    _ = (∫ ω, G ω ∂μ) * 1 := by ring
    _ ≤ (∫ ω, G ω ∂μ) * ∫ ω, Q ω ∂μ :=
      mul_le_mul_of_nonneg_left (hlower (i + 1)) hGnonneg
    _ = ∫ ω, G ω * Q ω ∂μ := by
      rw [mul_comm, ← hfactor]
      apply integral_congr_ae
      filter_upwards with ω
      ring
    _ = ∫ ω, s.indicator (M (i + 1)) ω ∂μ := by rw [hnext]
    _ = ∫ ω in s, M (i + 1) ω ∂μ := integral_indicator hs0

private lemma lil_submartingale_maximal_measure_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℕ _} {M : ℕ → Ω → ℝ}
    (hM : Submartingale M 𝒢 μ) (hMnonneg : 0 ≤ M) {ε : ℝ≥0} (hε : ε ≠ 0)
    (n : ℕ) {B : ℝ} (hB : ∫ ω, M n ω ∂μ ≤ B) :
    μ {ω | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ M k ω} ≤
      ENNReal.ofReal B / ε := by
  refine (ENNReal.le_div_iff_mul_le (Or.inl ?_) (Or.inl ?_)).2 ?_
  · exact_mod_cast hε
  · simp
  rw [mul_comm]
  refine (MeasureTheory.maximal_ineq hM hMnonneg n).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact (setIntegral_le_integral (hM.integrable n)
    (Filter.Eventually.of_forall fun ω ↦ hMnonneg n ω)).trans hB

private lemma lil_centered_maximal_measure_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ) (hMean : ∫ ω, X 0 ω ∂μ = 0)
    (hVar : Var[X 0; μ] = 1) {δ t ρ a : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {n : ℕ} (hn : 0 < n)
    (htCut : ∀ j ∈ Finset.range n, t * (2 * lilCut δ j) ≤ ρ) :
    μ {ω | Real.exp (t * a) ≤
        (Finset.range n).sup' (Finset.nonempty_range_iff.mpr hn.ne') fun k ↦
          Real.exp (t * ∑ j ∈ Finset.range (k + 1), lilCentered μ X δ j ω)} ≤
      ENNReal.ofReal (Real.exp
        ((n : ℝ) * ((1 : ℝ) / 2 + 2 * ρ / 9) * t ^ 2 - t * a)) := by
  let W := lilCentered μ X δ
  let M := fun i ω ↦ Real.exp (t * ∑ j ∈ Finset.range (i + 1), W j ω)
  let ε : ℝ≥0 := ⟨Real.exp (t * a), (Real.exp_pos _).le⟩
  have hsub : Submartingale M (Filtration.natural W fun j ↦
      (lilCentered_measurable X hMeas δ j).stronglyMeasurable) μ := by
    exact lil_exp_partial_sum_submartingale
      (C := fun j ↦ 2 * lilCut δ j)
      (fun j ↦ (lilCentered_measurable X hMeas δ j).stronglyMeasurable)
      (lilCentered_iIndep X hIndep δ)
      (fun j ω ↦ lilCentered_abs_le X hδ j ω) ht
      (lil_one_le_centered_mgf X hMeas hδ ht)
  have hmgf : ∫ ω, M (n - 1) ω ∂μ ≤
      Real.exp ((n : ℝ) * ((1 : ℝ) / 2 + 2 * ρ / 9) * t ^ 2) := by
    simpa only [M, W, Nat.sub_add_cancel hn] using
      lil_centered_sum_mgf_le X hMeas hIndep hIdent hMemLp hMean hVar
        hδ ht hρ hρ1 htCut
  have hmax := lil_submartingale_maximal_measure_le hsub
    (fun _ _ ↦ (Real.exp_pos _).le)
    (show ε ≠ 0 by exact ne_of_gt (Real.exp_pos (t * a))) (n - 1) hmgf
  simp only [M, W, Nat.sub_add_cancel hn] at hmax
  change μ {ω | Real.exp (t * a) ≤
      (Finset.range n).sup' (Finset.nonempty_range_iff.mpr hn.ne') fun k ↦
        Real.exp (t * ∑ j ∈ Finset.range (k + 1), lilCentered μ X δ j ω)} ≤
    ENNReal.ofReal (Real.exp
      ((n : ℝ) * ((1 : ℝ) / 2 + 2 * ρ / 9) * t ^ 2)) / (ε : ℝ≥0∞) at hmax
  rw [show (ε : ℝ≥0∞) = ENNReal.ofReal (Real.exp (t * a)) by
      rw [ENNReal.coe_nnreal_eq]
      rfl,
    ← ENNReal.ofReal_div_of_pos (Real.exp_pos (t * a)), ← Real.exp_sub] at hmax
  exact hmax

private def lilGrid (q r k : ℕ) : ℕ :=
  (q + r) * 2 ^ k

private noncomputable def lilUpperC (q : ℕ) : ℝ :=
  1 + 4 / (q : ℝ)

private noncomputable def lilUpperRho (q : ℕ) : ℝ :=
  1 / (q : ℝ)

private noncomputable def lilUpperDelta (q : ℕ) : ℝ :=
  1 / (100 * (q : ℝ))

private noncomputable def lilUpperA (q : ℕ) : ℝ :=
  1 / 2 + 2 * lilUpperRho q / 9

private noncomputable def lilUpperT (q r k : ℕ) : ℝ :=
  lilUpperC q * lilScale (lilGrid q r k) /
    (2 * lilUpperA q * (lilGrid q (r + 1) k : ℝ))

private lemma lilGrid_pos {q : ℕ} (hq : 0 < q) (r k : ℕ) :
    0 < lilGrid q r k := by
  rw [lilGrid]
  positivity

private lemma lilGrid_mono_r (q k : ℕ) : Monotone fun r ↦ lilGrid q r k := by
  intro r s hrs
  change (q + r) * 2 ^ k ≤ (q + s) * 2 ^ k
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_left hrs q)

private lemma lilGrid_tendsto_atTop {q r : ℕ} (hq : 0 < q) :
    Filter.Tendsto (lilGrid q r) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono (f := fun k : ℕ ↦ 2 ^ k)
  · intro k
    rw [lilGrid]
    exact Nat.le_mul_of_pos_left _ (by omega)
  · exact tendsto_pow_atTop_atTop_of_one_lt one_lt_two

private lemma lilUpperT_nonneg {q : ℕ} (hq : 0 < q) (r k : ℕ) :
    0 ≤ lilUpperT q r k := by
  rw [lilUpperT]
  apply div_nonneg
  · exact mul_nonneg (by rw [lilUpperC]; positivity) (lilScale_nonneg _)
  · apply mul_nonneg
    · rw [lilUpperA, lilUpperRho]
      positivity
    · positivity

private lemma lilUpperT_tendsto_zero {q : ℕ} (hq : 0 < q) (r : ℕ) :
    Filter.Tendsto (lilUpperT q r) Filter.atTop (nhds 0) := by
  have hend := lilGrid_tendsto_atTop (r := r + 1) hq
  have hscale := lil_scale_div_tendsto_zero.comp hend
  have hconst : 0 ≤ lilUpperC q / (2 * lilUpperA q) := by
    rw [lilUpperC, lilUpperA, lilUpperRho]
    positivity
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun k ↦ lilUpperT_nonneg hq r k
  · change ∀ᶠ k : ℕ in Filter.atTop, lilUpperT q r k ≤
        (lilUpperC q / (2 * lilUpperA q)) *
          (lilScale (lilGrid q (r + 1) k) / (lilGrid q (r + 1) k : ℝ))
    exact Filter.Eventually.of_forall fun k ↦ by
      rw [lilUpperT]
      have hs := lilScale_monotone (lilGrid_mono_r q k (Nat.le_succ r))
      have hend0 : (0 : ℝ) < lilGrid q (r + 1) k := by
        exact_mod_cast lilGrid_pos hq (r + 1) k
      calc
        lilUpperC q * lilScale (lilGrid q r k) /
            (2 * lilUpperA q * (lilGrid q (r + 1) k : ℝ)) =
            (lilUpperC q / (2 * lilUpperA q)) *
              (lilScale (lilGrid q r k) / (lilGrid q (r + 1) k : ℝ)) := by ring
        _ ≤ (lilUpperC q / (2 * lilUpperA q)) *
              (lilScale (lilGrid q (r + 1) k) /
                (lilGrid q (r + 1) k : ℝ)) := by
            gcongr
        _ = _ := rfl
  · simpa using hscale.const_mul (lilUpperC q / (2 * lilUpperA q))

private lemma lil_upper_numeric {q : ℕ} (hq : 0 < q) :
    (1 + 1 / (q : ℝ)) ^ 2 * (2 * lilUpperA q) ≤ lilUpperC q ^ 2 := by
  rw [lilUpperA, lilUpperRho, lilUpperC]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  field_simp [hq0.ne']
  nlinarith [show (q : ℝ) ≥ 1 by exact_mod_cast hq]

private lemma lil_upper_cut_numeric {q : ℕ} (hq : 0 < q) :
    (lilUpperC q / lilUpperA q) *
        (lilUpperDelta q * Real.sqrt 2) ≤ lilUpperRho q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  rw [lilUpperC, lilUpperA, lilUpperRho, lilUpperDelta]
  field_simp [hq0.ne']
  nlinarith [show (q : ℝ) ≥ 1 by exact_mod_cast hq]

private lemma lil_upper_cut_pred_le {q : ℕ} (hq : 0 < q) (r k : ℕ) :
    lilUpperT q r k *
        (2 * lilCut (lilUpperDelta q) (lilGrid q (r + 1) k - 1)) ≤
      lilUpperRho q := by
  have hend : 0 < lilGrid q (r + 1) k := lilGrid_pos hq (r + 1) k
  have hend0 : (0 : ℝ) < lilGrid q (r + 1) k := by exact_mod_cast hend
  have hCA : 0 ≤ lilUpperC q / lilUpperA q := by
    rw [lilUpperC, lilUpperA, lilUpperRho]
    positivity
  have hs := lilScale_monotone (lilGrid_mono_r q k (Nat.le_succ r))
  calc
    lilUpperT q r k *
        (2 * lilCut (lilUpperDelta q) (lilGrid q (r + 1) k - 1)) =
        (lilUpperC q / lilUpperA q) *
          (lilScale (lilGrid q r k) / (lilGrid q (r + 1) k : ℝ) *
            lilCut (lilUpperDelta q) (lilGrid q (r + 1) k - 1)) := by
      rw [lilUpperT]
      field_simp
    _ ≤ (lilUpperC q / lilUpperA q) *
          (lilScale (lilGrid q (r + 1) k) / (lilGrid q (r + 1) k : ℝ) *
            lilCut (lilUpperDelta q) (lilGrid q (r + 1) k - 1)) := by
      gcongr
      rw [lilCut, lilUpperDelta]
      positivity
    _ = (lilUpperC q / lilUpperA q) *
        (lilUpperDelta q * Real.sqrt 2) := by
      rw [lil_scale_div_mul_cut_pred hend]
    _ ≤ lilUpperRho q := lil_upper_cut_numeric hq

private lemma lil_upper_cut_condition {q : ℕ} (hq : 0 < q) (r : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ j ∈ Finset.range (lilGrid q (r + 1) k),
      lilUpperT q r k * (2 * lilCut (lilUpperDelta q) j) ≤ lilUpperRho q := by
  have hδ : 0 ≤ lilUpperDelta q := by
    rw [lilUpperDelta]
    positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (lilCut_eventually_mono hδ)
  have hρ : 0 < lilUpperRho q := by
    rw [lilUpperRho]
    positivity
  have hearly : ∀ᶠ k : ℕ in Filter.atTop, ∀ j ∈ Finset.range N,
      lilUpperT q r k * (2 * lilCut (lilUpperDelta q) j) ≤ lilUpperRho q := by
    refine (Finset.eventually_all (Finset.range N)).2 ?_
    intro j hj
    have ht : Filter.Tendsto
        (fun k ↦ lilUpperT q r k * (2 * lilCut (lilUpperDelta q) j))
        Filter.atTop (nhds 0) := by
      simpa using (lilUpperT_tendsto_zero hq r).mul_const
        (2 * lilCut (lilUpperDelta q) j)
    filter_upwards [(tendsto_order.1 ht).2 (lilUpperRho q) hρ] with k hk
    exact hk.le
  filter_upwards [hearly] with k hk j hj
  by_cases hjN : j < N
  · exact hk j (Finset.mem_range.2 hjN)
  · have hNj : N ≤ j := Nat.le_of_not_gt hjN
    have hjend : j < lilGrid q (r + 1) k := Finset.mem_range.1 hj
    have hjpred : j ≤ lilGrid q (r + 1) k - 1 := Nat.le_sub_one_of_lt hjend
    have hcut := hN j hNj (lilGrid q (r + 1) k - 1) hjpred
    calc
      lilUpperT q r k * (2 * lilCut (lilUpperDelta q) j) ≤
          lilUpperT q r k *
            (2 * lilCut (lilUpperDelta q) (lilGrid q (r + 1) k - 1)) := by
        gcongr
        exact lilUpperT_nonneg hq r k
      _ ≤ lilUpperRho q := lil_upper_cut_pred_le hq r k

private lemma lil_upper_exponent_le {q : ℕ} (hq : 0 < q) (r k : ℕ) :
    (lilGrid q (r + 1) k : ℝ) * lilUpperA q * lilUpperT q r k ^ 2 -
        lilUpperT q r k * (lilUpperC q * lilScale (lilGrid q r k)) ≤
      -(1 + 1 / (q : ℝ)) * lilLog (lilGrid q r k) := by
  let s := lilGrid q r k
  let e := lilGrid q (r + 1) k
  let c := lilUpperC q
  let A := lilUpperA q
  let p := 1 + 1 / (q : ℝ)
  have hs : 0 < s := lilGrid_pos hq r k
  have he : 0 < e := lilGrid_pos hq (r + 1) k
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hA : 0 < A := by
    dsimp only [A]
    rw [lilUpperA, lilUpperRho]
    positivity
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  have heratio : (e : ℝ) ≤ p * (s : ℝ) := by
    dsimp only [e, s, p]
    rw [lilGrid, lilGrid]
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    push_cast
    field_simp [hq0.ne']
    nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ k by positivity]
  have hcoef : p * (2 * A) * (e : ℝ) ≤ c ^ 2 * (s : ℝ) := by
    have hnum : p ^ 2 * (2 * A) ≤ c ^ 2 := by
      simpa only [p, A, c] using lil_upper_numeric hq
    calc
      p * (2 * A) * (e : ℝ) ≤ p * (2 * A) * (p * (s : ℝ)) := by
        gcongr
      _ = (p ^ 2 * (2 * A)) * (s : ℝ) := by ring
      _ ≤ c ^ 2 * (s : ℝ) := by gcongr
  have hL : 0 < lilLog s := zero_lt_one.trans_le (lilLog_one_le s)
  have hscale : lilScale s ^ 2 = 2 * (s : ℝ) * lilLog s := by
    rw [lilScale, Real.sq_sqrt]
    positivity
  have hexact : (e : ℝ) * A * lilUpperT q r k ^ 2 -
      lilUpperT q r k * (c * lilScale s) =
      -(c * lilScale s) ^ 2 / (4 * A * (e : ℝ)) := by
    rw [lilUpperT]
    change (e : ℝ) * A * (c * lilScale s / (2 * A * (e : ℝ))) ^ 2 -
      (c * lilScale s / (2 * A * (e : ℝ))) * (c * lilScale s) = _
    field_simp [hA.ne', he0.ne']
    ring
  change (e : ℝ) * A * lilUpperT q r k ^ 2 -
      lilUpperT q r k * (c * lilScale s) ≤ -p * lilLog s
  rw [hexact, neg_div]
  have hrhs : -p * lilLog s = -(p * lilLog s) := by ring
  rw [hrhs, neg_le_neg_iff]
  apply (le_div_iff₀ (by positivity : 0 < 4 * A * (e : ℝ))).2
  rw [mul_assoc]
  nlinarith [mul_le_mul_of_nonneg_right hcoef (show 0 ≤ 2 * lilLog s by positivity)]

private def lilUpperBad
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (q r k : ℕ) : Set Ω :=
  {ω | ∃ i ∈ Finset.range (lilGrid q (r + 1) k),
    lilUpperC q * lilScale (lilGrid q r k) ≤
      ∑ j ∈ Finset.range (i + 1), lilCentered μ X (lilUpperDelta q) j ω}

private lemma lilUpperBad_measurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (X : ℕ → Ω → ℝ)
    (hMeas : ∀ j, Measurable (X j)) (q r k : ℕ) :
    MeasurableSet (lilUpperBad μ X q r k) := by
  rw [lilUpperBad]
  rw [show {ω | ∃ i ∈ Finset.range (lilGrid q (r + 1) k),
      lilUpperC q * lilScale (lilGrid q r k) ≤
        ∑ j ∈ Finset.range (i + 1), lilCentered μ X (lilUpperDelta q) j ω} =
      ⋃ i ∈ (Finset.range (lilGrid q (r + 1) k) : Set ℕ),
        {ω | lilUpperC q * lilScale (lilGrid q r k) ≤
          ∑ j ∈ Finset.range (i + 1), lilCentered μ X (lilUpperDelta q) j ω} by
    ext ω
    simp]
  apply MeasurableSet.biUnion (Finset.countable_toSet _)
  intro i hi
  exact measurableSet_le measurable_const <|
    Finset.measurable_fun_sum _ fun j _ ↦ lilCentered_measurable X hMeas _ j

private lemma lil_upper_bad_measure_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ) (hMean : ∫ ω, X 0 ω ∂μ = 0)
    (hVar : Var[X 0; μ] = 1) {q : ℕ} (hq : 0 < q) (r : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      μ (lilUpperBad μ X q r k) ≤ ENNReal.ofReal (Real.exp
        (-(1 + 1 / (q : ℝ)) * lilLog (lilGrid q r k))) := by
  filter_upwards [lil_upper_cut_condition hq r] with k hcut
  have hδ : 0 ≤ lilUpperDelta q := by
    rw [lilUpperDelta]
    positivity
  have ht : 0 ≤ lilUpperT q r k := lilUpperT_nonneg hq r k
  have hρ : 0 ≤ lilUpperRho q := by
    rw [lilUpperRho]
    positivity
  have hρ1 : lilUpperRho q ≤ 1 := by
    rw [lilUpperRho]
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    exact (div_le_iff₀ (show (0 : ℝ) < q by exact_mod_cast hq)).2 (by simpa using hq1)
  have hn : 0 < lilGrid q (r + 1) k := lilGrid_pos hq (r + 1) k
  let E : Set Ω := {ω | Real.exp (lilUpperT q r k *
      (lilUpperC q * lilScale (lilGrid q r k))) ≤
    (Finset.range (lilGrid q (r + 1) k)).sup'
      (Finset.nonempty_range_iff.mpr hn.ne') fun i ↦
        Real.exp (lilUpperT q r k *
          ∑ j ∈ Finset.range (i + 1), lilCentered μ X (lilUpperDelta q) j ω)}
  have hmax : μ E ≤ ENNReal.ofReal (Real.exp
      ((lilGrid q (r + 1) k : ℝ) *
          ((1 : ℝ) / 2 + 2 * lilUpperRho q / 9) * lilUpperT q r k ^ 2 -
        lilUpperT q r k * (lilUpperC q * lilScale (lilGrid q r k)))) := by
    simpa only [E] using lil_centered_maximal_measure_le X hMeas hIndep hIdent hMemLp
      hMean hVar hδ ht hρ hρ1 hn hcut
  have hsubset : lilUpperBad μ X q r k ⊆ E := by
    intro ω hω
    rcases hω with ⟨i, hi, hsum⟩
    have hexp : Real.exp (lilUpperT q r k *
        (lilUpperC q * lilScale (lilGrid q r k))) ≤
        Real.exp (lilUpperT q r k *
          ∑ j ∈ Finset.range (i + 1), lilCentered μ X (lilUpperDelta q) j ω) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum ht)
    exact hexp.trans (Finset.le_sup'
      (fun i ↦ Real.exp (lilUpperT q r k *
        ∑ j ∈ Finset.range (i + 1), lilCentered μ X (lilUpperDelta q) j ω)) hi)
  calc
    μ (lilUpperBad μ X q r k) ≤ μ E := measure_mono hsubset
    _ ≤ ENNReal.ofReal (Real.exp
        ((lilGrid q (r + 1) k : ℝ) * lilUpperA q * lilUpperT q r k ^ 2 -
          lilUpperT q r k * (lilUpperC q * lilScale (lilGrid q r k)))) := by
      simpa only [lilUpperA] using hmax
    _ ≤ ENNReal.ofReal (Real.exp
        (-(1 + 1 / (q : ℝ)) * lilLog (lilGrid q r k))) := by
      exact ENNReal.ofReal_le_ofReal <| Real.exp_le_exp.mpr (lil_upper_exponent_le hq r k)

private lemma lil_upper_exp_bound_summable {q : ℕ} (hq : 0 < q) (r : ℕ) :
    Summable (fun k : ℕ ↦ Real.exp
      (-(1 + 1 / (q : ℝ)) * lilLog (lilGrid q r k))) := by
  let p : ℝ := 1 + 1 / (q : ℝ)
  let C : ℝ := Real.exp (-p * Real.log (Real.log 2))
  have hp : 1 < p := by
    dsimp only [p]
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    linarith [one_div_pos.mpr hq0]
  have hg : Summable (fun k : ℕ ↦ C * (k : ℝ) ^ (-p)) := by
    exact ((Real.summable_nat_rpow).2 (neg_lt_neg hp)).mul_left C
  apply hg.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop 2] with k hk
  have hk0 : (0 : ℝ) < k := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hstart3 : 3 ≤ lilGrid q r k := by
    rw [lilGrid]
    have hqr : 1 ≤ q + r := by omega
    have hkpow : 4 ≤ 2 ^ k := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    nlinarith
  have hpow : (k : ℝ) * Real.log 2 ≤ Real.log (lilGrid q r k : ℝ) := by
    have hgrid : (2 : ℝ) ^ k ≤ (lilGrid q r k : ℝ) := by
      rw [lilGrid]
      push_cast
      have hqr : (1 : ℝ) ≤ q + r := by exact_mod_cast (show 1 ≤ q + r by omega)
      nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ k by positivity]
    calc
      (k : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ k) := by
        rw [Real.log_pow]
      _ ≤ Real.log (lilGrid q r k : ℝ) := Real.log_le_log (by positivity) hgrid
  have hloglog : Real.log ((k : ℝ) * Real.log 2) ≤
      lilLog (lilGrid q r k) := by
    rw [lilLog, Nat.max_eq_left hstart3]
    exact (Real.log_le_log (mul_pos hk0 hlog2) hpow).trans (le_max_right _ _)
  have hmain : Real.exp (-p * lilLog (lilGrid q r k)) ≤
      C * (k : ℝ) ^ (-p) := by
    calc
      Real.exp (-p * lilLog (lilGrid q r k)) ≤
          Real.exp (-p * Real.log ((k : ℝ) * Real.log 2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = C * (k : ℝ) ^ (-p) := by
        rw [Real.log_mul hk0.ne' hlog2.ne', Real.rpow_def_of_pos hk0]
        rw [← Real.exp_add]
        congr 1
        ring
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hmain

private lemma lil_upper_bad_tsum_ne_top
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ) (hMean : ∫ ω, X 0 ω ∂μ = 0)
    (hVar : Var[X 0; μ] = 1) {q : ℕ} (hq : 0 < q) (r : ℕ) :
    ∑' k, μ (lilUpperBad μ X q r k) ≠ ∞ := by
  let f := fun k : ℕ ↦ Real.exp
    (-(1 + 1 / (q : ℝ)) * lilLog (lilGrid q r k))
  let g := fun k : ℕ ↦
    (⟨μ.real (lilUpperBad μ X q r k), measureReal_nonneg⟩ : ℝ≥0)
  have hf : Summable f := lil_upper_exp_bound_summable hq r
  have hgreal : Summable (fun k ↦ (g k : ℝ)) := by
    apply hf.of_norm_bounded_eventually
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [lil_upper_bad_measure_le X hMeas hIndep hIdent hMemLp hMean hVar hq r]
      with k hk
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    simpa only [Measure.real, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hk
  rw [show (fun k ↦ μ (lilUpperBad μ X q r k)) =
      fun k ↦ ENNReal.ofReal (μ.real (lilUpperBad μ X q r k)) by
    funext k
    exact (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm]
  simpa only [g] using hgreal.tsum_ofReal_ne_top

private lemma lil_grid_cover {q K n : ℕ} (hq : 0 < q) (hn : q * 2 ^ K ≤ n) :
    ∃ k ≥ K, ∃ r < q,
      lilGrid q r k ≤ n ∧ n < lilGrid q (r + 1) k := by
  let d := n / q
  let k := Nat.log 2 d
  let step := 2 ^ k
  have hqn : q ≤ n := by
    exact le_trans (by simpa using Nat.le_mul_of_pos_right q (pow_pos (by omega) K)) hn
  have hd : 0 < d := by
    dsimp only [d]
    exact Nat.div_pos hqn hq
  have hstep : 0 < step := by
    dsimp only [step]
    positivity
  have hstepd : step ≤ d := by
    exact Nat.pow_log_le_self 2 hd.ne'
  have hdupper : d < 2 ^ (k + 1) := by
    exact Nat.lt_pow_succ_log_self one_lt_two d
  have hKd : 2 ^ K ≤ d := by
    apply (Nat.le_div_iff_mul_le hq).2
    simpa [Nat.mul_comm] using hn
  have hKk : K ≤ k := Nat.le_log_of_pow_le one_lt_two hKd
  have hlower : q * step ≤ n := by
    calc
      q * step ≤ q * d := Nat.mul_le_mul_left q hstepd
      _ = d * q := Nat.mul_comm _ _
      _ ≤ n := Nat.div_mul_le_self n q
  have hupper : n < 2 * q * step := by
    calc
      n < q * (d + 1) := Nat.lt_mul_div_succ n hq
      _ ≤ q * 2 ^ (k + 1) := Nat.mul_le_mul_left q (Nat.succ_le_iff.mpr hdupper)
      _ = 2 * q * step := by simp [step, pow_succ]; ring
  let r := n / step - q
  have hqdiv : q ≤ n / step := by
    exact (Nat.le_div_iff_mul_le hstep).2 (by simpa [Nat.mul_comm] using hlower)
  have hdiv2q : n / step < 2 * q := by
    exact (Nat.div_lt_iff_lt_mul hstep).2 (by simpa [Nat.mul_comm, mul_assoc] using hupper)
  have hr : r < q := by
    dsimp only [r]
    omega
  refine ⟨k, hKk, r, hr, ?_, ?_⟩
  · rw [lilGrid]
    have hqr : q + r = n / step := by
      dsimp only [r]
      omega
    rw [hqr]
    exact Nat.div_mul_le_self n step
  · rw [lilGrid]
    have hqr : q + (r + 1) = n / step + 1 := by
      dsimp only [r]
      omega
    rw [hqr]
    simpa [Nat.mul_comm] using Nat.lt_mul_div_succ n hstep

private lemma lil_ae_centered_eventually_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ) (hMean : ∫ ω, X 0 ω ∂μ = 0)
    (hVar : Var[X 0; μ] = 1) {q : ℕ} (hq : 0 < q) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in Filter.atTop,
      (∑ j ∈ Finset.range n, lilCentered μ X (lilUpperDelta q) j ω) ≤
        lilUpperC q * lilScale n := by
  have hae : ∀ᵐ ω ∂μ, ∀ r : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
      ω ∉ lilUpperBad μ X q r k := by
    rw [ae_all_iff]
    intro r
    exact ae_eventually_notMem <|
      lil_upper_bad_tsum_ne_top X hMeas hIndep hIdent hMemLp hMean hVar hq r
  filter_upwards [hae] with ω hω
  have hall : ∀ᶠ k : ℕ in Filter.atTop, ∀ r ∈ Finset.range q,
      ω ∉ lilUpperBad μ X q r k := by
    refine (Finset.eventually_all (Finset.range q)).2 ?_
    intro r hr
    exact hω r
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hall
  filter_upwards [Filter.eventually_ge_atTop (q * 2 ^ K)] with n hn
  obtain ⟨k, hkK, r, hrq, hstart, hend⟩ := lil_grid_cover hq hn
  have hn0 : 0 < n := lt_of_lt_of_le (lilGrid_pos hq r k) hstart
  have hnot := hK k hkK r (Finset.mem_range.2 hrq)
  have hsum : (∑ j ∈ Finset.range n,
      lilCentered μ X (lilUpperDelta q) j ω) <
      lilUpperC q * lilScale (lilGrid q r k) := by
    apply lt_of_not_ge
    intro hge
    apply hnot
    refine ⟨n - 1, Finset.mem_range.2 ?_, ?_⟩
    · exact (Nat.sub_lt hn0 (by omega)).trans hend
    · simpa only [Nat.sub_add_cancel hn0] using hge
  exact hsum.le.trans <| mul_le_mul_of_nonneg_left (lilScale_monotone hstart) <| by
    rw [lilUpperC]
    positivity

private lemma lil_sum_decomposition
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hInt : Integrable (X 0) μ) (hMean : ∫ ω, X 0 ω ∂μ = 0)
    (δ : ℝ) (n : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range n, X j ω) =
      (∑ j ∈ Finset.range n, lilCentered μ X δ j ω) +
      (∑ j ∈ Finset.range n, lilRemainder X δ j ω) -
      ∑ j ∈ Finset.range n, ∫ x, lilRemainder X δ j x ∂μ := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hXj : Integrable (X j) μ := (hIdent j).integrable_iff.mpr hInt
  have hR : ∫ x, lilRemainder X δ j x ∂μ =
      -(∫ x, lilTruncated X δ j x ∂μ) := by
    change (∫ x, X j x - lilTruncated X δ j x ∂μ) = _
    rw [integral_sub hXj (lilTruncated_integrable X hMeas δ j),
      (hIdent j).integral_eq, hMean]
    ring
  change X j ω =
    (lilTruncated X δ j ω - ∫ x, lilTruncated X δ j x ∂μ) +
      (X j ω - lilTruncated X δ j ω) - ∫ x, lilRemainder X δ j x ∂μ
  rw [hR]
  ring

private lemma lil_ae_eventually_sum_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hInt : Integrable (X 0) μ) (hMemLp : MemLp (X 0) 2 μ)
    (hMean : ∫ ω, X 0 ω ∂μ = 0) (hVar : Var[X 0; μ] = 1)
    {q : ℕ} (hq : 0 < q) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in Filter.atTop,
      (∑ j ∈ Finset.range n, X j ω) / lilScale n ≤
        1 + 6 / (q : ℝ) := by
  have hδ : 0 < lilUpperDelta q := by
    rw [lilUpperDelta]
    positivity
  have hmeanRem := lil_mean_remainder_tendsto X hMeas hIdent hInt hMemLp hδ
  have hmeanSmall : ∀ᶠ n : ℕ in Filter.atTop,
      |(∑ j ∈ Finset.range n, ∫ ω, lilRemainder X (lilUpperDelta q) j ω ∂μ) /
        lilScale n| < 1 / (q : ℝ) := by
    have habs : Filter.Tendsto
        (fun n ↦ |(∑ j ∈ Finset.range n,
          ∫ ω, lilRemainder X (lilUpperDelta q) j ω ∂μ) / lilScale n|)
        Filter.atTop (nhds 0) := by simpa using hmeanRem.abs
    exact (tendsto_order.1 habs).2 _ (one_div_pos.mpr <| by exact_mod_cast hq)
  filter_upwards [lil_ae_centered_eventually_le X hMeas hIndep hIdent hMemLp hMean hVar hq,
    lil_ae_remainder_tendsto X hMeas hIdent hInt hMemLp hδ] with ω hcenter hrem
  have hremSmall : ∀ᶠ n : ℕ in Filter.atTop,
      |(∑ j ∈ Finset.range n, lilRemainder X (lilUpperDelta q) j ω) / lilScale n| <
        1 / (q : ℝ) := by
    have habs : Filter.Tendsto
        (fun n ↦ |(∑ j ∈ Finset.range n,
          lilRemainder X (lilUpperDelta q) j ω) / lilScale n|)
        Filter.atTop (nhds 0) := by simpa using hrem.abs
    exact (tendsto_order.1 habs).2 _ (one_div_pos.mpr <| by exact_mod_cast hq)
  filter_upwards [hcenter, hremSmall, hmeanSmall, Filter.eventually_gt_atTop 0]
    with n hcenterN hremN hmeanN hn
  have hscale : 0 < lilScale n := by
    rw [lilScale]
    apply Real.sqrt_pos.2
    exact mul_pos (mul_pos zero_lt_two (by exact_mod_cast hn))
      (zero_lt_one.trans_le (lilLog_one_le n))
  have hcenterDiv :
      (∑ j ∈ Finset.range n, lilCentered μ X (lilUpperDelta q) j ω) / lilScale n ≤
        lilUpperC q := (div_le_iff₀ hscale).2 hcenterN
  rw [lil_sum_decomposition X hMeas hIdent hInt hMean (lilUpperDelta q) n ω,
    sub_div, add_div]
  rw [lilUpperC] at hcenterDiv
  have hremLe := (le_abs_self ((∑ j ∈ Finset.range n,
    lilRemainder X (lilUpperDelta q) j ω) / lilScale n)).trans hremN.le
  have hmeanLe := (neg_le_abs ((∑ j ∈ Finset.range n,
    ∫ x, lilRemainder X (lilUpperDelta q) j x ∂μ) / lilScale n)).trans hmeanN.le
  have hfrac : 4 / (q : ℝ) + 1 / (q : ℝ) + 1 / (q : ℝ) = 6 / (q : ℝ) := by ring
  nlinarith

private lemma lil_gaussian_tail_lower {y : ℝ} (hy : 1 ≤ y) :
    (Real.sqrt (2 * Real.pi))⁻¹ * (1 / y) *
        Real.exp (-((y + 1 / y) ^ 2) / 2) ≤
      (gaussianReal 0 1).real (Set.Ioi y) := by
  let z := y + 1 / y
  let c := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2)
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hz : 0 < z := by
    dsimp only [z]
    positivity
  have hpdf : ∫ x in Set.Ioc y z, c ≤
      ∫ x in Set.Ioc y z, gaussianPDFReal 0 1 x := by
    apply integral_mono_ae (μ := volume.restrict (Set.Ioc y z))
      (integrableOn_const (μ := volume) (s := Set.Ioc y z) (C := c) (by simp))
      (integrable_gaussianPDFReal 0 1).integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 ≤ x := le_trans hy0.le hx.1.le
    have hsq : x ^ 2 ≤ z ^ 2 := (sq_le_sq₀ hx0 hz.le).2 hx.2
    dsimp only [c]
    rw [gaussianPDFReal]
    norm_num
    gcongr
  have hinterval : ∫ x in Set.Ioc y z, c =
      (1 / y) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2)) := by
    rw [setIntegral_const]
    simp only [Measure.real, Real.volume_Ioc, smul_eq_mul]
    have : z - y = 1 / y := by simp [z]
    rw [this]
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hsubset : Set.Ioc y z ⊆ Set.Ioi y := fun _ hx ↦ hx.1
  have hset : ∫ x in Set.Ioc y z, gaussianPDFReal 0 1 x ≤
      ∫ x in Set.Ioi y, gaussianPDFReal 0 1 x :=
    setIntegral_mono_set (integrable_gaussianPDFReal 0 1).integrableOn
      (Filter.Eventually.of_forall fun x ↦ gaussianPDFReal_nonneg 0 1 x)
      (Filter.Eventually.of_forall hsubset)
  have hgauss : (gaussianReal 0 1).real (Set.Ioi y) =
      ∫ x in Set.Ioi y, gaussianPDFReal 0 1 x := by
    rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
    exact ENNReal.toReal_ofReal (integral_nonneg fun x ↦ gaussianPDFReal_nonneg 0 1 x)
  rw [hgauss]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * (1 / y) *
        Real.exp (-((y + 1 / y) ^ 2) / 2) = ∫ x in Set.Ioc y z, c := by
      rw [hinterval]
      dsimp only [z, c]
      ring
    _ ≤ _ := hpdf.trans hset

private lemma lil_gaussian_tail_exp_lower {η y : ℝ} (hy : 1 ≤ y)
    (hlarge : 6 * Real.exp (3 / 2) ≤ η * y) :
    Real.exp (-(1 + η) * y ^ 2 / 2) ≤ (gaussianReal 0 1).real (Set.Ioi y) := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hpi : 2 * Real.pi ≤ 8 := by nlinarith [Real.pi_le_four]
  have hsqrtpos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 <| by positivity
  have hsqrtle : Real.sqrt (2 * Real.pi) ≤ 3 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hK : (1 / 3 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    simpa only [one_div] using (inv_le_inv₀ (by norm_num : (0 : ℝ) < 3) hsqrtpos).2 hsqrtle
  have hinv : 1 / y ≤ 1 := (div_le_one hy0).2 hy
  have hsquare : (y + 1 / y) ^ 2 ≤ y ^ 2 + 3 := by
    have hinv0 : 0 ≤ 1 / y := by positivity
    have hinvsq : (1 / y) ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ hinv0 zero_le_one).2 hinv
    field_simp [hy0.ne'] at hinvsq ⊢
    nlinarith
  have hexpLarge : 3 * y * Real.exp (3 / 2) ≤ Real.exp (η * y ^ 2 / 2) := by
    have hpoly : 3 * y * Real.exp (3 / 2) ≤ η * y ^ 2 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hlarge hy0.le]
    exact hpoly.trans <| (le_add_of_nonneg_left zero_le_one).trans <| by
      simpa [add_comm] using Real.add_one_le_exp (η * y ^ 2 / 2)
  have hratio : 3 * y ≤ Real.exp
      (((1 + η) * y ^ 2 - (y + 1 / y) ^ 2) / 2) := by
    have hexpDiff : Real.exp (η * y ^ 2 / 2 - 3 / 2) ≤
        Real.exp (((1 + η) * y ^ 2 - (y + 1 / y) ^ 2) / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      3 * y = (3 * y * Real.exp (3 / 2)) / Real.exp (3 / 2) := by
        field_simp [Real.exp_ne_zero]
      _ ≤ Real.exp (η * y ^ 2 / 2) / Real.exp (3 / 2) := by gcongr
      _ = Real.exp (η * y ^ 2 / 2 - 3 / 2) := by rw [Real.exp_sub]
      _ ≤ _ := hexpDiff
  have hcore : Real.exp (-(1 + η) * y ^ 2 / 2) ≤
      (1 / (3 * y)) * Real.exp (-((y + 1 / y) ^ 2) / 2) := by
    rw [show (1 / (3 * y)) * Real.exp (-((y + 1 / y) ^ 2) / 2) =
        Real.exp (-((y + 1 / y) ^ 2) / 2) / (3 * y) by ring]
    apply (le_div_iff₀ (mul_pos (by norm_num) hy0)).2
    calc
      Real.exp (-(1 + η) * y ^ 2 / 2) * (3 * y) ≤
          Real.exp (-(1 + η) * y ^ 2 / 2) *
            Real.exp (((1 + η) * y ^ 2 - (y + 1 / y) ^ 2) / 2) := by
        gcongr
      _ = Real.exp (-((y + 1 / y) ^ 2) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    Real.exp (-(1 + η) * y ^ 2 / 2) ≤
        (1 / (3 * y)) * Real.exp (-((y + 1 / y) ^ 2) / 2) := hcore
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (1 / y) *
        Real.exp (-((y + 1 / y) ^ 2) / 2) := by
      gcongr
      calc
        1 / (3 * y) = (1 / 3) * (1 / y) := by ring
        _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (1 / y) := by gcongr
    _ ≤ _ := lil_gaussian_tail_lower hy

private lemma lil_clt_tail_eventually
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hMean : ∫ ω, X 0 ω ∂μ = 0) (hVar : Var[X 0; μ] = 1)
    {η a : ℝ} (ha : 1 ≤ a)
    (halarge : 6 * Real.exp (3 / 2) ≤ η * a) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (Real.exp (-(1 + η) * a ^ 2 / 2) / 2) ≤
        μ {ω | a < (Real.sqrt (n : ℝ))⁻¹ *
          ∑ j ∈ Finset.range n, X j ω} := by
  have hsq : ∫ ω, X 0 ω ^ 2 ∂μ = 1 :=
    lil_integral_sq_eq_one X (hMeas 0) hMean hVar
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum
    (P' := gaussianReal 0 1) (Y := id) (HasLaw.id) hMean hsq hIndep hIdent
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    hclt.tendsto (isOpen_Ioi : IsOpen (Set.Ioi a))
  have htailReal := lil_gaussian_tail_exp_lower ha halarge
  have htail : ENNReal.ofReal (Real.exp (-(1 + η) * a ^ 2 / 2)) ≤
      gaussianReal 0 1 (Set.Ioi a) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (gaussianReal 0 1) (Set.Ioi a))]
    exact ENNReal.ofReal_le_ofReal htailReal
  have hp : ENNReal.ofReal (Real.exp (-(1 + η) * a ^ 2 / 2) / 2) <
      ENNReal.ofReal (Real.exp (-(1 + η) * a ^ 2 / 2)) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    nlinarith [Real.exp_pos (-(1 + η) * a ^ 2 / 2)]
  have hlim : ENNReal.ofReal (Real.exp (-(1 + η) * a ^ 2 / 2) / 2) <
      Filter.liminf (fun n : ℕ ↦
        (μ.map (fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ *
          ∑ j ∈ Finset.range n, X j ω)) (Set.Ioi a)) Filter.atTop := by
    refine hp.trans_le (htail.trans ?_)
    simpa using hport
  filter_upwards [Filter.eventually_lt_of_lt_liminf hlim] with n hn
  rw [Measure.map_apply_of_aemeasurable (hclt.forall_aemeasurable n) measurableSet_Ioi] at hn
  exact hn.le

private lemma lil_shifted_sum_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (s n : ℕ) :
    IdentDistrib
      (fun ω ↦ ∑ j ∈ Finset.range n, X (s + j) ω)
      (fun ω ↦ ∑ j ∈ Finset.range n, X j ω) μ μ := by
  let F : Ω → Fin n → ℝ := fun ω i ↦ X (s + i) ω
  let G : Ω → Fin n → ℝ := fun ω i ↦ X i ω
  have hs_inj : Function.Injective (fun i : Fin n ↦ s + (i : ℕ)) := by
    intro i j hij
    exact Fin.ext (Nat.add_left_cancel hij)
  have hFindep : iIndepFun (fun i : Fin n ↦ X (s + i)) μ :=
    hIndep.precomp hs_inj
  have hGindep : iIndepFun (fun i : Fin n ↦ X (i : ℕ)) μ :=
    hIndep.precomp Fin.val_injective
  have hFmap : μ.map F = Measure.pi (fun i : Fin n ↦ μ.map (X (s + i))) := by
    exact hFindep.map_fun_eq_pi_map (fun i ↦ (hMeas (s + i)).aemeasurable)
  have hGmap : μ.map G = Measure.pi (fun i : Fin n ↦ μ.map (X i)) := by
    exact hGindep.map_fun_eq_pi_map (fun i ↦ (hMeas i).aemeasurable)
  have hmarg : (fun i : Fin n ↦ μ.map (X (s + i))) =
      fun i : Fin n ↦ μ.map (X (i : ℕ)) := by
    funext i
    exact (hIdent (s + i)).map_eq.trans (hIdent i).map_eq.symm
  have hFG : IdentDistrib F G μ μ := by
    refine ⟨(show Measurable F by exact Measurable.of_eval fun i ↦ hMeas (s + i)).aemeasurable,
      (show Measurable G by exact Measurable.of_eval fun i ↦ hMeas i).aemeasurable, ?_⟩
    rw [hFmap, hGmap, hmarg]
  have hsum := hFG.comp (Finset.measurable_sum Finset.univ fun i _ ↦ measurable_pi_apply i)
  convert hsum using 1 <;> ext ω
  · simpa only [Function.comp_apply, F] using
      (Fin.sum_univ_eq_sum_range (fun j ↦ X (s + j) ω) n).symm
  · simpa only [Function.comp_apply, G] using
      (Fin.sum_univ_eq_sum_range (fun j ↦ X j ω) n).symm

private lemma lil_iIndepSet_of_disjoint_blocks
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (I : ι → Finset ℕ)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (A : ι → Set Ω)
    (hA : ∀ k, MeasurableSet[⨆ j ∈ (I k : Set ℕ),
      MeasurableSpace.comap (X j) Real.measurableSpace] (A k)) :
    iIndepSet A μ := by
  classical
  let mX : ℕ → MeasurableSpace Ω :=
    fun j ↦ MeasurableSpace.comap (X j) Real.measurableSpace
  let m : ι → MeasurableSpace Ω := fun k ↦ ⨆ j ∈ (I k : Set ℕ), mX j
  have hmX_le : ∀ j, mX j ≤ ‹MeasurableSpace Ω› := fun j ↦ by
    exact (hMeas j).comap_le
  have hmX_indep : iIndep mX μ := by
    simpa only [mX] using hIndep.iIndep
  have hm_indep : iIndep m μ := by
    rw [iIndep_iff]
    intro S f hf
    induction S using Finset.induction with
    | empty => simp
    | @insert a S ha ih =>
        let U : Set ℕ := ⋃ k ∈ (S : Set ι), (I k : Set ℕ)
        have hdis : Disjoint (I a : Set ℕ) U := by
          rw [Set.disjoint_left]
          intro j hja hjU
          rcases Set.mem_iUnion.1 hjU with ⟨k, hjU⟩
          rcases Set.mem_iUnion.1 hjU with ⟨hk, hjk⟩
          have hak : a ≠ k := by
            intro hak
            subst k
            exact ha hk
          exact Finset.disjoint_left.1 (hI hak) hja hjk
        have hcoord : ProbabilityTheory.Indep
            (⨆ j ∈ (I a : Set ℕ), mX j) (⨆ j ∈ U, mX j) μ :=
          ProbabilityTheory.indep_iSup_of_disjoint hmX_le hmX_indep hdis
        have hfa : MeasurableSet[⨆ j ∈ (I a : Set ℕ), mX j] (f a) := by
          simpa only [m] using hf a (Finset.mem_insert_self a S)
        have hfs : MeasurableSet[⨆ j ∈ U, mX j] (⋂ k ∈ S, f k) := by
          apply Finset.measurableSet_biInter
          intro k hk
          have hmk : m k ≤ ⨆ j ∈ U, mX j := by
            dsimp only [m]
            refine iSup_le fun j ↦ iSup_le fun hj ↦ ?_
            refine le_iSup_of_le j (le_iSup_of_le ?_ le_rfl)
            exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, hj⟩⟩
          exact hmk (f k) (hf k (Finset.mem_insert_of_mem hk))
        have hfactor : μ (f a ∩ ⋂ k ∈ S, f k) =
            μ (f a) * μ (⋂ k ∈ S, f k) :=
          (ProbabilityTheory.Indep_iff _ _ μ).1 hcoord _ _ hfa hfs
        rw [Finset.set_biInter_insert, Finset.prod_insert ha, hfactor,
          ih (fun k hk ↦ hf k (Finset.mem_insert_of_mem hk))]
  rw [iIndepSet_iff_iIndep]
  apply iIndep_of_iIndep_of_le hm_indep
  intro k
  apply MeasurableSpace.generateFrom_le
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  subst s
  simpa only [m, mX] using hA k

private noncomputable def lilLowerEps (q : ℕ) : ℝ :=
  1 / (100 * (q : ℝ))

private def lilLowerPower (q : ℕ) : ℕ :=
  (10000 * q) ^ 2

private def lilLowerBase (q : ℕ) : ℕ :=
  2 ^ lilLowerPower q

private def lilLowerTheta (q : ℕ) : ℕ :=
  (100 * q) ^ 2 + 1

private noncomputable def lilLowerA (q : ℕ) : ℝ :=
  (1 - lilLowerEps q) * Real.sqrt (2 * Real.log (lilLowerBase q : ℝ))

private def lilLowerN (q k : ℕ) : ℕ :=
  lilLowerTheta q ^ k

private def lilLowerM (q k : ℕ) : ℕ :=
  lilLowerN q (k + 1) - lilLowerN q k

private def lilLowerR (q k : ℕ) : ℕ :=
  Nat.log (lilLowerBase q) (k + 2)

private def lilLowerEll (q k : ℕ) : ℕ :=
  lilLowerM q k / lilLowerR q k

private lemma lil_lower_eps_bounds {q : ℕ} (hq : 0 < q) :
    0 < lilLowerEps q ∧ lilLowerEps q ≤ 1 / 100 := by
  rw [lilLowerEps]
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  constructor
  · positivity
  · apply one_div_le_one_div_of_le
    · norm_num
    · simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hq' (show (0 : ℝ) ≤ 100 by norm_num)

private lemma lil_lower_base_gt_one {q : ℕ} (hq : 0 < q) :
    1 < lilLowerBase q := by
  rw [lilLowerBase]
  exact one_lt_pow₀ one_lt_two (by simp [lilLowerPower, hq.ne'])

private lemma lil_lower_theta_gt_one {q : ℕ} (hq : 0 < q) :
    1 < lilLowerTheta q := by
  rw [lilLowerTheta]
  have : 0 < (100 * q) ^ 2 := pow_pos (by positivity) _
  omega

private lemma lil_lower_log_base {q : ℕ} :
    Real.log (lilLowerBase q : ℝ) =
      (lilLowerPower q : ℝ) * Real.log 2 := by
  rw [lilLowerBase]
  push_cast
  rw [Real.log_pow]

private lemma lil_log_two_half_le : (1 / 2 : ℝ) ≤ Real.log 2 := by
  apply (Real.le_log_iff_exp_le (by norm_num)).2
  exact (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans_eq (by norm_num)

private lemma lil_exp_three_halves_le : Real.exp (3 / 2) ≤ 8 := by
  have hhalf : Real.exp (1 / 2) ≤ 2 :=
    (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans_eq (by norm_num)
  rw [show (3 / 2 : ℝ) = (3 : ℕ) * (1 / 2 : ℝ) by norm_num, Real.exp_nat_mul]
  exact (pow_le_pow_left₀ (Real.exp_pos (1 / 2)).le hhalf 3).trans_eq (by norm_num)

private lemma lil_lower_a_one_le_and_large {q : ℕ} (hq : 0 < q) :
    1 ≤ lilLowerA q ∧
      6 * Real.exp (3 / 2) ≤ lilLowerEps q * lilLowerA q := by
  have he := lil_lower_eps_bounds hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpow : (lilLowerPower q : ℝ) = (10000 * (q : ℝ)) ^ 2 := by
    rw [lilLowerPower]
    push_cast
    rfl
  have harg : (lilLowerPower q : ℝ) ≤
      2 * Real.log (lilLowerBase q : ℝ) := by
    rw [lil_lower_log_base]
    nlinarith [lil_log_two_half_le]
  have hsqrt : 10000 * (q : ℝ) ≤
      Real.sqrt (2 * Real.log (lilLowerBase q : ℝ)) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    rw [← hpow]
    exact harg
  have honeMinus : (99 / 100 : ℝ) ≤ 1 - lilLowerEps q := by
    nlinarith [he.2]
  have ha : 9900 * (q : ℝ) ≤ lilLowerA q := by
    rw [lilLowerA]
    calc
      9900 * (q : ℝ) = (99 / 100 : ℝ) * (10000 * (q : ℝ)) := by ring
      _ ≤ (1 - lilLowerEps q) *
          Real.sqrt (2 * Real.log (lilLowerBase q : ℝ)) := by gcongr
  constructor
  · exact (by nlinarith [show (1 : ℝ) ≤ q by exact_mod_cast hq])
  · have hleft : 6 * Real.exp (3 / 2) ≤ 48 := by
      nlinarith [lil_exp_three_halves_le]
    have hright : 99 ≤ lilLowerEps q * lilLowerA q := by
      rw [lilLowerEps]
      calc
        (99 : ℝ) = (1 / (100 * (q : ℝ))) * (9900 * (q : ℝ)) := by
          field_simp [hq0.ne']
          norm_num
        _ ≤ (1 / (100 * (q : ℝ))) * lilLowerA q := by gcongr
    exact hleft.trans (by linarith)

private lemma lil_lower_probability_real {q : ℕ} (hq : 0 < q) :
    1 / (lilLowerBase q : ℝ) ≤
      Real.exp (-(1 + lilLowerEps q) * lilLowerA q ^ 2 / 2) / 2 := by
  let e := lilLowerEps q
  let B := (lilLowerBase q : ℝ)
  change 1 / B ≤ Real.exp (-(1 + e) * lilLowerA q ^ 2 / 2) / 2
  have he := lil_lower_eps_bounds hq
  have he0 : 0 < e := by simpa only [e] using he.1
  have he1 : e ≤ 1 := he.2.trans (by norm_num)
  have hB : 1 < B := by
    dsimp only [B]
    exact_mod_cast lil_lower_base_gt_one hq
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hcoef : (1 + e) * (1 - e) ^ 2 ≤ 1 - e := by
    nlinarith [mul_nonneg he0.le (sub_nonneg.2 he1)]
  have ha2 : lilLowerA q ^ 2 = (1 - e) ^ 2 * (2 * Real.log B) := by
    rw [lilLowerA]
    dsimp only [e, B]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have heR : 1 ≤ e * (lilLowerPower q : ℝ) := by
    dsimp only [e, lilLowerEps, lilLowerPower]
    push_cast
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    field_simp [hq0.ne']
    nlinarith [show (1 : ℝ) ≤ q by exact_mod_cast hq]
  have helog : Real.log 2 ≤ e * Real.log B := by
    rw [show Real.log B = (lilLowerPower q : ℝ) * Real.log 2 by
      simpa only [B] using lil_lower_log_base (q := q)]
    nlinarith [Real.log_pos one_lt_two, heR]
  have htwo : (2 : ℝ) ≤ Real.exp (e * Real.log B) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr helog
  have hmain : 2 * Real.exp (-Real.log B) ≤
      Real.exp (-((1 + e) * (1 - e) ^ 2) * Real.log B) := by
    calc
      2 * Real.exp (-Real.log B) ≤
          Real.exp (e * Real.log B) * Real.exp (-Real.log B) := by gcongr
      _ = Real.exp (-(1 - e) * Real.log B) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-((1 + e) * (1 - e) ^ 2) * Real.log B) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  rw [ha2]
  have hB0 : 0 < B := zero_lt_one.trans hB
  rw [show 1 / B = Real.exp (-Real.log B) by
    rw [one_div, Real.exp_neg, Real.exp_log hB0]]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  convert hmain using 1 <;> ring_nf

private def lilSmallBlock
    {Ω : Type*} (X : ℕ → Ω → ℝ) (s ell : ℕ) (a : ℝ) : Set Ω :=
  {ω | a < (Real.sqrt (ell : ℝ))⁻¹ *
    ∑ j ∈ Finset.range ell, X (s + j) ω}

private lemma lilSmallBlock_measurable
    {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hMeas : ∀ j, Measurable (X j)) (s ell : ℕ) (a : ℝ) :
    MeasurableSet (lilSmallBlock X s ell a) := by
  change MeasurableSet ((fun ω ↦ (Real.sqrt (ell : ℝ))⁻¹ *
    ∑ j ∈ Finset.range ell, X (s + j) ω) ⁻¹' Set.Ioi a)
  apply measurableSet_Ioi.preimage
  exact (Finset.measurable_fun_sum (Finset.range ell)
    fun j _ ↦ hMeas (s + j)).const_mul _

private lemma lilSmallBlock_measurable_block
    {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (s ell : ℕ) (a : ℝ) :
    MeasurableSet[⨆ j ∈ (Finset.Ico s (s + ell) : Set ℕ),
      MeasurableSpace.comap (X j) Real.measurableSpace]
      (lilSmallBlock X s ell a) := by
  rw [lilSmallBlock]
  apply measurableSet_lt measurable_const
  apply Measurable.const_mul
  apply Finset.measurable_fun_sum
  intro j hj
  apply Measurable.of_comap_le
  refine le_iSup_of_le (s + j) (le_iSup_of_le ?_ le_rfl)
  rw [Finset.mem_coe, Finset.mem_Ico]
  exact ⟨Nat.le_add_right s j, Nat.add_lt_add_left (Finset.mem_range.1 hj) s⟩

private lemma lil_small_blocks_iIndep
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (ell s : ℕ) (a : ℝ) :
    iIndepSet (fun l ↦ lilSmallBlock X (s + l * ell) ell a) μ := by
  let I := fun l : ℕ ↦ Finset.Ico (s + l * ell) (s + (l + 1) * ell)
  have hI : Pairwise fun l m ↦ Disjoint (I l) (I m) := by
    intro l m hlm
    rw [Finset.disjoint_left]
    intro j hjl hjm
    simp only [I, Finset.mem_Ico] at hjl hjm
    rcases lt_or_gt_of_ne hlm with hlt | hgt
    · have hstep : (l + 1) * ell ≤ m * ell :=
        Nat.mul_le_mul_right ell (Nat.succ_le_iff.2 hlt)
      omega
    · have hstep : (m + 1) * ell ≤ l * ell :=
        Nat.mul_le_mul_right ell (Nat.succ_le_iff.2 hgt)
      omega
  apply lil_iIndepSet_of_disjoint_blocks X hMeas hIndep I hI
  intro l
  convert lilSmallBlock_measurable_block X (s + l * ell) ell a using 1
  all_goals simp only [I, Nat.add_mul, one_mul, add_assoc]

private lemma lil_small_block_measure_eventually
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hMean : ∫ ω, X 0 ω ∂μ = 0) (hVar : Var[X 0; μ] = 1)
    {q : ℕ} (hq : 0 < q) :
    ∀ᶠ ell : ℕ in Filter.atTop, ∀ s : ℕ,
      ENNReal.ofReal (Real.exp (-(1 + lilLowerEps q) * lilLowerA q ^ 2 / 2) / 2) ≤
        μ (lilSmallBlock X s ell (lilLowerA q)) := by
  have ha := lil_lower_a_one_le_and_large hq
  filter_upwards [lil_clt_tail_eventually X hMeas hIndep hIdent hMean hVar
    ha.1 ha.2] with ell hell
  intro s
  have hid := (lil_shifted_sum_identDistrib X hMeas hIndep hIdent s ell).comp
    (measurable_const_mul (Real.sqrt (ell : ℝ))⁻¹)
  have heq := hid.measure_mem_eq (measurableSet_Ioi : MeasurableSet (Set.Ioi (lilLowerA q)))
  have hshift :
      (((fun x ↦ (Real.sqrt (ell : ℝ))⁻¹ * x) ∘
          fun ω ↦ ∑ j ∈ Finset.range ell, X (s + j) ω) ⁻¹' Set.Ioi (lilLowerA q)) =
        lilSmallBlock X s ell (lilLowerA q) := by
    ext ω
    rfl
  have hbase :
      (((fun x ↦ (Real.sqrt (ell : ℝ))⁻¹ * x) ∘
          fun ω ↦ ∑ j ∈ Finset.range ell, X j ω) ⁻¹' Set.Ioi (lilLowerA q)) =
        lilSmallBlock X 0 ell (lilLowerA q) := by
    ext ω
    simp only [Function.comp_apply, lilSmallBlock, Set.mem_preimage, Set.mem_Ioi,
      Set.mem_ofPred_eq, zero_add]
  rw [hshift, hbase] at heq
  have heq' : μ (lilSmallBlock X s ell (lilLowerA q)) =
      μ (lilSmallBlock X 0 ell (lilLowerA q)) := by
    exact heq
  rw [heq']
  simpa only [lilSmallBlock, zero_add] using hell

private lemma lil_lower_m_eq (q k : ℕ) :
    lilLowerM q k = (lilLowerTheta q - 1) * lilLowerTheta q ^ k := by
  rw [lilLowerM, lilLowerN, pow_succ, Nat.sub_mul, one_mul]
  rw [Nat.mul_comm (lilLowerTheta q) (lilLowerTheta q ^ k)]
  rw [lilLowerN]

private lemma lil_add_two_div_pow_tendsto_zero {θ : ℕ} (hθ : 1 < θ) :
    Filter.Tendsto (fun k : ℕ ↦ (k + 2 : ℝ) / (θ : ℝ) ^ k)
      Filter.atTop (nhds 0) := by
  have hθr : (1 : ℝ) < θ := by exact_mod_cast hθ
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hθr
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hθr
  have h := h1.add (h0.const_mul 2)
  convert h using 1
  · funext k
    simp only [pow_one, pow_zero]
    ring
  · simp

private lemma lil_lower_linear_le_m_eventually {q C : ℕ} (hq : 0 < q) :
    ∀ᶠ k : ℕ in Filter.atTop, C * (k + 2) ≤ lilLowerM q k := by
  by_cases hC : C = 0
  · simp [hC]
  have hθ := lil_lower_theta_gt_one hq
  have hlim := lil_add_two_div_pow_tendsto_zero hθ
  have hε : (0 : ℝ) < 1 / (C : ℝ) := by positivity
  filter_upwards [(tendsto_order.1 hlim).2 _ hε] with k hk
  have hpow : (0 : ℝ) < (lilLowerTheta q : ℝ) ^ k := by positivity
  have hCr : (0 : ℝ) < C := by exact_mod_cast Nat.pos_of_ne_zero hC
  have hcast : (C : ℝ) * (k + 2 : ℝ) ≤ (lilLowerTheta q : ℝ) ^ k := by
    have := (div_lt_iff₀ hpow).1 hk
    apply le_of_lt
    calc
      (C : ℝ) * (k + 2 : ℝ) <
          (C : ℝ) * ((1 / (C : ℝ)) * (lilLowerTheta q : ℝ) ^ k) := by gcongr
      _ = (lilLowerTheta q : ℝ) ^ k := by field_simp
  have hnat : C * (k + 2) ≤ lilLowerTheta q ^ k := by exact_mod_cast hcast
  rw [lil_lower_m_eq]
  exact hnat.trans (Nat.le_mul_of_pos_left _ (by omega))

private lemma lil_lower_ell_tendsto_atTop {q : ℕ} (hq : 0 < q) :
    Filter.Tendsto (lilLowerEll q) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro C
  filter_upwards [lil_lower_linear_le_m_eventually (q := q) (C := C) hq,
    Filter.eventually_ge_atTop (lilLowerBase q)] with k hk hkB
  have hrpos : 0 < lilLowerR q k := by
    rw [lilLowerR]
    exact Nat.log_pos (lil_lower_base_gt_one hq) (hkB.trans (Nat.le_add_right k 2))
  have hrle : lilLowerR q k ≤ k + 2 := Nat.log_le_self _ _
  rw [lilLowerEll]
  exact (Nat.le_div_iff_mul_le hrpos).2 <|
    (Nat.mul_le_mul_left C hrle).trans hk

private def lilLowerBlockLen (q k l : ℕ) : ℕ :=
  if l + 1 = lilLowerR q k then
    lilLowerM q k - l * lilLowerEll q k
  else
    lilLowerEll q k

private def lilLowerEvent
    {Ω : Type*} (X : ℕ → Ω → ℝ) (q k : ℕ) : Set Ω :=
  ⋂ l : Fin (lilLowerR q k),
    lilSmallBlock X (lilLowerN q k + l * lilLowerEll q k)
      (lilLowerBlockLen q k l) (lilLowerA q)

private lemma lil_lower_n_le_succ {q : ℕ} (hq : 0 < q) (k : ℕ) :
    lilLowerN q k ≤ lilLowerN q (k + 1) := by
  rw [lilLowerN, lilLowerN, pow_succ]
  have hθpos : 0 < lilLowerTheta q := lt_trans Nat.zero_lt_one (lil_lower_theta_gt_one hq)
  exact Nat.le_mul_of_pos_right _ hθpos

private lemma lil_lower_n_add_m (q k : ℕ) :
    lilLowerN q k + lilLowerM q k = lilLowerN q (k + 1) := by
  rw [lilLowerM]
  have hθpos : 0 < lilLowerTheta q := by
    rw [lilLowerTheta]
    positivity
  exact Nat.add_sub_of_le <| Nat.pow_le_pow_right hθpos (Nat.le_succ k)

private lemma lilLowerEvent_measurable
    {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hMeas : ∀ j, Measurable (X j)) (q k : ℕ) :
    MeasurableSet (lilLowerEvent X q k) := by
  apply MeasurableSet.iInter
  intro l
  exact lilSmallBlock_measurable X hMeas _ _ _

private lemma lilLowerEvent_measurable_block
    {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (q k : ℕ) :
    MeasurableSet[⨆ j ∈ (Finset.Ico (lilLowerN q k) (lilLowerN q (k + 1)) : Set ℕ),
      MeasurableSpace.comap (X j) Real.measurableSpace]
      (lilLowerEvent X q k) := by
  apply MeasurableSet.iInter
  intro l
  let s := lilLowerN q k + l * lilLowerEll q k
  let ell := lilLowerBlockLen q k l
  let msmall : MeasurableSpace Ω := ⨆ j ∈ (Finset.Ico s (s + ell) : Set ℕ),
    MeasurableSpace.comap (X j) Real.measurableSpace
  let mlarge : MeasurableSpace Ω :=
    ⨆ j ∈ (Finset.Ico (lilLowerN q k) (lilLowerN q (k + 1)) : Set ℕ),
      MeasurableSpace.comap (X j) Real.measurableSpace
  have hsub : Finset.Ico s (s + ell) ⊆
      Finset.Ico (lilLowerN q k) (lilLowerN q (k + 1)) := by
    intro j hj
    rw [Finset.mem_Ico] at hj ⊢
    have hcover : lilLowerR q k * lilLowerEll q k ≤ lilLowerM q k := by
      rw [lilLowerEll]
      simpa only [Nat.mul_comm] using Nat.div_mul_le_self (lilLowerM q k) (lilLowerR q k)
    have hlprod : (l : ℕ) * lilLowerEll q k ≤ lilLowerM q k :=
      (Nat.mul_le_mul_right _ (Nat.le_of_lt l.isLt)).trans hcover
    have hend : (l : ℕ) * lilLowerEll q k + lilLowerBlockLen q k l ≤
        lilLowerM q k := by
      rw [lilLowerBlockLen]
      split_ifs with hlast
      · exact (Nat.add_sub_of_le hlprod).le
      · have hsucc : (l : ℕ) + 1 < lilLowerR q k :=
          lt_of_le_of_ne (Nat.succ_le_iff.2 l.isLt) hlast
        have hmul : ((l : ℕ) + 1) * lilLowerEll q k ≤
            lilLowerR q k * lilLowerEll q k :=
          Nat.mul_le_mul_right _ hsucc.le
        rw [Nat.add_mul, one_mul] at hmul
        exact hmul.trans hcover
    constructor
    · exact (Nat.le_add_right _ _).trans hj.1
    · calc
        j < lilLowerN q k +
            ((l : ℕ) * lilLowerEll q k + lilLowerBlockLen q k l) := by
          dsimp only [s, ell] at hj
          omega
        _ ≤ lilLowerN q k + lilLowerM q k := Nat.add_le_add_left hend _
        _ = lilLowerN q (k + 1) := lil_lower_n_add_m q k
  have hle : msmall ≤ mlarge := by
    dsimp only [msmall, mlarge]
    refine iSup_le fun j ↦ iSup_le fun hj ↦ ?_
    exact le_iSup_of_le j (le_iSup_of_le (hsub hj) le_rfl)
  apply hle
  simpa only [s, ell] using
    lilSmallBlock_measurable_block X s ell (lilLowerA q)

private lemma lil_lower_events_iIndep
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) {q : ℕ} (hq : 0 < q) :
    iIndepSet (lilLowerEvent X q) μ := by
  let I := fun k : ℕ ↦ Finset.Ico (lilLowerN q k) (lilLowerN q (k + 1))
  have hI : Pairwise fun k l ↦ Disjoint (I k) (I l) := by
    intro k l hkl
    rw [Finset.disjoint_left]
    intro j hjk hjl
    simp only [I, Finset.mem_Ico] at hjk hjl
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · have hstep : lilLowerN q (k + 1) ≤ lilLowerN q l := by
        rw [lilLowerN, lilLowerN]
        have hθpos : 0 < lilLowerTheta q :=
          lt_trans Nat.zero_lt_one (lil_lower_theta_gt_one hq)
        exact Nat.pow_le_pow_right hθpos
          (Nat.succ_le_iff.2 hlt)
      omega
    · have hstep : lilLowerN q (l + 1) ≤ lilLowerN q k := by
        rw [lilLowerN, lilLowerN]
        have hθpos : 0 < lilLowerTheta q :=
          lt_trans Nat.zero_lt_one (lil_lower_theta_gt_one hq)
        exact Nat.pow_le_pow_right hθpos
          (Nat.succ_le_iff.2 hgt)
      omega
  apply lil_iIndepSet_of_disjoint_blocks X hMeas hIndep I hI
  intro k
  simpa only [I] using lilLowerEvent_measurable_block X q k

private lemma lil_lower_event_measure_eventually
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hMean : ∫ ω, X 0 ω ∂μ = 0) (hVar : Var[X 0; μ] = 1)
    {q : ℕ} (hq : 0 < q) :
    ∀ᶠ k : ℕ in Filter.atTop,
      ENNReal.ofReal (1 / (k + 2 : ℝ)) ≤ μ (lilLowerEvent X q k) := by
  let p := ENNReal.ofReal
    (Real.exp (-(1 + lilLowerEps q) * lilLowerA q ^ 2 / 2) / 2)
  let p0 := ENNReal.ofReal (1 / (lilLowerBase q : ℝ))
  have hp0p : p0 ≤ p := by
    exact ENNReal.ofReal_le_ofReal (lil_lower_probability_real hq)
  have hsmall := lil_small_block_measure_eventually X hMeas hIndep hIdent hMean hVar hq
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
  filter_upwards [(lil_lower_ell_tendsto_atTop hq).eventually_ge_atTop N] with k hk
  let r := lilLowerR q k
  let ell := lilLowerEll q k
  let I := fun l : Fin r ↦ Finset.Ico
    (lilLowerN q k + (l : ℕ) * ell)
    (lilLowerN q k + (l : ℕ) * ell + lilLowerBlockLen q k l)
  let A := fun l : Fin r ↦ lilSmallBlock X
    (lilLowerN q k + (l : ℕ) * ell) (lilLowerBlockLen q k l) (lilLowerA q)
  have hcover : r * ell ≤ lilLowerM q k := by
    dsimp only [r, ell]
    rw [lilLowerEll]
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self (lilLowerM q k) (lilLowerR q k)
  have hlen : ∀ l : Fin r, ell ≤ lilLowerBlockLen q k l := by
    intro l
    rw [lilLowerBlockLen]
    split_ifs with hlast
    · apply Nat.le_sub_of_add_le'
      have hmul : ((l : ℕ) + 1) * ell ≤ r * ell :=
        Nat.mul_le_mul_right ell (Nat.succ_le_iff.2 l.isLt)
      simpa only [Nat.add_mul, one_mul] using hmul.trans hcover
    · exact le_rfl
  have hI : Pairwise fun l m : Fin r ↦ Disjoint (I l) (I m) := by
    intro l m hlm
    rw [Finset.disjoint_left]
    intro j hjl hjm
    simp only [I, Finset.mem_Ico] at hjl hjm
    have hlm' : (l : ℕ) ≠ (m : ℕ) := fun h ↦ hlm (Fin.ext h)
    rcases lt_or_gt_of_ne hlm' with hlt | hgt
    · have hlast : (l : ℕ) + 1 ≠ r := by
        exact ne_of_lt ((Nat.succ_le_iff.2 hlt).trans_lt m.isLt)
      rw [lilLowerBlockLen, ite_eq_right hlast] at hjl
      have hstep : ((l : ℕ) + 1) * ell ≤ (m : ℕ) * ell :=
        Nat.mul_le_mul_right ell (Nat.succ_le_iff.2 hlt)
      rw [Nat.add_mul, one_mul] at hstep
      omega
    · have hlast : (m : ℕ) + 1 ≠ r := by
        exact ne_of_lt ((Nat.succ_le_iff.2 hgt).trans_lt l.isLt)
      rw [lilLowerBlockLen, ite_eq_right hlast] at hjm
      have hstep : ((m : ℕ) + 1) * ell ≤ (l : ℕ) * ell :=
        Nat.mul_le_mul_right ell (Nat.succ_le_iff.2 hgt)
      rw [Nat.add_mul, one_mul] at hstep
      omega
  have hind : iIndepSet A μ := by
    apply lil_iIndepSet_of_disjoint_blocks X hMeas hIndep I hI
    intro l
    simpa only [I, A, add_assoc] using lilSmallBlock_measurable_block X
      (lilLowerN q k + (l : ℕ) * ell) (lilLowerBlockLen q k l) (lilLowerA q)
  have heq := hind.meas_biInter (Finset.univ : Finset (Fin r))
  have hprod : p ^ r ≤ μ (lilLowerEvent X q k) := by
    rw [show μ (lilLowerEvent X q k) = ∏ l ∈ (Finset.univ : Finset (Fin r)), μ (A l) by
      rw [← heq]
      congr 1
      ext ω
      simp only [lilLowerEvent, A, r, ell, Set.mem_iInter, Finset.mem_univ,
        forall_const]]
    simpa only [Finset.prod_const, Finset.card_fin, p] using
      (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin r))) fun l _ ↦
        hN _ (hk.trans (hlen l)) (lilLowerN q k + (l : ℕ) * ell))
  have hpowNat : lilLowerBase q ^ r ≤ k + 2 := by
    dsimp only [r, lilLowerR]
    exact Nat.pow_log_le_self _ (by omega)
  have hpowReal : ((lilLowerBase q : ℝ) ^ r) ≤ (k + 2 : ℝ) := by
    exact_mod_cast hpowNat
  have hinvReal : 1 / (k + 2 : ℝ) ≤ (1 / (lilLowerBase q : ℝ)) ^ r := by
    rw [one_div_pow]
    apply one_div_le_one_div_of_le
    · exact pow_pos (by exact_mod_cast lt_trans Nat.zero_lt_one (lil_lower_base_gt_one hq)) r
    · exact hpowReal
  have hharm : ENNReal.ofReal (1 / (k + 2 : ℝ)) ≤ p0 ^ r := by
    calc
      ENNReal.ofReal (1 / (k + 2 : ℝ)) ≤
          ENNReal.ofReal ((1 / (lilLowerBase q : ℝ)) ^ r) :=
        ENNReal.ofReal_le_ofReal hinvReal
      _ = p0 ^ r := by
        rw [ENNReal.ofReal_pow (by positivity)]
  exact hharm.trans <| (pow_le_pow_left' hp0p r).trans hprod

private lemma lil_harmonic_ennreal_tsum_top (K : ℕ) :
    ∑' k : ℕ, ENNReal.ofReal (1 / (k + K + 2 : ℝ)) = ∞ := by
  let f : ℕ → ℝ≥0 := fun k ↦ ⟨1 / (k + K + 2 : ℝ), by positivity⟩
  have hnot : ¬ Summable (fun k : ℕ ↦ 1 / (k + K + 2 : ℝ)) := by
    intro hs
    have hs' : Summable (fun k : ℕ ↦ 1 / (k : ℝ)) := by
      apply (summable_nat_add_iff (K + 2)).1
      simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc] using hs
    exact Real.not_summable_one_div_natCast hs'
  have htop : ∑' k : ℕ, ((f k : ℝ≥0) : ℝ≥0∞) = ∞ := by
    by_contra hne
    have hsf : Summable f := ENNReal.tsum_coe_ne_top_iff_summable.1 hne
    have hsreal : Summable (fun k ↦ (f k : ℝ)) := NNReal.summable_coe.2 hsf
    change Summable (fun k : ℕ ↦ 1 / (k + K + 2 : ℝ)) at hsreal
    exact hnot hsreal
  have hterm (k : ℕ) : ((f k : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (1 / (k + K + 2 : ℝ)) := by
    rw [ENNReal.coe_nnreal_eq]
    congr 1
  simpa only [hterm] using htop

private lemma lil_lower_event_tsum_top
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hMean : ∫ ω, X 0 ω ∂μ = 0) (hVar : Var[X 0; μ] = 1)
    {q : ℕ} (hq : 0 < q) :
    ∑' k, μ (lilLowerEvent X q k) = ∞ := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 <|
    lil_lower_event_measure_eventually X hMeas hIndep hIdent hMean hVar hq
  have htail : ∑' k, μ (lilLowerEvent X q (k + K)) = ∞ := by
    apply top_unique
    calc
      ∞ = ∑' k : ℕ, ENNReal.ofReal (1 / (k + K + 2 : ℝ)) :=
        (lil_harmonic_ennreal_tsum_top K).symm
      _ ≤ ∑' k, μ (lilLowerEvent X q (k + K)) := by
        apply ENNReal.tsum_le_tsum
        intro k
        simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc] using
          hK (k + K) (Nat.le_add_left K k)
  apply top_unique
  exact htail ▸ ENNReal.tsum_comp_le_tsum_of_injective
    (fun _ _ h ↦ Nat.add_right_cancel h) (fun k ↦ μ (lilLowerEvent X q k))

private lemma lil_tendsto_log :
    Filter.Tendsto lilLog Filter.atTop Filter.atTop := by
  have hraw : Filter.Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply hraw.congr'
  filter_upwards [lil_eventually_log_eq] with n hn
  exact hn.symm

private lemma lil_lower_n_succ_tendsto_atTop {q : ℕ} (hq : 0 < q) :
    Filter.Tendsto (fun k ↦ lilLowerN q (k + 1)) Filter.atTop Filter.atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (lil_lower_theta_gt_one hq)).comp
    (Filter.tendsto_add_atTop_nat 1)

private lemma lil_lower_r_pos_eventually {q : ℕ} (hq : 0 < q) :
    ∀ᶠ k : ℕ in Filter.atTop, 0 < lilLowerR q k := by
  filter_upwards [Filter.eventually_ge_atTop (lilLowerBase q)] with k hk
  rw [lilLowerR]
  exact Nat.log_pos (lil_lower_base_gt_one hq) (hk.trans (Nat.le_add_right k 2))

private lemma lil_lower_coverage_eventually {q : ℕ} (hq : 0 < q) :
    ∀ᶠ k : ℕ in Filter.atTop,
      (1 - lilLowerEps q) * (lilLowerM q k : ℝ) ≤
        (lilLowerR q k : ℝ) * (lilLowerEll q k : ℝ) := by
  filter_upwards [lil_lower_linear_le_m_eventually (q := q) (C := 100 * q) hq,
    lil_lower_r_pos_eventually hq] with k hlinear hrpos
  have hrle : lilLowerR q k ≤ k + 2 := Nat.log_le_self _ _
  have hscaled : 100 * q * lilLowerR q k ≤ lilLowerM q k :=
    (Nat.mul_le_mul_left (100 * q) hrle).trans hlinear
  have hdiv : lilLowerM q k <
      lilLowerR q k * (lilLowerEll q k + 1) := by
    simpa only [lilLowerEll] using Nat.lt_mul_div_succ (lilLowerM q k) hrpos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : (100 * (q : ℝ)) * (lilLowerR q k : ℝ) ≤
      (lilLowerM q k : ℝ) := by exact_mod_cast hscaled
  have hscaled' : (lilLowerR q k : ℝ) ≤
      lilLowerEps q * (lilLowerM q k : ℝ) := by
    have hdivle : (lilLowerR q k : ℝ) ≤
        (lilLowerM q k : ℝ) / (100 * (q : ℝ)) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 100 * q)).2
      nlinarith [hc]
    rw [lilLowerEps]
    calc
      (lilLowerR q k : ℝ) ≤ (lilLowerM q k : ℝ) / (100 * (q : ℝ)) := hdivle
      _ = (1 / (100 * (q : ℝ))) * (lilLowerM q k : ℝ) := by ring
  have hdiv' : (lilLowerM q k : ℝ) ≤
      (lilLowerR q k : ℝ) * ((lilLowerEll q k : ℝ) + 1) := by
    exact_mod_cast hdiv.le
  nlinarith

private lemma lil_lower_log_eventually {q : ℕ} (hq : 0 < q) :
    ∀ᶠ k : ℕ in Filter.atTop,
      (1 - lilLowerEps q) * lilLog (lilLowerN q (k + 1)) ≤
        (lilLowerR q k : ℝ) * Real.log (lilLowerBase q : ℝ) := by
  let θ := lilLowerTheta q
  let B := lilLowerBase q
  let e := lilLowerEps q
  let C := Real.log (Real.log (θ : ℝ))
  have hθ : 1 < θ := lil_lower_theta_gt_one hq
  have hB : 1 < B := lil_lower_base_gt_one hq
  have hlogθ : 0 < Real.log (θ : ℝ) := Real.log_pos <| by exact_mod_cast hθ
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos <| by exact_mod_cast hB
  have he0 : 0 < e := by simpa only [e] using (lil_lower_eps_bounds hq).1
  have hL : Filter.Tendsto (fun k ↦ lilLog (lilLowerN q (k + 1)))
      Filter.atTop Filter.atTop :=
    lil_tendsto_log.comp (lil_lower_n_succ_tendsto_atTop hq)
  have hlarge : ∀ᶠ k : ℕ in Filter.atTop,
      Real.log (B : ℝ) + C ≤ e * lilLog (lilLowerN q (k + 1)) :=
    (hL.const_mul_atTop he0).eventually_ge_atTop _
  have hlogeq := (lil_lower_n_succ_tendsto_atTop hq).eventually lil_eventually_log_eq
  filter_upwards [hlarge, hlogeq] with k hk hLeq
  have hk0 : (0 : ℝ) < k + 1 := by positivity
  have hk20 : (0 : ℝ) < k + 2 := by positivity
  have hLupper : lilLog (lilLowerN q (k + 1)) ≤ Real.log (k + 2 : ℝ) + C := by
    rw [hLeq, lilLowerN]
    rw [Nat.cast_pow]
    rw [Real.log_pow]
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      Real.log ((k + 1 : ℝ) * Real.log (lilLowerTheta q : ℝ)) ≤
          Real.log ((k + 2 : ℝ) * Real.log (lilLowerTheta q : ℝ)) := by
        apply Real.log_le_log (mul_pos hk0 hlogθ)
        apply mul_le_mul_of_nonneg_right _ hlogθ.le
        norm_num
      _ = Real.log (k + 2 : ℝ) + C := by
        rw [Real.log_mul hk20.ne' hlogθ.ne']
  have hnat := Nat.lt_pow_succ_log_self (lil_lower_base_gt_one hq) (k + 2)
  have hnatReal : (k + 2 : ℝ) < (B : ℝ) ^ (lilLowerR q k + 1) := by
    dsimp only [B, lilLowerR]
    exact_mod_cast hnat
  have hlogk : Real.log (k + 2 : ℝ) <
      ((lilLowerR q k : ℝ) + 1) * Real.log (B : ℝ) := by
    have hB0 : (0 : ℝ) < B := by exact_mod_cast Nat.zero_lt_one.trans hB
    calc
      Real.log (k + 2 : ℝ) < Real.log ((B : ℝ) ^ (lilLowerR q k + 1)) := by
        exact Real.strictMonoOn_log hk20 (pow_pos hB0 _) hnatReal
      _ = ((lilLowerR q k : ℝ) + 1) * Real.log (B : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          Real.log_pow (B : ℝ) (lilLowerR q k + 1)
  dsimp only [e, B] at hk hLupper hlogk ⊢
  linarith

private lemma lil_lower_block_len_ge (q k : ℕ) {l : ℕ}
    (hl : l < lilLowerR q k) :
    lilLowerEll q k ≤ lilLowerBlockLen q k l := by
  have hcover : lilLowerR q k * lilLowerEll q k ≤ lilLowerM q k := by
    rw [lilLowerEll]
    simpa only [Nat.mul_comm] using
      Nat.div_mul_le_self (lilLowerM q k) (lilLowerR q k)
  rw [lilLowerBlockLen]
  split_ifs with hlast
  · apply Nat.le_sub_of_add_le'
    have hmul : (l + 1) * lilLowerEll q k ≤
        lilLowerR q k * lilLowerEll q k :=
      Nat.mul_le_mul_right _ (Nat.succ_le_iff.2 hl)
    simpa only [Nat.add_mul, one_mul] using hmul.trans hcover
  · exact le_rfl

private lemma lil_lower_block_end (q k : ℕ) {l : ℕ}
    (hl : l < lilLowerR q k) :
    lilLowerN q k + l * lilLowerEll q k + lilLowerBlockLen q k l =
      if l + 1 = lilLowerR q k then lilLowerN q (k + 1)
      else lilLowerN q k + (l + 1) * lilLowerEll q k := by
  have hcover : lilLowerR q k * lilLowerEll q k ≤ lilLowerM q k := by
    rw [lilLowerEll]
    simpa only [Nat.mul_comm] using
      Nat.div_mul_le_self (lilLowerM q k) (lilLowerR q k)
  have hlprod : l * lilLowerEll q k ≤ lilLowerM q k :=
    (Nat.mul_le_mul_right _ hl.le).trans hcover
  rw [lilLowerBlockLen]
  split_ifs with hlast
  · rw [Nat.add_assoc, Nat.add_sub_of_le hlprod, lil_lower_n_add_m]
  · rw [Nat.add_mul, one_mul]
    omega

private lemma lil_lower_block_sum_telescope
    {Ω : Type*} {q k : ℕ} (hrpos : 0 < lilLowerR q k)
    {X : ℕ → Ω → ℝ} (omega : Ω) :
    ∑ l ∈ Finset.range (lilLowerR q k),
      ∑ j ∈ Finset.range (lilLowerBlockLen q k l),
        X (lilLowerN q k + l * lilLowerEll q k + j) omega =
      (∑ j ∈ Finset.range (lilLowerN q (k + 1)), X j omega) -
        ∑ j ∈ Finset.range (lilLowerN q k), X j omega := by
  let F : ℕ → ℝ := fun t ↦
    ∑ j ∈ Finset.range
      (if t = lilLowerR q k then lilLowerN q (k + 1)
      else lilLowerN q k + t * lilLowerEll q k), X j omega
  have hterm (l : ℕ) (hl : l < lilLowerR q k) :
      (∑ j ∈ Finset.range (lilLowerBlockLen q k l),
          X (lilLowerN q k + l * lilLowerEll q k + j) omega) =
        F (l + 1) - F l := by
    have hlR : l < lilLowerR q k := hl
    have hlne : l ≠ lilLowerR q k := ne_of_lt hl
    have hstart : lilLowerN q k + l * lilLowerEll q k ≤
        lilLowerN q k + l * lilLowerEll q k + lilLowerBlockLen q k l :=
      Nat.le_add_right _ _
    rw [show (∑ j ∈ Finset.range (lilLowerBlockLen q k l),
        X (lilLowerN q k + l * lilLowerEll q k + j) omega) =
        ∑ j ∈ Finset.Ico (lilLowerN q k + l * lilLowerEll q k)
          (lilLowerN q k + l * lilLowerEll q k + lilLowerBlockLen q k l),
          X j omega by
      simpa only [Finset.range_eq_Ico, zero_add, add_comm] using
        Finset.sum_Ico_add (fun j ↦ X j omega) 0
          (lilLowerBlockLen q k l) (lilLowerN q k + l * lilLowerEll q k)]
    rw [Finset.sum_Ico_eq_sub _ hstart]
    dsimp only [F]
    rw [ite_eq_right hlne]
    congr 1
    rw [lil_lower_block_end q k hlR]
  calc
    ∑ l ∈ Finset.range (lilLowerR q k),
        ∑ j ∈ Finset.range (lilLowerBlockLen q k l),
          X (lilLowerN q k + l * lilLowerEll q k + j) omega =
      ∑ l ∈ Finset.range (lilLowerR q k),
        (F (l + 1) - F l) := by
      apply Finset.sum_congr rfl
      intro l hl
      exact hterm l (Finset.mem_range.1 hl)
    _ = F (lilLowerR q k) - F 0 :=
      Finset.sum_range_sub F (lilLowerR q k)
    _ = (∑ j ∈ Finset.range (lilLowerN q (k + 1)), X j omega) -
        ∑ j ∈ Finset.range (lilLowerN q k), X j omega := by
      simp only [F, ite_eq_left, ite_eq_right hrpos.ne, zero_mul, add_zero]

private lemma lil_lower_event_increment
    {Ω : Type*} {X : ℕ → Ω → ℝ} {q k : ℕ} (hq : 0 < q)
    (hrpos : 0 < lilLowerR q k) (hellpos : 0 < lilLowerEll q k)
    {ω : Ω} (hω : ω ∈ lilLowerEvent X q k) :
    (lilLowerR q k : ℝ) * lilLowerA q *
        Real.sqrt (lilLowerEll q k : ℝ) <
      (∑ j ∈ Finset.range (lilLowerN q (k + 1)), X j ω) -
        ∑ j ∈ Finset.range (lilLowerN q k), X j ω := by
  let r := lilLowerR q k
  let ell := lilLowerEll q k
  have ha0 : 0 ≤ lilLowerA q := zero_le_one.trans (lil_lower_a_one_le_and_large hq).1
  have hpoint : ∀ l ∈ Finset.range r,
      lilLowerA q * Real.sqrt (ell : ℝ) <
        ∑ j ∈ Finset.range (lilLowerBlockLen q k l),
          X (lilLowerN q k + l * ell + j) ω := by
    intro l hl
    have hlr : l < lilLowerR q k := by
      simpa only [r] using Finset.mem_range.1 hl
    have hlen := lil_lower_block_len_ge q k hlr
    have hlenpos : 0 < lilLowerBlockLen q k l := hellpos.trans_le hlen
    have hsqrtpos : 0 < Real.sqrt (lilLowerBlockLen q k l : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hlenpos)
    have hblock := Set.mem_iInter.1 hω ⟨l, hlr⟩
    have hblock' : lilLowerA q <
        (∑ j ∈ Finset.range (lilLowerBlockLen q k l),
          X (lilLowerN q k + l * ell + j) ω) /
            Real.sqrt (lilLowerBlockLen q k l : ℝ) := by
      simpa only [lilSmallBlock, Set.mem_ofPred_eq, div_eq_mul_inv, mul_comm,
        ell] using hblock
    have hstrict := (lt_div_iff₀ hsqrtpos).1 hblock'
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by exact_mod_cast hlen)) ha0) hstrict
  have hsum :
      ∑ l ∈ Finset.range r, lilLowerA q * Real.sqrt (ell : ℝ) <
        ∑ l ∈ Finset.range r,
          ∑ j ∈ Finset.range (lilLowerBlockLen q k l),
            X (lilLowerN q k + l * ell + j) ω :=
    Finset.sum_lt_sum_of_nonempty
      (Finset.nonempty_range_iff.2 (by simpa only [r] using hrpos.ne')) hpoint
  rw [lil_lower_block_sum_telescope hrpos ω] at hsum
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, r, ell, mul_assoc] using hsum

private lemma lil_lower_threshold_eventually {q : ℕ} (hq : 0 < q) :
    ∀ᶠ k : ℕ in Filter.atTop,
      (1 - lilLowerEps q) ^ 2 *
          Real.sqrt (2 * (lilLowerM q k : ℝ) * lilLog (lilLowerN q (k + 1))) ≤
        (lilLowerR q k : ℝ) * lilLowerA q *
          Real.sqrt (lilLowerEll q k : ℝ) := by
  filter_upwards [lil_lower_coverage_eventually hq, lil_lower_log_eventually hq,
    (lil_lower_ell_tendsto_atTop hq).eventually_ge_atTop 1] with k hcover hlog hell
  let e := lilLowerEps q
  let M := (lilLowerM q k : ℝ)
  let L := lilLog (lilLowerN q (k + 1))
  let r := (lilLowerR q k : ℝ)
  let ell := (lilLowerEll q k : ℝ)
  let B := (lilLowerBase q : ℝ)
  have he := lil_lower_eps_bounds hq
  have he1 : e ≤ 1 := by simpa only [e] using he.2.trans (by norm_num)
  have hM0 : 0 ≤ M := by positivity
  have hL0 : 0 ≤ L := zero_le_one.trans (lilLog_one_le _)
  have hr0 : 0 ≤ r := by positivity
  have hell0 : 0 ≤ ell := by positivity
  have hlogB0 : 0 ≤ Real.log B := by
    apply (Real.log_pos _).le
    dsimp only [B]
    exact_mod_cast lil_lower_base_gt_one hq
  have hprod : ((1 - e) * M) * ((1 - e) * L) ≤
      (r * ell) * (r * Real.log B) := by
    calc
      ((1 - e) * M) * ((1 - e) * L) ≤
          (r * ell) * ((1 - e) * L) := by
        apply mul_le_mul_of_nonneg_right
        · simpa only [e, M, r, ell] using hcover
        · positivity
      _ ≤ (r * ell) * (r * Real.log B) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [e, L, r, B] using hlog
        · positivity
  have hmain : (1 - e) ^ 2 * M * L ≤ r ^ 2 * ell * Real.log B := by
    calc
      (1 - e) ^ 2 * M * L = ((1 - e) * M) * ((1 - e) * L) := by ring
      _ ≤ (r * ell) * (r * Real.log B) := hprod
      _ = r ^ 2 * ell * Real.log B := by ring
  have harg0 : 0 ≤ 2 * M * L := by positivity
  have hleft0 : 0 ≤ (1 - e) ^ 2 * Real.sqrt (2 * M * L) := by positivity
  have hright0 : 0 ≤ r * lilLowerA q * Real.sqrt ell := by
    have ha0 : 0 ≤ lilLowerA q :=
      zero_le_one.trans (lil_lower_a_one_le_and_large hq).1
    positivity
  have ha2 : lilLowerA q ^ 2 = (1 - e) ^ 2 * (2 * Real.log B) := by
    rw [lilLowerA]
    dsimp only [e, B]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hellSq : (Real.sqrt ell) ^ 2 = ell := Real.sq_sqrt hell0
  have hscaled : 2 * (1 - e) ^ 2 * ((1 - e) ^ 2 * M * L) ≤
      2 * (1 - e) ^ 2 * (r ^ 2 * ell * Real.log B) :=
    mul_le_mul_of_nonneg_left hmain (by positivity)
  dsimp only [e, M, L, r, ell, B] at hleft0 hright0 ⊢
  rw [← sq_le_sq₀ hleft0 hright0]
  calc
    ((1 - lilLowerEps q) ^ 2 *
        Real.sqrt (2 * (lilLowerM q k : ℝ) * lilLog (lilLowerN q (k + 1)))) ^ 2 =
        2 * (1 - e) ^ 2 * ((1 - e) ^ 2 * M * L) := by
      rw [mul_pow, Real.sq_sqrt harg0]
      ring
    _ ≤ 2 * (1 - e) ^ 2 * (r ^ 2 * ell * Real.log B) := hscaled
    _ = ((lilLowerR q k : ℝ) * lilLowerA q *
        Real.sqrt (lilLowerEll q k : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow, ha2, hellSq]
      dsimp only [r, ell, e, B]
      ring

private lemma lil_lower_threshold_ge_scale {q : ℕ} (hq : 0 < q) (k : ℕ) :
    (1 - 1 / (q : ℝ)) * lilScale (lilLowerN q (k + 1)) ≤
      (1 - lilLowerEps q) ^ 2 *
        Real.sqrt (2 * (lilLowerM q k : ℝ) * lilLog (lilLowerN q (k + 1))) := by
  let e := lilLowerEps q
  let θ := lilLowerTheta q
  let n := (lilLowerN q (k + 1) : ℝ)
  let m := (lilLowerM q k : ℝ)
  let L := lilLog (lilLowerN q (k + 1))
  have he := lil_lower_eps_bounds hq
  have he0 : 0 ≤ e := by simpa only [e] using he.1.le
  have he1 : e ≤ 1 := by simpa only [e] using he.2.trans (by norm_num)
  have hθcoef : (1 - e) ^ 2 * (θ : ℝ) ≤ (θ : ℝ) - 1 := by
    dsimp only [e, θ, lilLowerEps, lilLowerTheta]
    push_cast
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hQ : (1 : ℝ) ≤ 100 * q := by nlinarith
    have hnonneg : 0 ≤ (100 * (q : ℝ)) ^ 2 * (100 * q - 1) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.2 hQ)
    field_simp [hq0.ne']
    nlinarith
  have hmratio : (1 - e) ^ 2 * n ≤ m := by
    have hpow0 : 0 ≤ (θ : ℝ) ^ k := by positivity
    have hmul := mul_le_mul_of_nonneg_right hθcoef hpow0
    have hθ1 : 1 ≤ θ := by
      dsimp only [θ]
      exact (lil_lower_theta_gt_one hq).le
    have hnEq : n = (θ : ℝ) * (θ : ℝ) ^ k := by
      dsimp only [n, θ]
      rw [lilLowerN, pow_succ]
      simp only [Nat.cast_mul, Nat.cast_pow]
      ring
    have hmEq : m = ((θ : ℝ) - 1) * (θ : ℝ) ^ k := by
      dsimp only [m]
      rw [lil_lower_m_eq]
      change (((θ - 1) * θ ^ k : ℕ) : ℝ) = ((θ : ℝ) - 1) * (θ : ℝ) ^ k
      simp only [Nat.cast_mul, Nat.cast_sub hθ1, Nat.cast_one, Nat.cast_pow]
    calc
      (1 - e) ^ 2 * n = ((1 - e) ^ 2 * (θ : ℝ)) * (θ : ℝ) ^ k := by
        rw [hnEq]
        ring
      _ ≤ ((θ : ℝ) - 1) * (θ : ℝ) ^ k := hmul
      _ = m := hmEq.symm
  have hL0 : 0 ≤ L := zero_le_one.trans (lilLog_one_le _)
  have hn0 : 0 ≤ n := by positivity
  have hm0 : 0 ≤ m := by positivity
  have hargN : 0 ≤ 2 * n * L := by positivity
  have hargM : 0 ≤ 2 * m * L := by positivity
  have hsqrt : (1 - e) * Real.sqrt (2 * n * L) ≤
      Real.sqrt (2 * m * L) := by
    have hleft0 : 0 ≤ (1 - e) * Real.sqrt (2 * n * L) := by positivity
    have hright0 : 0 ≤ Real.sqrt (2 * m * L) := Real.sqrt_nonneg _
    rw [← sq_le_sq₀ hleft0 hright0]
    rw [mul_pow, Real.sq_sqrt hargN, Real.sq_sqrt hargM]
    nlinarith [mul_le_mul_of_nonneg_right hmratio (show 0 ≤ 2 * L by positivity)]
  have h3e : 3 * e ≤ 1 / (q : ℝ) := by
    dsimp only [e, lilLowerEps]
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    field_simp [hq0.ne']
    nlinarith
  have hcubic : 1 - 1 / (q : ℝ) ≤ (1 - e) ^ 3 := by
    have hbern : 1 - 3 * e ≤ (1 - e) ^ 3 := by
      have : 0 ≤ e ^ 2 * (3 - e) := mul_nonneg (sq_nonneg e) (by linarith)
      nlinarith
    linarith
  have hscale : lilScale (lilLowerN q (k + 1)) = Real.sqrt (2 * n * L) := by
    simp only [lilScale, n, L]
  rw [hscale]
  calc
    (1 - 1 / (q : ℝ)) * Real.sqrt (2 * n * L) ≤
        (1 - e) ^ 3 * Real.sqrt (2 * n * L) :=
      mul_le_mul_of_nonneg_right hcubic (Real.sqrt_nonneg _)
    _ = (1 - e) ^ 2 * ((1 - e) * Real.sqrt (2 * n * L)) := by ring
    _ ≤ (1 - e) ^ 2 * Real.sqrt (2 * m * L) :=
      mul_le_mul_of_nonneg_left hsqrt (sq_nonneg _)
    _ = (1 - lilLowerEps q) ^ 2 *
        Real.sqrt (2 * (lilLowerM q k : ℝ) * lilLog (lilLowerN q (k + 1))) := by
      rfl

private lemma lil_lower_prev_scale {q : ℕ} (hq : 0 < q) (k : ℕ) :
    lilScale (lilLowerN q k) ≤
      (1 / (100 * (q : ℝ))) * lilScale (lilLowerN q (k + 1)) := by
  let Q := 100 * (q : ℝ)
  let n₀ := (lilLowerN q k : ℝ)
  let n₁ := (lilLowerN q (k + 1) : ℝ)
  let L₀ := lilLog (lilLowerN q k)
  let L₁ := lilLog (lilLowerN q (k + 1))
  have hQ0 : 0 < Q := by
    dsimp only [Q]
    positivity
  have hn : lilLowerN q k ≤ lilLowerN q (k + 1) := lil_lower_n_le_succ hq k
  have hL : L₀ ≤ L₁ := lilLog_monotone hn
  have hL₀0 : 0 ≤ L₀ := zero_le_one.trans (lilLog_one_le _)
  have hL₁0 : 0 ≤ L₁ := zero_le_one.trans (lilLog_one_le _)
  have hθ : Q ^ 2 ≤ (lilLowerTheta q : ℝ) := by
    dsimp only [Q, lilLowerTheta]
    push_cast
    nlinarith
  have hnEq : n₁ = (lilLowerTheta q : ℝ) * n₀ := by
    dsimp only [n₀, n₁]
    rw [lilLowerN, lilLowerN, pow_succ]
    simp only [Nat.cast_mul, Nat.cast_pow]
    ring
  have harg₀ : 0 ≤ 2 * n₀ * L₀ := by positivity
  have harg₁ : 0 ≤ 2 * n₁ * L₁ := by positivity
  have hsq : (Q * lilScale (lilLowerN q k)) ^ 2 ≤
      lilScale (lilLowerN q (k + 1)) ^ 2 := by
    rw [lilScale, lilScale, mul_pow, Real.sq_sqrt harg₀, Real.sq_sqrt harg₁]
    dsimp only [n₀, n₁, L₀, L₁] at hnEq hL ⊢
    calc
      Q ^ 2 * (2 * (lilLowerN q k : ℝ) * lilLog (lilLowerN q k)) =
          2 * (Q ^ 2 * (lilLowerN q k : ℝ)) * lilLog (lilLowerN q k) := by ring
      _ ≤ 2 * ((lilLowerTheta q : ℝ) * (lilLowerN q k : ℝ)) *
          lilLog (lilLowerN q k) := by gcongr
      _ = 2 * (lilLowerN q (k + 1) : ℝ) * lilLog (lilLowerN q k) := by
        rw [← hnEq]
      _ ≤ 2 * (lilLowerN q (k + 1) : ℝ) *
          lilLog (lilLowerN q (k + 1)) := by gcongr
  have hmul : Q * lilScale (lilLowerN q k) ≤ lilScale (lilLowerN q (k + 1)) := by
    rw [← sq_le_sq₀ (mul_nonneg hQ0.le (lilScale_nonneg _)) (lilScale_nonneg _)]
    exact hsq
  have hdiv : lilScale (lilLowerN q k) ≤ lilScale (lilLowerN q (k + 1)) / Q :=
    (le_div_iff₀ hQ0).2 (by simpa only [mul_comm] using hmul)
  simpa only [Q, div_eq_mul_inv, one_div, one_mul, mul_comm] using hdiv

private lemma lil_ae_frequently_lower_event
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hMean : ∫ ω, X 0 ω ∂μ = 0) (hVar : Var[X 0; μ] = 1)
    {q : ℕ} (hq : 0 < q) :
    ∀ᵐ ω ∂μ, ∃ᶠ k : ℕ in Filter.atTop, ω ∈ lilLowerEvent X q k := by
  have hmeasure : μ (Filter.limsup (lilLowerEvent X q) Filter.atTop) = 1 :=
    ProbabilityTheory.measure_limsup_eq_one
      (lilLowerEvent_measurable X hMeas q)
      (lil_lower_events_iIndep X hMeas hIndep hq)
      (lil_lower_event_tsum_top X hMeas hIndep hIdent hMean hVar hq)
  have hmeas : MeasurableSet (Filter.limsup (lilLowerEvent X q) Filter.atTop) :=
    MeasurableSet.measurableSet_limsup (lilLowerEvent_measurable X hMeas q)
  have hae : ∀ᵐ ω ∂μ, ω ∈ Filter.limsup (lilLowerEvent X q) Filter.atTop := by
    apply (ae_mem_iff_measure_eq hmeas.nullMeasurableSet).2
    simpa using hmeasure
  filter_upwards [hae] with ω hω
  exact Filter.mem_limsup_iff_frequently_mem.1 hω

private lemma lil_ae_frequently_sum_ge
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X μ) (hIdent : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hInt : Integrable (X 0) μ) (hMemLp : MemLp (X 0) 2 μ)
    (hMean : ∫ ω, X 0 ω ∂μ = 0) (hVar : Var[X 0; μ] = 1)
    {q : ℕ} (hq : 0 < q) :
    ∀ᵐ ω ∂μ, ∃ᶠ n : ℕ in Filter.atTop,
      1 - 2 / (q : ℝ) ≤
        (∑ j ∈ Finset.range n, X j ω) / lilScale n := by
  let Xneg : ℕ → Ω → ℝ := fun n ↦ -X n
  have hXneg (n : ℕ) : Xneg n = (fun x : ℝ ↦ -x) ∘ X n := by
    funext ω
    simp only [Xneg, Pi.neg_apply, Function.comp_apply]
  have hMeasNeg : ∀ n, Measurable (Xneg n) := fun n ↦ (hMeas n).neg
  have hIndepNeg : iIndepFun Xneg μ := by
    rw [show Xneg = fun n ↦ (fun x : ℝ ↦ -x) ∘ X n by
      funext n
      exact hXneg n]
    exact hIndep.comp (fun _ : ℕ ↦ fun x : ℝ ↦ -x) (fun _ ↦ measurable_neg)
  have hIdentNeg : ∀ j, IdentDistrib (Xneg j) (Xneg 0) μ μ := by
    intro j
    rw [hXneg j, hXneg 0]
    exact (hIdent j).comp measurable_neg
  have hIntNeg : Integrable (Xneg 0) μ := by simpa only [Xneg] using hInt.neg
  have hMemLpNeg : MemLp (Xneg 0) 2 μ := by
    simpa only [Xneg] using hMemLp.neg
  have hMeanNeg : ∫ ω, Xneg 0 ω ∂μ = 0 := by
    change (∫ ω, -X 0 ω ∂μ) = 0
    rw [integral_neg, hMean, neg_zero]
  have hVarNeg : Var[Xneg 0; μ] = 1 := by
    change Var[fun ω ↦ -X 0 ω; μ] = 1
    rw [ProbabilityTheory.variance_fun_neg, hVar]
  have hevents := lil_ae_frequently_lower_event X hMeas hIndep hIdent hMean hVar hq
  have hupperNeg := lil_ae_eventually_sum_le Xneg hMeasNeg hIndepNeg hIdentNeg
    hIntNeg hMemLpNeg hMeanNeg hVarNeg hq
  have hgood : ∀ᶠ k : ℕ in Filter.atTop,
      0 < lilLowerR q k ∧ 0 < lilLowerEll q k ∧
        (1 - lilLowerEps q) ^ 2 *
            Real.sqrt (2 * (lilLowerM q k : ℝ) * lilLog (lilLowerN q (k + 1))) ≤
          (lilLowerR q k : ℝ) * lilLowerA q *
            Real.sqrt (lilLowerEll q k : ℝ) := by
    filter_upwards [lil_lower_r_pos_eventually hq,
      (lil_lower_ell_tendsto_atTop hq).eventually_ge_atTop 1,
      lil_lower_threshold_eventually hq] with k hr hell hthreshold
    exact ⟨hr, hell, hthreshold⟩
  have hN : Filter.Tendsto (lilLowerN q) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (lil_lower_theta_gt_one hq)
  have hNsucc := lil_lower_n_succ_tendsto_atTop hq
  filter_upwards [hevents, hupperNeg] with ω hfreq hupper
  have hupperK : ∀ᶠ k : ℕ in Filter.atTop,
      (∑ j ∈ Finset.range (lilLowerN q k), Xneg j ω) /
          lilScale (lilLowerN q k) ≤ 1 + 6 / (q : ℝ) :=
    hN.eventually hupper
  have hkfreq : ∃ᶠ k : ℕ in Filter.atTop,
      1 - 2 / (q : ℝ) ≤
        (∑ j ∈ Finset.range (lilLowerN q (k + 1)), X j ω) /
          lilScale (lilLowerN q (k + 1)) := by
    apply (hfreq.and_eventually (hgood.and hupperK)).mono
    intro k hk
    rcases hk with ⟨hEvent, ⟨hrpos, hellpos, hthreshold⟩, hnegRaw⟩
    let S₀ := ∑ j ∈ Finset.range (lilLowerN q k), X j ω
    let S₁ := ∑ j ∈ Finset.range (lilLowerN q (k + 1)), X j ω
    let b₀ := lilScale (lilLowerN q k)
    let b₁ := lilScale (lilLowerN q (k + 1))
    have hb₀0 : 0 < b₀ := by
      dsimp only [b₀, lilScale]
      apply Real.sqrt_pos.2
      have hn0 : 0 < lilLowerN q k := pow_pos
        (lt_trans Nat.zero_lt_one (lil_lower_theta_gt_one hq)) _
      exact mul_pos (mul_pos zero_lt_two (by exact_mod_cast hn0))
        (zero_lt_one.trans_le (lilLog_one_le _))
    have hb₁0 : 0 < b₁ := by
      dsimp only [b₁, lilScale]
      apply Real.sqrt_pos.2
      have hn1 : 0 < lilLowerN q (k + 1) := pow_pos
        (lt_trans Nat.zero_lt_one (lil_lower_theta_gt_one hq)) _
      exact mul_pos (mul_pos zero_lt_two (by exact_mod_cast hn1))
        (zero_lt_one.trans_le (lilLog_one_le _))
    have hincRaw := lil_lower_event_increment hq hrpos hellpos hEvent
    have hinc : (1 - 1 / (q : ℝ)) * b₁ < S₁ - S₀ := by
      exact (lil_lower_threshold_ge_scale hq k).trans_lt
        (hthreshold.trans_lt hincRaw)
    have hneg : -S₀ / b₀ ≤ 1 + 6 / (q : ℝ) := by
      simpa only [Xneg, Pi.neg_apply, Finset.sum_neg_distrib, S₀, b₀] using hnegRaw
    have hnegMul : -S₀ ≤ (1 + 6 / (q : ℝ)) * b₀ :=
      (div_le_iff₀ hb₀0).1 hneg
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hcoef : (1 + 6 / (q : ℝ)) * (1 / (100 * (q : ℝ))) ≤
        1 / (q : ℝ) := by
      field_simp [hq0.ne']
      nlinarith
    have hcost : (1 + 6 / (q : ℝ)) * b₀ ≤ (1 / (q : ℝ)) * b₁ := by
      calc
        (1 + 6 / (q : ℝ)) * b₀ ≤
            (1 + 6 / (q : ℝ)) * ((1 / (100 * (q : ℝ))) * b₁) := by
          apply mul_le_mul_of_nonneg_left (lil_lower_prev_scale hq k)
          positivity
        _ = ((1 + 6 / (q : ℝ)) * (1 / (100 * (q : ℝ)))) * b₁ := by ring
        _ ≤ (1 / (q : ℝ)) * b₁ :=
          mul_le_mul_of_nonneg_right hcoef hb₁0.le
    have hS₀ : -(1 / (q : ℝ) * b₁) ≤ S₀ := by linarith
    apply (le_div_iff₀ hb₁0).2
    calc
      (1 - 2 / (q : ℝ)) * b₁ =
          (1 - 1 / (q : ℝ)) * b₁ + -(1 / (q : ℝ) * b₁) := by ring
      _ ≤ (S₁ - S₀) + S₀ := add_le_add hinc.le hS₀
      _ = ∑ j ∈ Finset.range (lilLowerN q (k + 1)), X j ω := by
        dsimp only [S₀, S₁]
        ring
  rw [Filter.frequently_atTop]
  intro n
  obtain ⟨k, hk, hn⟩ :=
    (hkfreq.and_eventually (hNsucc.eventually_ge_atTop n)).exists
  exact ⟨lilLowerN q (k + 1), hn, hk⟩

private lemma lil_limsup_eq_one (u : ℕ → ℝ)
    (hupper : ∀ q : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      u n ≤ 1 + 6 / ((q + 1 : ℕ) : ℝ))
    (hlower : ∀ q : ℕ, ∃ᶠ n : ℕ in Filter.atTop,
      1 - 2 / ((q + 1 : ℕ) : ℝ) ≤ u n) :
    Filter.limsup u Filter.atTop = 1 := by
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u :=
    Filter.isBoundedUnder_of_eventually_le (hupper 0)
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop u :=
    Filter.IsCoboundedUnder.of_frequently_ge (hlower 0)
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨q, hq⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε / 6 by positivity)
    have hsmall : 6 / ((q + 1 : ℕ) : ℝ) ≤ ε := by
      simp only [Nat.cast_add, Nat.cast_one] at hq ⊢
      have := mul_le_mul_of_nonneg_left hq.le (show (0 : ℝ) ≤ 6 by norm_num)
      convert this using 1 <;> ring
    exact (Filter.limsup_le_of_le hcobdd (hupper q)).trans (by linarith)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨q, hq⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε / 2 by positivity)
    have hsmall : 2 / ((q + 1 : ℕ) : ℝ) ≤ ε := by
      simp only [Nat.cast_add, Nat.cast_one] at hq ⊢
      have := mul_le_mul_of_nonneg_left hq.le (show (0 : ℝ) ≤ 2 by norm_num)
      convert this using 1 <;> ring
    have hhit := Filter.le_limsup_of_frequently_le (hlower q) hbdd
    linarith

private lemma lil_liminf_eq_neg_one (u : ℕ → ℝ)
    (hupperNeg : ∀ q : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      -u n ≤ 1 + 6 / ((q + 1 : ℕ) : ℝ))
    (hlowerNeg : ∀ q : ℕ, ∃ᶠ n : ℕ in Filter.atTop,
      1 - 2 / ((q + 1 : ℕ) : ℝ) ≤ -u n) :
    Filter.liminf u Filter.atTop = -1 := by
  let v : ℕ → ℝ := fun n ↦ -u n
  have hv : Filter.limsup v Filter.atTop = 1 :=
    lil_limsup_eq_one v hupperNeg hlowerNeg
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop v :=
    Filter.isBoundedUnder_of_eventually_le (hupperNeg 0)
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop v :=
    Filter.IsCoboundedUnder.of_frequently_ge (hlowerNeg 0)
  have hanti : Antitone (fun x : ℝ ↦ -x) := fun _ _ h ↦ neg_le_neg h
  have hmap := hanti.map_limsup_of_continuousAt v continuousAt_neg hbdd hcobdd
  rw [hv] at hmap
  calc
    Filter.liminf u Filter.atTop =
        Filter.liminf ((fun x : ℝ ↦ -x) ∘ v) Filter.atTop := by
      apply Filter.liminf_congr
      exact Filter.Eventually.of_forall fun n ↦ by simp only [v, Function.comp_apply, neg_neg]
    _ = -1 := hmap.symm

/--
**Law of the iterated logarithm, square-integrable form.** Let $X_0, X_1, \dots$ be independent,
identically distributed, measurable real random variables on a probability space with
$\mathbb{E}[X_0^2] < \infty$, $\mathbb{E}[X_0] = 0$ and $\operatorname{Var}(X_0) = 1$, and let
$S_n = X_0 + \dots + X_{n-1}$. Then almost surely
$\limsup_{n \to \infty} S_n / \sqrt{2 n \log \log n} = 1$ and
$\liminf_{n \to \infty} S_n / \sqrt{2 n \log \log n} = -1$.

Integrability of $X_0$ is not assumed separately, since it follows from square integrability on a
probability space.
-/
public theorem law_of_the_iterated_logarithm_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (X n))
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ)
    (hMean : μ[X 0] = 0)
    (hVar : Var[X 0; μ] = 1) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n : ℕ =>
        (∑ i ∈ Finset.range n, X i ω) /
          Real.sqrt (2 * (n : ℝ) * Real.log (Real.log (n : ℝ)))) Filter.atTop = (1 : ℝ)
      ∧ Filter.liminf (fun n : ℕ =>
        (∑ i ∈ Finset.range n, X i ω) /
          Real.sqrt (2 * (n : ℝ) * Real.log (Real.log (n : ℝ)))) Filter.atTop = (-1 : ℝ) := by
  have hInt : Integrable (X 0) μ := hMemLp.integrable one_le_two
  let Xneg : ℕ → Ω → ℝ := fun n ↦ -X n
  have hXneg (n : ℕ) : Xneg n = (fun x : ℝ ↦ -x) ∘ X n := by
    funext ω
    simp only [Xneg, Pi.neg_apply, Function.comp_apply]
  have hMeasNeg : ∀ n, Measurable (Xneg n) := fun n ↦ (hMeas n).neg
  have hIndepNeg : iIndepFun Xneg μ := by
    rw [show Xneg = fun n ↦ (fun x : ℝ ↦ -x) ∘ X n by
      funext n
      exact hXneg n]
    exact hIndep.comp (fun _ : ℕ ↦ fun x : ℝ ↦ -x) (fun _ ↦ measurable_neg)
  have hIdentNeg : ∀ j, IdentDistrib (Xneg j) (Xneg 0) μ μ := by
    intro j
    rw [hXneg j, hXneg 0]
    exact (hIdent j).comp measurable_neg
  have hIntNeg : Integrable (Xneg 0) μ := by simpa only [Xneg] using hInt.neg
  have hMemLpNeg : MemLp (Xneg 0) 2 μ := by
    simpa only [Xneg] using hMemLp.neg
  have hMeanNeg : ∫ ω, Xneg 0 ω ∂μ = 0 := by
    change (∫ ω, -X 0 ω ∂μ) = 0
    rw [integral_neg, hMean, neg_zero]
  have hVarNeg : Var[Xneg 0; μ] = 1 := by
    change Var[fun ω ↦ -X 0 ω; μ] = 1
    rw [ProbabilityTheory.variance_fun_neg, hVar]
  have hUpperX : ∀ᵐ ω ∂μ, ∀ q : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      (∑ j ∈ Finset.range n, X j ω) / lilScale n ≤
        1 + 6 / ((q + 1 : ℕ) : ℝ) := by
    apply ae_all_iff.2
    intro q
    exact lil_ae_eventually_sum_le X hMeas hIndep hIdent hInt hMemLp hMean hVar
      (Nat.succ_pos q)
  have hLowerX : ∀ᵐ ω ∂μ, ∀ q : ℕ, ∃ᶠ n : ℕ in Filter.atTop,
      1 - 2 / ((q + 1 : ℕ) : ℝ) ≤
        (∑ j ∈ Finset.range n, X j ω) / lilScale n := by
    apply ae_all_iff.2
    intro q
    exact lil_ae_frequently_sum_ge X hMeas hIndep hIdent hInt hMemLp hMean hVar
      (Nat.succ_pos q)
  have hUpperNeg : ∀ᵐ ω ∂μ, ∀ q : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      (∑ j ∈ Finset.range n, Xneg j ω) / lilScale n ≤
        1 + 6 / ((q + 1 : ℕ) : ℝ) := by
    apply ae_all_iff.2
    intro q
    exact lil_ae_eventually_sum_le Xneg hMeasNeg hIndepNeg hIdentNeg hIntNeg hMemLpNeg
      hMeanNeg hVarNeg (Nat.succ_pos q)
  have hLowerNeg : ∀ᵐ ω ∂μ, ∀ q : ℕ, ∃ᶠ n : ℕ in Filter.atTop,
      1 - 2 / ((q + 1 : ℕ) : ℝ) ≤
        (∑ j ∈ Finset.range n, Xneg j ω) / lilScale n := by
    apply ae_all_iff.2
    intro q
    exact lil_ae_frequently_sum_ge Xneg hMeasNeg hIndepNeg hIdentNeg hIntNeg hMemLpNeg
      hMeanNeg hVarNeg (Nat.succ_pos q)
  filter_upwards [hUpperX, hLowerX, hUpperNeg, hLowerNeg] with ω hUX hLX hUN hLN
  let u : ℕ → ℝ := fun n ↦ (∑ j ∈ Finset.range n, X j ω) / lilScale n
  have huUpper : ∀ q : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      u n ≤ 1 + 6 / ((q + 1 : ℕ) : ℝ) := fun q ↦ by
    simpa only [u] using hUX q
  have huLower : ∀ q : ℕ, ∃ᶠ n : ℕ in Filter.atTop,
      1 - 2 / ((q + 1 : ℕ) : ℝ) ≤ u n := fun q ↦ by
    simpa only [u] using hLX q
  have huUpperNeg : ∀ q : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      -u n ≤ 1 + 6 / ((q + 1 : ℕ) : ℝ) := fun q ↦ by
    simpa only [u, Xneg, Pi.neg_apply, Finset.sum_neg_distrib, neg_div] using hUN q
  have huLowerNeg : ∀ q : ℕ, ∃ᶠ n : ℕ in Filter.atTop,
      1 - 2 / ((q + 1 : ℕ) : ℝ) ≤ -u n := fun q ↦ by
    simpa only [u, Xneg, Pi.neg_apply, Finset.sum_neg_distrib, neg_div] using hLN q
  have hsup : Filter.limsup u Filter.atTop = 1 :=
    lil_limsup_eq_one u huUpper huLower
  have hinf : Filter.liminf u Filter.atTop = -1 :=
    lil_liminf_eq_neg_one u huUpperNeg huLowerNeg
  let v : ℕ → ℝ := fun n ↦
    (∑ j ∈ Finset.range n, X j ω) /
      Real.sqrt (2 * (n : ℝ) * Real.log (Real.log (n : ℝ)))
  have huv : u =ᶠ[Filter.atTop] v := by
    filter_upwards [lil_eventually_scale_eq] with n hn
    simp only [u, v, hn]
  constructor
  · rw [← Filter.limsup_congr huv]
    exact hsup
  · rw [← Filter.liminf_congr huv]
    exact hinf

/--
**Law of the iterated logarithm.** Let $X_0, X_1, \dots$ be independent, identically distributed,
measurable real random variables on a probability space such that $X_0$ is integrable,
$\mathbb{E}[X_0^2] < \infty$, $\mathbb{E}[X_0] = 0$ and $\operatorname{Var}(X_0) = 1$, and let
$S_n = X_0 + \dots + X_{n-1}$. Then almost surely
$\limsup_{n \to \infty} S_n / \sqrt{2 n \log \log n} = 1$ and
$\liminf_{n \to \infty} S_n / \sqrt{2 n \log \log n} = -1$.

Proof: Hartman–Wintner truncation and exponential maximal bounds give the upper half; a CLT block
argument and the second Borel–Cantelli lemma give the lower half.

Proves `Wanted` entry `law_of_the_iterated_logarithm`.

Source: A. Y. Khinchin 1924, A. N. Kolmogorov 1929, P. Hartman and A. Wintner, On the law of
the iterated logarithm, Amer. J. Math. 63 (1941) 169–176; textbook in Durrett, Probability Theory
and Examples, 5th ed., Foundations of Modern Probability (Hartman-Wintner LIL). Lean i.i.d.
mean-zero variance-one normalized `√(2 n log log n)` form.
-/
public theorem law_of_the_iterated_logarithm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (X n))
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hInt : Integrable (X 0) μ)
    (hMemLp : MemLp (X 0) 2 μ)
    (hMean : μ[X 0] = 0)
    (hVar : Var[X 0; μ] = 1) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n : ℕ =>
        (∑ i ∈ Finset.range n, X i ω) /
          Real.sqrt (2 * (n : ℝ) * Real.log (Real.log (n : ℝ)))) Filter.atTop = (1 : ℝ)
      ∧ Filter.liminf (fun n : ℕ =>
        (∑ i ∈ Finset.range n, X i ω) /
          Real.sqrt (2 * (n : ℝ) * Real.log (Real.log (n : ℝ)))) Filter.atTop = (-1 : ℝ) := by
  exact law_of_the_iterated_logarithm_of_memLp X hMeas hIndep hIdent hMemLp hMean hVar

end MathlibExt.Probability.LawIteratedLogarithmWanted
