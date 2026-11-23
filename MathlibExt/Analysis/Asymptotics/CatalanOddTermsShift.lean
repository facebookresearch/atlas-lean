/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Choose.Basic

import MathlibExt.Analysis.Asymptotics.CatalanAsymptoticExpansion
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The unique even-power shift for Catalan asymptotics

This file proves that `3/4` is the unique shift for which the normalized
Catalan numbers have an all-orders expansion containing only even powers.
-/

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

private noncomputable def catalanOddShiftLogCoeff (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ (j + 2) *
    (Polynomial.aeval (-1 / 4 : ℝ) (Polynomial.bernoulli (j + 2)) -
      Polynomial.aeval (5 / 4 : ℝ) (Polynomial.bernoulli (j + 2))) /
      ((j + 1 : ℕ) * (j + 2 : ℕ))

private lemma catalanOddShift_bernoulli_aeval_rat (n : ℕ) (x : ℚ) :
    Polynomial.aeval (x : ℝ) (Polynomial.bernoulli n) =
      algebraMap ℚ ℝ ((Polynomial.bernoulli n).eval x) := by
  rw [Polynomial.aeval_def]
  rw [Polynomial.eval₂_eq_eval_map]
  exact Polynomial.eval_map_apply (f := algebraMap ℚ ℝ)
    (p := Polynomial.bernoulli n) x

private lemma catalanOddShift_logCoeff_even_zero (r : ℕ) :
    catalanOddShiftLogCoeff (2 * r) = 0 := by
  have hreflect := Polynomial.bernoulli_eval_one_sub (2 * r + 2) (-1 / 4 : ℚ)
  have heven : Even (2 * r + 2) := ⟨r + 1, by omega⟩
  norm_num [heven.neg_one_pow] at hreflect
  have heq : (Polynomial.bernoulli (2 * r + 2)).eval (-1 / 4 : ℚ) =
      (Polynomial.bernoulli (2 * r + 2)).eval (5 / 4 : ℚ) := by
    rw [hreflect]
    norm_num
  rw [catalanOddShiftLogCoeff,
    show (-1 / 4 : ℝ) = ((-1 / 4 : ℚ) : ℝ) by norm_num,
    show (5 / 4 : ℝ) = ((5 / 4 : ℚ) : ℝ) by norm_num,
    catalanOddShift_bernoulli_aeval_rat,
    catalanOddShift_bernoulli_aeval_rat, heq, sub_self, mul_zero, zero_div]

private noncomputable def catalanOddShiftLogPoly (M : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, catalanOddShiftLogCoeff j * x ^ (j + 1)

private noncomputable def catalanOddShiftExpCoeff (M k : ℕ) : ℝ :=
  iteratedDeriv k (fun x : ℝ => Real.exp (catalanOddShiftLogPoly M x)) 0 /
    k.factorial

private lemma catalanOddShift_logPoly_neg (M : ℕ) (x : ℝ) :
    catalanOddShiftLogPoly M (-x) = catalanOddShiftLogPoly M x := by
  apply Finset.sum_congr rfl
  intro j hj
  rcases Nat.even_or_odd j with heven | hodd
  · obtain ⟨r, hr⟩ := heven
    have hjr : j = 2 * r := by omega
    subst j
    rw [show r + r = 2 * r by omega, catalanOddShift_logCoeff_even_zero]
    simp
  · have hevenSucc : Even (j + 1) := by
      obtain ⟨r, hr⟩ := hodd
      exact ⟨r + 1, by omega⟩
    rw [neg_pow, hevenSucc.neg_one_pow, one_mul]

private lemma catalanOddShift_logPoly_analyticAt (M : ℕ) (x : ℝ) :
    AnalyticAt ℝ (catalanOddShiftLogPoly M) x := by
  unfold catalanOddShiftLogPoly
  fun_prop

private lemma catalanOddShift_expCoeff_odd_zero (M r : ℕ) :
    catalanOddShiftExpCoeff M (2 * r + 1) = 0 := by
  let f : ℝ → ℝ := fun x => Real.exp (catalanOddShiftLogPoly M x)
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    dsimp only [f]
    rw [catalanOddShift_logPoly_neg]
  have hderivEq : iteratedDeriv (2 * r + 1) (fun x => f (-x)) 0 =
      iteratedDeriv (2 * r + 1) f 0 := by
    apply Filter.EventuallyEq.iteratedDeriv_eq
    exact Filter.Eventually.of_forall heven
  have hcomp := iteratedDeriv_comp_neg (2 * r + 1) f 0
  have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
  rw [hderivEq, neg_zero, hodd.neg_one_pow, neg_one_smul] at hcomp
  have hz : iteratedDeriv (2 * r + 1) f 0 = 0 := by linarith
  rw [catalanOddShiftExpCoeff]
  change iteratedDeriv (2 * r + 1) f 0 / ((2 * r + 1).factorial : ℕ) = 0
  rw [hz, zero_div]

private lemma catalanOddShift_choose_div_eq_catalan (n : ℕ) :
    (Nat.choose (2 * n) n : ℝ) / ((n : ℝ) + 1) = catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  rw [Nat.centralBinom_eq_two_mul_choose] at h
  rw [div_eq_iff (by positivity : (n : ℝ) + 1 ≠ 0)]
  have h' : (Nat.choose (2 * n) n : ℝ) =
      (catalan n : ℝ) * ((n : ℝ) + 1) := by
    norm_cast
    simpa [mul_comm] using h.symm
  simpa [mul_comm] using h'

private lemma catalanOddShift_sqrt_cube_eq_rpow {x : ℝ} (hx : 0 < x) :
    Real.sqrt (Real.pi * x ^ 3) =
      Real.sqrt Real.pi * Real.rpow x ((3 : ℝ) / 2) := by
  rw [Real.sqrt_mul Real.pi_pos.le,
    show x ^ 3 = x ^ 2 * x by ring,
    Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx.le]
  have h32 : ((3 : ℝ) / 2) = 1 + 1 / 2 := by norm_num
  have hrpow : Real.rpow x ((3 : ℝ) / 2) = x * Real.sqrt x := by
    rw [h32]
    calc
      Real.rpow x (1 + 1 / 2) =
          Real.rpow x 1 * Real.rpow x (1 / 2) :=
        Real.rpow_add hx (1 : ℝ) (1 / 2 : ℝ)
      _ = x * Real.sqrt x := by
        have hone : Real.rpow x 1 = x := Real.rpow_one x
        have hhalf : Real.rpow x (1 / 2) = Real.sqrt x :=
          (Real.sqrt_eq_rpow x).symm
        rw [hone, hhalf]
  rw [hrpow]

private lemma catalanOddShift_scaled_eq (c : ℝ) (n : ℕ)
    (hx : 0 < (n : ℝ) + c) :
    (Nat.choose (2 * n) n : ℝ) / ((n : ℝ) + 1) *
        Real.sqrt Real.pi * Real.rpow ((n : ℝ) + c) ((3 : ℝ) / 2) /
        (4 : ℝ) ^ n =
      (catalan n : ℝ) * Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) /
        (4 : ℝ) ^ n := by
  rw [catalanOddShift_choose_div_eq_catalan,
    catalanOddShift_sqrt_cube_eq_rpow hx]
  ring

private noncomputable def catalanOddShiftU (n : ℕ) : ℝ := (n : ℝ) + 3 / 4

private noncomputable def catalanOddShiftY (n : ℕ) : ℝ := 1 / catalanOddShiftU n

private noncomputable def catalanOddShiftG (n : ℕ) : ℝ :=
  (catalan n : ℝ) * Real.sqrt (Real.pi * catalanOddShiftU n ^ 3) / (4 : ℝ) ^ n

private lemma catalanOddShift_u_pos (n : ℕ) : 0 < catalanOddShiftU n := by
  unfold catalanOddShiftU
  positivity

private lemma catalanOddShift_u_tendsto_atTop :
    Filter.Tendsto catalanOddShiftU Filter.atTop Filter.atTop := by
  exact Filter.tendsto_atTop_add_const_right Filter.atTop (3 / 4 : ℝ)
    tendsto_natCast_atTop_atTop

private lemma catalanOddShift_y_tendsto_zero :
    Filter.Tendsto catalanOddShiftY Filter.atTop (nhds 0) := by
  exact catalanOddShift_u_tendsto_atTop.const_div_atTop 1

private lemma catalanOddShift_g_pos (n : ℕ) : 0 < catalanOddShiftG n := by
  unfold catalanOddShiftG
  have hProduct : 0 < (n + 1) * catalan n := by
    rw [succ_mul_catalan_eq_centralBinom]
    exact Nat.centralBinom_pos n
  have hCatalan : (0 : ℝ) < catalan n := by
    exact_mod_cast Nat.pos_of_mul_pos_left hProduct
  have hsqrt : 0 < Real.sqrt (Real.pi * catalanOddShiftU n ^ 3) := by
    exact Real.sqrt_pos.mpr <|
      mul_pos Real.pi_pos (pow_pos (catalanOddShift_u_pos n) 3)
  exact div_pos (mul_pos hCatalan hsqrt) (by positivity)

private theorem catalanOddShift_log_expansion (M : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => catalanOddShiftU n ^ M *
        (Real.log (catalanOddShiftG n) -
          catalanOddShiftLogPoly M (catalanOddShiftY n)))
      Filter.atTop (nhds 0) := by
  have h := tendsto_pow_mul_log_catalan_sub_bernoulli_sum (3 / 4) M
  refine h.congr' ?_
  filter_upwards with n
  unfold catalanOddShiftU catalanOddShiftY catalanOddShiftG
  unfold catalanOddShiftLogPoly catalanOddShiftLogCoeff
  norm_num only [show (1 / 2 : ℝ) - 3 / 4 = -1 / 4 by norm_num,
    show (2 : ℝ) - 3 / 4 = 5 / 4 by norm_num]
  simp only [catalanOddShiftU, one_div_pow]

private lemma catalanOddShift_logPoly_tendsto_zero (M : ℕ) :
    Filter.Tendsto (fun n : ℕ =>
      catalanOddShiftLogPoly M (catalanOddShiftY n))
      Filter.atTop (nhds 0) := by
  have h := (catalanOddShift_logPoly_analyticAt M 0).continuousAt.tendsto.comp
    catalanOddShift_y_tendsto_zero
  have hzero : catalanOddShiftLogPoly M 0 = 0 := by
    simp [catalanOddShiftLogPoly]
  rw [hzero] at h
  exact h

private lemma catalanOddShift_logError_tendsto_zero (M : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => Real.log (catalanOddShiftG n) -
        catalanOddShiftLogPoly M (catalanOddShiftY n))
      Filter.atTop (nhds 0) := by
  have hg := tendsto_pow_mul_log_catalan_sub_bernoulli_sum (3 / 4) 0
  simp only [pow_zero, one_mul, Finset.sum_range_zero, sub_zero] at hg
  have hg' : Filter.Tendsto (fun n : ℕ => Real.log (catalanOddShiftG n))
      Filter.atTop (nhds 0) := by
    simpa [catalanOddShiftG, catalanOddShiftU] using hg
  simpa only [sub_zero] using hg'.sub (catalanOddShift_logPoly_tendsto_zero M)

private lemma catalanOddShift_exp_log_remainder (M : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => catalanOddShiftU n ^ M *
        (catalanOddShiftG n -
          Real.exp (catalanOddShiftLogPoly M (catalanOddShiftY n))))
      Filter.atTop (nhds 0) := by
  let d : ℕ → ℝ := fun n => Real.log (catalanOddShiftG n) -
    catalanOddShiftLogPoly M (catalanOddShiftY n)
  have hd0 : Filter.Tendsto d Filter.atTop (nhds 0) :=
    catalanOddShift_logError_tendsto_zero M
  have hscaled : Filter.Tendsto (fun n => catalanOddShiftU n ^ M * d n)
      Filter.atTop (nhds 0) := catalanOddShift_log_expansion M
  have hexpO : (fun x : ℝ => Real.exp x - 1) =O[nhds 0] (fun x => x) := by
    simpa using Real.exp_sub_sum_range_isBigO_pow 1
  have hexpOd : (fun n => Real.exp (d n) - 1) =O[Filter.atTop] d := by
    apply (hexpO.comp_tendsto hd0).congr
    · intro n
      rfl
    · intro n
      rfl
  have hscaledO :
      (fun n => catalanOddShiftU n ^ M * (Real.exp (d n) - 1)) =O[Filter.atTop]
        (fun n => catalanOddShiftU n ^ M * d n) :=
    (Asymptotics.isBigO_refl (fun n => catalanOddShiftU n ^ M)
      Filter.atTop).mul hexpOd
  have hscaledExp : Filter.Tendsto
      (fun n => catalanOddShiftU n ^ M * (Real.exp (d n) - 1))
      Filter.atTop (nhds 0) := hscaledO.trans_tendsto hscaled
  have hpolyExp : Filter.Tendsto
      (fun n => Real.exp (catalanOddShiftLogPoly M (catalanOddShiftY n)))
      Filter.atTop (nhds 1) := by
    simpa only [Real.exp_zero] using (catalanOddShift_logPoly_tendsto_zero M).rexp
  have hproduct := hpolyExp.mul hscaledExp
  rw [mul_zero] at hproduct
  refine Filter.Tendsto.congr (fun n => ?_) hproduct
  have hlog : Real.log (catalanOddShiftG n) =
      catalanOddShiftLogPoly M (catalanOddShiftY n) + d n := by
    dsimp only [d]
    ring
  rw [← Real.exp_log (catalanOddShift_g_pos n), hlog, Real.exp_add]
  ring

private lemma catalanOddShift_scaled_y_succ_tendsto_zero (N : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => catalanOddShiftU n ^ N *
        ‖catalanOddShiftY n‖ ^ (N + 1))
      Filter.atTop (nhds 0) := by
  refine Filter.Tendsto.congr (fun n => ?_) catalanOddShift_y_tendsto_zero
  have hu := (catalanOddShift_u_pos n).ne'
  symm
  unfold catalanOddShiftY
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (catalanOddShift_u_pos n))]
  field_simp
  rw [← pow_succ, ← mul_pow]
  simp [hu]

private lemma catalanOddShift_taylor_remainder (M N : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => catalanOddShiftU n ^ N *
        (Real.exp (catalanOddShiftLogPoly M (catalanOddShiftY n)) -
          ∑ k ∈ Finset.range (N + 1),
            catalanOddShiftExpCoeff M k * catalanOddShiftY n ^ k))
      Filter.atTop (nhds 0) := by
  have hf : AnalyticAt ℝ
      (fun x => Real.exp (catalanOddShiftLogPoly M x)) 0 :=
    (catalanOddShift_logPoly_analyticAt M 0).rexp
  have hO := hf.hasFPowerSeriesAt.isBigO_sub_partialSum_pow (N + 1)
  have hOY :
      (fun n : ℕ =>
        Real.exp (catalanOddShiftLogPoly M (catalanOddShiftY n)) -
        ∑ k ∈ Finset.range (N + 1),
          catalanOddShiftExpCoeff M k * catalanOddShiftY n ^ k)
        =O[Filter.atTop]
      (fun n : ℕ => ‖catalanOddShiftY n‖ ^ (N + 1)) := by
    apply (hO.comp_tendsto catalanOddShift_y_tendsto_zero).congr
    · intro n
      simp only [Function.comp_apply, zero_add,
        FormalMultilinearSeries.partialSum,
        FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
        catalanOddShiftExpCoeff]
    · intro n
      rfl
  have hscaledO :=
    (Asymptotics.isBigO_refl (fun n : ℕ => catalanOddShiftU n ^ N)
      Filter.atTop).mul hOY
  have hscaled := hscaledO.trans_tendsto
    (catalanOddShift_scaled_y_succ_tendsto_zero N)
  exact hscaled

private lemma catalanOddShift_downscale {f : ℕ → ℝ} {M N : ℕ} (hNM : N ≤ M)
    (h : Filter.Tendsto (fun n => catalanOddShiftU n ^ M * f n)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => catalanOddShiftU n ^ N * f n)
      Filter.atTop (nhds 0) := by
  have hy := catalanOddShift_y_tendsto_zero.pow (M - N)
  have hproduct := hy.mul h
  rw [mul_zero] at hproduct
  refine Filter.Tendsto.congr (fun n => ?_) hproduct
  unfold catalanOddShiftY
  rw [show M = N + (M - N) by omega, pow_add, one_div_pow]
  have hu := (catalanOddShift_u_pos n).ne'
  field_simp
  rw [show N + (M - N) - N = M - N by omega]

private theorem catalanOddShift_expansionWith (M N : ℕ) (hNM : N ≤ M) :
    Filter.Tendsto
      (fun n : ℕ => catalanOddShiftU n ^ N *
        (catalanOddShiftG n -
          ∑ k ∈ Finset.range (N + 1),
            catalanOddShiftExpCoeff M k * catalanOddShiftY n ^ k))
      Filter.atTop (nhds 0) := by
  have hlog := catalanOddShift_downscale hNM
    (catalanOddShift_exp_log_remainder M)
  have htaylor := catalanOddShift_taylor_remainder M N
  have hsum := hlog.add htaylor
  rw [add_zero] at hsum
  refine Filter.Tendsto.congr (fun n => ?_) hsum
  ring

private lemma catalanOddShift_expCoeff_compatible (M k : ℕ) (hkM : k ≤ M) :
    catalanOddShiftExpCoeff M k = catalanOddShiftExpCoeff k k := by
  induction k using Nat.strong_induction_on generalizing M with
  | h k ih =>
      have hprefix (n : ℕ) :
          ∑ i ∈ Finset.range k,
              catalanOddShiftExpCoeff M i * catalanOddShiftY n ^ i =
            ∑ i ∈ Finset.range k,
              catalanOddShiftExpCoeff k i * catalanOddShiftY n ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hik : i < k := Finset.mem_range.mp hi
        rw [ih i hik M (le_trans (Nat.le_of_lt hik) hkM),
          ih i hik k (Nat.le_of_lt hik)]
      have hM := catalanOddShift_expansionWith M k hkM
      have hk := catalanOddShift_expansionWith k k le_rfl
      have hdiff := hM.sub hk
      simp only [sub_zero] at hdiff
      have hconst : Filter.Tendsto
          (fun _ : ℕ =>
            catalanOddShiftExpCoeff k k - catalanOddShiftExpCoeff M k)
          Filter.atTop (nhds 0) := by
        refine Filter.Tendsto.congr (fun n => ?_) hdiff
        rw [Finset.sum_range_succ, Finset.sum_range_succ, hprefix n]
        have hsumcomm :
            ∑ i ∈ Finset.range k,
                catalanOddShiftY n ^ i * catalanOddShiftExpCoeff k i =
              ∑ i ∈ Finset.range k,
                catalanOddShiftExpCoeff k i * catalanOddShiftY n ^ i := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        have hy : catalanOddShiftU n ^ k * catalanOddShiftY n ^ k = 1 := by
          have hu := (catalanOddShift_u_pos n).ne'
          unfold catalanOddShiftY
          rw [← mul_pow]
          field_simp
          simp
        ring_nf
        rw [hsumcomm, hy]
        ring
      have heq : catalanOddShiftExpCoeff k k -
          catalanOddShiftExpCoeff M k = 0 :=
        tendsto_nhds_unique tendsto_const_nhds hconst
      linarith

private noncomputable def catalanOddShiftCoeff (k : ℕ) : ℝ :=
  catalanOddShiftExpCoeff k k

private lemma catalanOddShift_coeff_odd_zero (r : ℕ) :
    catalanOddShiftCoeff (2 * r + 1) = 0 := by
  exact catalanOddShift_expCoeff_odd_zero (2 * r + 1) r

private theorem catalanOddShift_even_expansion (N : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => catalanOddShiftU n ^ N *
        (catalanOddShiftG n -
          ∑ k ∈ Finset.range (N + 1),
            catalanOddShiftCoeff k * catalanOddShiftY n ^ k))
      Filter.atTop (nhds 0) := by
  have h := catalanOddShift_expansionWith N N le_rfl
  have hsum (n : ℕ) :
      ∑ k ∈ Finset.range (N + 1),
          catalanOddShiftExpCoeff N k * catalanOddShiftY n ^ k =
        ∑ k ∈ Finset.range (N + 1),
          catalanOddShiftCoeff k * catalanOddShiftY n ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [catalanOddShiftCoeff,
      catalanOddShift_expCoeff_compatible N k (by
        have := Finset.mem_range.mp hk
        omega)]
  refine Filter.Tendsto.congr (fun n => ?_) h
  rw [← hsum n]

private noncomputable def catalanOddShiftF (c : ℝ) (n : ℕ) : ℝ :=
  (Nat.choose (2 * n) n : ℝ) / ((n : ℝ) + 1) * Real.sqrt Real.pi *
    Real.rpow ((n : ℝ) + c) ((3 : ℝ) / 2) / (4 : ℝ) ^ n

private lemma catalanOddShift_f_tendsto_one (c : ℝ) :
    Filter.Tendsto (catalanOddShiftF c) Filter.atTop (nhds 1) := by
  have hxTop : Filter.Tendsto (fun n : ℕ => (n : ℝ) + c)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop c tendsto_natCast_atTop_atTop
  have hlog := tendsto_pow_mul_log_catalan_sub_bernoulli_sum c 0
  simp only [pow_zero, one_mul, Finset.sum_range_zero, sub_zero] at hlog
  have hexp := hlog.rexp
  rw [Real.exp_zero] at hexp
  have hG : Filter.Tendsto (fun n : ℕ =>
      (catalan n : ℝ) * Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) /
        (4 : ℝ) ^ n) Filter.atTop (nhds 1) := by
    refine Filter.Tendsto.congr' ?_ hexp
    filter_upwards [hxTop.eventually (Filter.eventually_gt_atTop 0)] with n hn
    have hProduct : 0 < (n + 1) * catalan n := by
      rw [succ_mul_catalan_eq_centralBinom]
      exact Nat.centralBinom_pos n
    have hCatalan : (0 : ℝ) < catalan n := by
      exact_mod_cast Nat.pos_of_mul_pos_left hProduct
    rw [Real.exp_log]
    exact div_pos
      (mul_pos hCatalan
        (Real.sqrt_pos.mpr (mul_pos Real.pi_pos (pow_pos hn 3))))
      (by positivity)
  refine Filter.Tendsto.congr' ?_ hG
  filter_upwards [hxTop.eventually (Filter.eventually_gt_atTop 0)] with n hn
  exact (catalanOddShift_scaled_eq c n hn).symm

private lemma catalanOddShift_expansion_a0 (c : ℝ) (a : ℕ → ℝ)
    (hexp : ∀ N : ℕ,
      Filter.Tendsto
        (fun n : ℕ => ((n : ℝ) + c) ^ N *
          (catalanOddShiftF c n -
            ∑ k ∈ Finset.range (N + 1), a k / ((n : ℝ) + c) ^ k))
        Filter.atTop (nhds 0)) :
    a 0 = 1 := by
  have h0 := hexp 0
  simp only [zero_add, pow_zero, one_mul, Finset.sum_range_one, div_one] at h0
  have hlim := h0.add (tendsto_const_nhds (x := a 0))
  rw [zero_add] at hlim
  have hlim' : Filter.Tendsto (catalanOddShiftF c) Filter.atTop (nhds (a 0)) := by
    refine Filter.Tendsto.congr (fun n => ?_) hlim
    simp
  exact tendsto_nhds_unique hlim' (catalanOddShift_f_tendsto_one c)

private lemma catalanOddShift_first_remainder (c : ℝ) (a : ℕ → ℝ)
    (hexp : ∀ N : ℕ,
      Filter.Tendsto
        (fun n : ℕ => ((n : ℝ) + c) ^ N *
          (catalanOddShiftF c n -
            ∑ k ∈ Finset.range (N + 1), a k / ((n : ℝ) + c) ^ k))
        Filter.atTop (nhds 0))
    (ha0 : a 0 = 1) (ha1 : a 1 = 0) :
    Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) + c) * (catalanOddShiftF c n - 1))
      Filter.atTop (nhds 0) := by
  have h := hexp 1
  simpa [Finset.sum_range_succ, ha0, ha1] using h

private lemma catalanOddShift_log_first_remainder (c : ℝ) (a : ℕ → ℝ)
    (hexp : ∀ N : ℕ,
      Filter.Tendsto
        (fun n : ℕ => ((n : ℝ) + c) ^ N *
          (catalanOddShiftF c n -
            ∑ k ∈ Finset.range (N + 1), a k / ((n : ℝ) + c) ^ k))
        Filter.atTop (nhds 0))
    (ha0 : a 0 = 1) (ha1 : a 1 = 0) :
    Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) + c) * Real.log (catalanOddShiftF c n))
      Filter.atTop (nhds 0) := by
  have hlogO : (fun x : ℝ => Real.log x) =O[nhds 1] (fun x => x - 1) := by
    simpa using (Real.hasDerivAt_log one_ne_zero).isBigO_sub
  have hlogOF := hlogO.comp_tendsto (catalanOddShift_f_tendsto_one c)
  have hscaledO :=
    (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ) + c)
      Filter.atTop).mul hlogOF
  exact hscaledO.trans_tendsto (catalanOddShift_first_remainder c a hexp ha0 ha1)

private noncomputable def catalanOddShiftFirstLogCoeff (c : ℝ) : ℝ :=
  (Polynomial.aeval (1 / 2 - c) (Polynomial.bernoulli 2) -
    Polynomial.aeval (2 - c) (Polynomial.bernoulli 2)) / 2

private lemma catalanOddShift_log_first_expansion (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) + c) *
        (Real.log (catalanOddShiftF c n) -
          catalanOddShiftFirstLogCoeff c / ((n : ℝ) + c)))
      Filter.atTop (nhds 0) := by
  have h := tendsto_pow_mul_log_catalan_sub_bernoulli_sum c 1
  have hG : Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) + c) *
        (Real.log ((catalan n : ℝ) *
            Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) / (4 : ℝ) ^ n) -
          catalanOddShiftFirstLogCoeff c / ((n : ℝ) + c)))
      Filter.atTop (nhds 0) := by
    simpa [catalanOddShiftFirstLogCoeff, Finset.sum_range_succ,
      div_eq_mul_inv] using h
  have hxTop : Filter.Tendsto (fun n : ℕ => (n : ℝ) + c)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop c tendsto_natCast_atTop_atTop
  refine Filter.Tendsto.congr' ?_ hG
  filter_upwards [hxTop.eventually (Filter.eventually_gt_atTop 0)] with n hn
  rw [catalanOddShiftF, catalanOddShift_scaled_eq c n hn]

private lemma catalanOddShift_firstLogCoeff_zero (c : ℝ) (a : ℕ → ℝ)
    (hexp : ∀ N : ℕ,
      Filter.Tendsto
        (fun n : ℕ => ((n : ℝ) + c) ^ N *
          (catalanOddShiftF c n -
            ∑ k ∈ Finset.range (N + 1), a k / ((n : ℝ) + c) ^ k))
        Filter.atTop (nhds 0))
    (ha0 : a 0 = 1) (ha1 : a 1 = 0) :
    catalanOddShiftFirstLogCoeff c = 0 := by
  have hsmall := catalanOddShift_log_first_remainder c a hexp ha0 ha1
  have hexpLog := catalanOddShift_log_first_expansion c
  have hdiff := hsmall.sub hexpLog
  simp only [sub_zero] at hdiff
  have hxTop : Filter.Tendsto (fun n : ℕ => (n : ℝ) + c)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop c tendsto_natCast_atTop_atTop
  have hconst : Filter.Tendsto
      (fun _ : ℕ => catalanOddShiftFirstLogCoeff c)
      Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hdiff
    filter_upwards [hxTop.eventually (Filter.eventually_gt_atTop 0)] with n hn
    have hne : (n : ℝ) + c ≠ 0 := hn.ne'
    field_simp
    ring
  exact tendsto_nhds_unique tendsto_const_nhds hconst

private lemma catalanOddShift_firstLogCoeff_eq (c : ℝ) :
    catalanOddShiftFirstLogCoeff c = 3 * c / 2 - 9 / 8 := by
  unfold catalanOddShiftFirstLogCoeff
  rw [Polynomial.bernoulli_def]
  norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one,
    bernoulli_two, Polynomial.aeval_def]
  ring

/--
**Uniqueness of the even-power shift in Catalan asymptotics.** Let
$C_n = \binom{2n}{n} / (n + 1)$ be the $n$-th Catalan number. For a real number $\alpha$, there is
a real sequence $(a_k)_{k \ge 0}$ with $a_{2k+1} = 0$ for every $k$ such that, for every
$N \ge 0$, the difference
$C_n \sqrt{\pi} \, (n + \alpha)^{3/2} / 4^n - \sum_{k=0}^{N} a_k (n + \alpha)^{-k}$ is
$o\left((n + \alpha)^{-N}\right)$ as $n \to \infty$, if and only if $\alpha = 3/4$.

Elezović phrases this as the expansion "containing only odd terms"; the condition meant is that
the odd-indexed coefficients vanish: his displayed series for $\alpha = 3/4$ has only even powers,
and his proof obtains $\alpha = 3/4$ by setting the first odd coefficient to zero.

Proof: The reverse implication exponentiates the all-orders logarithmic expansion of the Catalan
numbers and uses the reflection symmetry of the Bernoulli polynomials to eliminate odd powers. The
first logarithmic coefficient gives uniqueness, following Elezović.

Proves `Wanted` entry `catalan_odd_terms_shift_unique`.

Source: Neven Elezović, "Asymptotic Expansions of Central Binomial
Coefficients and Catalan Numbers," Journal of Integer Sequences 17 (2014),
Article 14.2.1, Corollary, lines 568–578,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Elezovic/elezovic5.tex
-/
public theorem catalan_odd_terms_shift_unique :
    ∀ α : ℝ,
      (∃ a : ℕ → ℝ,
        (∀ N : ℕ,
          Filter.Tendsto
            (fun n : ℕ =>
              ((n : ℝ) + α) ^ N *
                (((Nat.choose (2 * n) n : ℝ) / ((n : ℝ) + 1) *
                    Real.sqrt Real.pi *
                    Real.rpow ((n : ℝ) + α) ((3 : ℝ) / 2) /
                    (4 : ℝ) ^ n) -
                  ∑ k ∈ Finset.range (N + 1), a k / ((n : ℝ) + α) ^ k))
            Filter.atTop (nhds 0)) ∧
        (∀ k : ℕ, a (2 * k + 1) = 0)) ↔
      α = (3 : ℝ) / 4 := by
  intro α
  constructor
  · rintro ⟨a, hexp, hodd⟩
    have hexpF : ∀ N : ℕ,
        Filter.Tendsto
          (fun n : ℕ => ((n : ℝ) + α) ^ N *
            (catalanOddShiftF α n -
              ∑ k ∈ Finset.range (N + 1), a k / ((n : ℝ) + α) ^ k))
          Filter.atTop (nhds 0) := by
      intro N
      simpa only [catalanOddShiftF] using hexp N
    have ha0 : a 0 = 1 := catalanOddShift_expansion_a0 α a hexpF
    have ha1 : a 1 = 0 := by simpa using hodd 0
    have hc := catalanOddShift_firstLogCoeff_zero α a hexpF ha0 ha1
    rw [catalanOddShift_firstLogCoeff_eq] at hc
    linarith
  · intro hα
    subst α
    refine ⟨catalanOddShiftCoeff, ?_, catalanOddShift_coeff_odd_zero⟩
    intro N
    have h := catalanOddShift_even_expansion N
    refine Filter.Tendsto.congr (fun n => ?_) h
    unfold catalanOddShiftG catalanOddShiftY catalanOddShiftU
    rw [← catalanOddShift_scaled_eq (3 / 4) n (by positivity)]
    simp only [one_mul, inv_pow, div_eq_mul_inv]

end MetaMathlibExt
