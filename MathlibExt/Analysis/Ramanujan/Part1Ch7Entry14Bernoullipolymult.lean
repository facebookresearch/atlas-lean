/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
import MathlibExt.Analysis.Ramanujan.Part1Ch7DirichletBeta
public import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry13Bernoullipolyadd
public import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import MathlibExt.Analysis.SpecialFunctions.ExpSubOneMittagLeffler

/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 14

This file proves the convergence and finite-order asymptotic expansion of Ramanujan's
Bernoulli-polynomial series in terms of the Stieltjes constants.
-/

@[expose] public section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry14Bernoullipolymult

open scoped Nat Real BigOperators Interval
open Asymptotics Filter Finset Topology MeasureTheory

noncomputable section

private abbrev entry14Remainder := MetaMathlibExt.oneDivExpSubOneLaurentRemainder

private def entry14Bound (N : ℕ) : ℝ :=
  2 * (2 * N + 3 : ℕ) *
    ∑' m : ℕ, ((2 * Real.pi * (m + 1)) ^ (2 * N + 2))⁻¹

private def entry14Phi (N : ℕ) (x t : ℝ) : ℝ :=
  entry14Remainder N (x * Real.log t) / t

private def entry14PhiDeriv (N : ℕ) (x t : ℝ) : ℝ :=
  (x * deriv (entry14Remainder N) (x * Real.log t) -
    entry14Remainder N (x * Real.log t)) / t ^ 2

private lemma entry14Bound_nonneg (N : ℕ) : 0 ≤ entry14Bound N := by
  unfold entry14Bound
  exact mul_nonneg (by positivity) (tsum_nonneg fun m =>
    inv_nonneg.mpr (pow_nonneg (by positivity) _))

private lemma entry14Remainder_hasDerivAt (N : ℕ) (v : ℝ) :
    HasDerivAt (entry14Remainder N) (deriv (entry14Remainder N) v) v :=
  (MetaMathlibExt.differentiable_oneDivExpSubOneLaurentRemainder N).differentiableAt.hasDerivAt

private lemma entry14Remainder_deriv_abs_le_bound (N : ℕ) (v : ℝ) :
    |deriv (entry14Remainder N) v| ≤ entry14Bound N * |v| ^ (2 * N) := by
  simpa only [entry14Bound] using
    MetaMathlibExt.abs_deriv_oneDivExpSubOneLaurentRemainder_le N v

private lemma entry14Phi_hasDerivAt (N : ℕ) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (entry14Phi N x) (entry14PhiDeriv N x t) t := by
  have hlog : HasDerivAt (fun y : ℝ => x * Real.log y) (x / t) t := by
    simpa only [div_eq_mul_inv] using (Real.hasDerivAt_log ht.ne').const_mul x
  have hrem : HasDerivAt (fun y : ℝ => entry14Remainder N (x * Real.log y))
      (deriv (entry14Remainder N) (x * Real.log t) * (x / t)) t := by
    simpa only [Function.comp_def] using (entry14Remainder_hasDerivAt N _).comp t hlog
  have h := hrem.div (hasDerivAt_id t) ht.ne'
  change HasDerivAt (fun y : ℝ => entry14Remainder N (x * Real.log y) / y) _ t at h
  simp only [id_eq] at h
  unfold entry14Phi entry14PhiDeriv
  convert h using 1
  field_simp [ht.ne']

private lemma entry14Remainder_abs_le_bound (N : ℕ) (v : ℝ) :
    |entry14Remainder N v| ≤ entry14Bound N * |v| ^ (2 * N + 1) := by
  simpa only [entry14Bound] using
    MetaMathlibExt.oneDivExpSubOneLaurentRemainder_abs_le N v

private lemma entry14PhiDeriv_abs_le (N : ℕ) {x t : ℝ} (hx : 0 ≤ x) (ht : 1 ≤ t) :
    |entry14PhiDeriv N x t| ≤
      entry14Bound N * x ^ (2 * N + 1) *
        (Real.log t ^ (2 * N) + Real.log t ^ (2 * N + 1)) / t ^ 2 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hD := entry14Remainder_deriv_abs_le_bound N (x * Real.log t)
  have hR := entry14Remainder_abs_le_bound N (x * Real.log t)
  unfold entry14PhiDeriv
  rw [abs_div, abs_pow, abs_of_pos ht0]
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  calc
    |x * deriv (entry14Remainder N) (x * Real.log t) -
        entry14Remainder N (x * Real.log t)| ≤
        |x| * |deriv (entry14Remainder N) (x * Real.log t)| +
          |entry14Remainder N (x * Real.log t)| := by
      simpa only [abs_mul, sub_zero, zero_sub, abs_neg] using
        (abs_sub_le
          (x * deriv (entry14Remainder N) (x * Real.log t))
          0 (entry14Remainder N (x * Real.log t)))
    _ ≤ x * (entry14Bound N * |x * Real.log t| ^ (2 * N)) +
        entry14Bound N * |x * Real.log t| ^ (2 * N + 1) := by
      rw [abs_of_nonneg hx]
      exact add_le_add (mul_le_mul_of_nonneg_left hD hx) hR
    _ = entry14Bound N * x ^ (2 * N + 1) *
        (Real.log t ^ (2 * N) + Real.log t ^ (2 * N + 1)) := by
      rw [abs_mul, abs_of_nonneg hx, abs_of_nonneg hlog, mul_pow, mul_pow, pow_succ]
      ring

private lemma entry14_log_pow_div_sq_summable (q : ℕ) : Summable (fun j : ℕ =>
    Real.log ((j : ℝ) + 2) ^ q / ((j : ℝ) + 1) ^ 2) := by
  have hs0 : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hs : Summable (fun j : ℕ => 4 * ((j : ℝ) + 2) ^ (-(3 / 2 : ℝ))) := by
    have hshift := (summable_nat_add_iff
      (f := fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) 2).mpr hs0
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hshift.mul_left 4
  apply hs.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  have hsmall := isLittleO_log_rpow_rpow_atTop (q : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hbound : ∀ᶠ y : ℝ in atTop,
      ‖Real.log y ^ (q : ℝ)‖ ≤ ‖y ^ (1 / 2 : ℝ)‖ := by
    simpa using hsmall.bound (by norm_num : (0 : ℝ) < 1)
  have hy : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop b)] with j hj
    linarith
  filter_upwards [hy.eventually hbound] with j hj
  let y : ℝ := (j : ℝ) + 2
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hy1 : 1 ≤ y := by
    dsimp [y]
    have := (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
    linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hden : 0 < (j : ℝ) + 1 := by positivity
  have hrel : y ≤ 2 * ((j : ℝ) + 1) := by dsimp [y]; linarith
  change ‖Real.log y ^ q / ((j : ℝ) + 1) ^ 2‖ ≤ 4 * y ^ (-(3 / 2 : ℝ))
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (pow_nonneg hlog q),
    abs_of_pos (pow_pos hden 2)]
  change ‖Real.log y ^ (q : ℝ)‖ ≤ ‖y ^ (1 / 2 : ℝ)‖ at hj
  rw [Real.rpow_natCast] at hj
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog q),
    Real.norm_rpow_of_nonneg hy0.le, Real.norm_eq_abs, abs_of_pos hy0] at hj
  calc
    Real.log y ^ q / ((j : ℝ) + 1) ^ 2 ≤
        y ^ (1 / 2 : ℝ) / ((j : ℝ) + 1) ^ 2 :=
      div_le_div_of_nonneg_right hj (sq_nonneg _)
    _ ≤ 4 * y ^ (-(3 / 2 : ℝ)) := by
      rw [Real.rpow_neg hy0.le]
      have hdenpow : 0 < y ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hy0 _
      have hy2 : y ^ 2 ≤ 4 * ((j : ℝ) + 1) ^ 2 := by nlinarith
      rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ (sq_pos_of_pos hden) hdenpow).2
      calc
        y ^ (1 / 2 : ℝ) * y ^ (3 / 2 : ℝ) = y ^ 2 := by
          rw [← Real.rpow_add hy0]
          norm_num
        _ ≤ 4 * ((j : ℝ) + 1) ^ 2 := hy2

private def entry14Majorant (N j : ℕ) : ℝ :=
  Real.log ((j : ℝ) + 2) ^ (2 * N) / ((j : ℝ) + 1) ^ 2 +
    Real.log ((j : ℝ) + 2) ^ (2 * N + 1) / ((j : ℝ) + 1) ^ 2

private def entry14Delta (N : ℕ) (x : ℝ) (j : ℕ) : ℝ :=
  entry14Phi N x ((j : ℝ) + 2) -
    ∫ t in ((j : ℝ) + 1)..((j : ℝ) + 2), entry14Phi N x t

private lemma entry14Majorant_nonneg (N j : ℕ) : 0 ≤ entry14Majorant N j := by
  have hlog : 0 ≤ Real.log ((j : ℝ) + 2) := by
    apply Real.log_nonneg
    have := (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
    linarith
  unfold entry14Majorant
  positivity

private lemma entry14Majorant_summable (N : ℕ) : Summable (entry14Majorant N) := by
  exact (entry14_log_pow_div_sq_summable (2 * N)).add
    (entry14_log_pow_div_sq_summable (2 * N + 1))

private lemma entry14PhiDeriv_le_majorant (N : ℕ) {x : ℝ} (hx : 0 ≤ x) (j : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc ((j : ℝ) + 1) ((j : ℝ) + 2)) :
    |entry14PhiDeriv N x t| ≤
      entry14Bound N * x ^ (2 * N + 1) * entry14Majorant N j := by
  have ht1 : 1 ≤ t := by
    have hj0 := (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
    linarith [ht.1]
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hj0 := (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
  have hb1 : 1 ≤ (j : ℝ) + 2 := by linarith
  have hb0 : 0 ≤ Real.log ((j : ℝ) + 2) := Real.log_nonneg hb1
  have hlogle : Real.log t ≤ Real.log ((j : ℝ) + 2) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one ht1) ht.2
  have hden : ((j : ℝ) + 1) ^ 2 ≤ t ^ 2 := by nlinarith [ht.1]
  calc
    |entry14PhiDeriv N x t| ≤
        entry14Bound N * x ^ (2 * N + 1) *
          (Real.log t ^ (2 * N) + Real.log t ^ (2 * N + 1)) / t ^ 2 :=
      entry14PhiDeriv_abs_le N hx ht1
    _ ≤ entry14Bound N * x ^ (2 * N + 1) *
        (Real.log ((j : ℝ) + 2) ^ (2 * N) +
          Real.log ((j : ℝ) + 2) ^ (2 * N + 1)) / ((j : ℝ) + 1) ^ 2 := by
      have hA : 0 ≤ entry14Bound N * x ^ (2 * N + 1) :=
        mul_nonneg (entry14Bound_nonneg N) (pow_nonneg hx _)
      have hnum : Real.log t ^ (2 * N) + Real.log t ^ (2 * N + 1) ≤
          Real.log ((j : ℝ) + 2) ^ (2 * N) +
            Real.log ((j : ℝ) + 2) ^ (2 * N + 1) :=
        add_le_add (pow_le_pow_left₀ hlog0 hlogle _) (pow_le_pow_left₀ hlog0 hlogle _)
      calc
        entry14Bound N * x ^ (2 * N + 1) *
              (Real.log t ^ (2 * N) + Real.log t ^ (2 * N + 1)) / t ^ 2 ≤
            entry14Bound N * x ^ (2 * N + 1) *
              (Real.log ((j : ℝ) + 2) ^ (2 * N) +
                Real.log ((j : ℝ) + 2) ^ (2 * N + 1)) / t ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hA) (sq_nonneg t)
        _ ≤ entry14Bound N * x ^ (2 * N + 1) *
              (Real.log ((j : ℝ) + 2) ^ (2 * N) +
                Real.log ((j : ℝ) + 2) ^ (2 * N + 1)) /
              ((j : ℝ) + 1) ^ 2 :=
          div_le_div_of_nonneg_left
            (mul_nonneg hA (add_nonneg (pow_nonneg hb0 _) (pow_nonneg hb0 _)))
            (sq_pos_of_pos (by positivity)) hden
    _ = entry14Bound N * x ^ (2 * N + 1) * entry14Majorant N j := by
      unfold entry14Majorant
      ring

private lemma entry14Delta_abs_le (N : ℕ) {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    |entry14Delta N x j| ≤
      entry14Bound N * x ^ (2 * N + 1) * entry14Majorant N j := by
  let a : ℝ := (j : ℝ) + 1
  let b : ℝ := (j : ℝ) + 2
  let K : ℝ := entry14Bound N * x ^ (2 * N + 1) * entry14Majorant N j
  have hab : a ≤ b := by unfold a b; linarith
  have ha : 0 < a := by unfold a; positivity
  have hK : 0 ≤ K := by
    unfold K
    exact mul_nonneg (mul_nonneg (entry14Bound_nonneg N) (pow_nonneg hx _))
      (entry14Majorant_nonneg N j)
  have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (entry14Phi N x) t := by
    intro t ht
    exact (entry14Phi_hasDerivAt N x t (lt_of_lt_of_le ha ht.1)).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc a b, ‖deriv (entry14Phi N x) t‖ ≤ K := by
    intro t ht
    rw [(entry14Phi_hasDerivAt N x t (lt_of_lt_of_le ha ht.1)).deriv, Real.norm_eq_abs]
    change |entry14PhiDeriv N x t| ≤
      entry14Bound N * x ^ (2 * N + 1) * entry14Majorant N j
    apply entry14PhiDeriv_le_majorant N hx j
    simpa [a, b] using ht
  have hlip : ∀ t ∈ Set.Icc a b,
      ‖entry14Phi N x b - entry14Phi N x t‖ ≤ K := by
    intro t ht
    calc
      ‖entry14Phi N x b - entry14Phi N x t‖ ≤ K * ‖b - t‖ :=
        Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv (convex_Icc a b)
          ht ⟨hab, le_rfl⟩
      _ ≤ K := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
        have hbt : b - t ≤ 1 := by unfold a b at *; linarith [ht.1]
        nlinarith
  have hcont : ContinuousOn (entry14Phi N x) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact (hdiff t ht).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (entry14Phi N x) volume a b := hcont.intervalIntegrable
  unfold entry14Delta
  change |entry14Phi N x b - ∫ t in a..b, entry14Phi N x t| ≤ K
  calc
    |entry14Phi N x b - ∫ t in a..b, entry14Phi N x t| =
        ‖∫ t in a..b, entry14Phi N x b - entry14Phi N x t‖ := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
        intervalIntegral.integral_const, Real.norm_eq_abs]
      simp only [smul_eq_mul]
      congr 1
      unfold a b
      ring
    _ ≤ K * |b - a| := intervalIntegral.norm_integral_le_of_norm_le_const (by
      intro t ht
      have ht' := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le hab] at ht'
      exact hlip t ht')
    _ = K := by
      have : b - a = 1 := by unfold a b; ring
      rw [this, abs_one, mul_one]

private lemma entry14Delta_summable (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (entry14Delta N x) := by
  have hm := (entry14Majorant_summable N).mul_left
    (entry14Bound N * x ^ (2 * N + 1))
  exact hm.of_norm_bounded fun j => by
    rw [Real.norm_eq_abs]
    exact entry14Delta_abs_le N hx j

private lemma entry14Delta_tsum_abs_le (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |∑' j : ℕ, entry14Delta N x j| ≤
      entry14Bound N * (∑' j : ℕ, entry14Majorant N j) * x ^ (2 * N + 1) := by
  have hd := entry14Delta_summable N hx
  have hm := entry14Majorant_summable N
  rw [← Real.norm_eq_abs]
  calc
    ‖∑' j : ℕ, entry14Delta N x j‖ ≤
        ∑' j : ℕ, ‖entry14Delta N x j‖ := norm_tsum_le_tsum_norm hd.norm
    _ ≤ ∑' j : ℕ,
        entry14Bound N * x ^ (2 * N + 1) * entry14Majorant N j :=
      hd.norm.tsum_le_tsum (fun j => by
        rw [Real.norm_eq_abs]
        exact entry14Delta_abs_le N hx j)
        (hm.mul_left (entry14Bound N * x ^ (2 * N + 1)))
    _ = entry14Bound N * (∑' j : ℕ, entry14Majorant N j) * x ^ (2 * N + 1) := by
      rw [tsum_mul_left]
      ring

private lemma entry14Kernel_eq (N : ℕ) (v : ℝ) (hv : v ≠ 0) :
    1 / (Real.exp v - 1) - 1 / v + 1 / 2 -
        ∑ n ∈ range N,
          (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
            v ^ (2 * n + 1) =
      entry14Remainder N v := by
  simp only [entry14Remainder, MetaMathlibExt.oneDivExpSubOneLaurentRemainder,
    hv, ↓reduceIte]

private def entry14KernelPrimitive (v : ℝ) : ℝ :=
  Real.log (1 - Real.exp (-v)) - Real.log v

private def entry14PrimitiveTerm (n : ℕ) (v : ℝ) : ℝ :=
  (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) /
    (2 * n + 2 : ℕ) * v ^ (2 * n + 2)

private def entry14PolyPrimitive (N : ℕ) (v : ℝ) : ℝ :=
  v / 2 - ∑ n ∈ range N, entry14PrimitiveTerm n v

private def entry14Primitive (N : ℕ) (v : ℝ) : ℝ :=
  entry14KernelPrimitive v + entry14PolyPrimitive N v

private lemma entry14KernelPrimitive_tendsto_zero_right :
    Tendsto entry14KernelPrimitive (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hslope := (Real.hasDerivAt_exp 0).tendsto_slope_zero_right
  have hbasic : Tendsto (fun v : ℝ => (Real.exp v - 1) / v)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa [smul_eq_mul, div_eq_inv_mul] using hslope
  have hexp : Tendsto Real.exp (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h : Tendsto Real.exp (nhds (0 : ℝ)) (nhds (Real.exp 0)) :=
      Real.continuous_exp.continuousAt.tendsto
    change Tendsto Real.exp (nhds 0 ⊓ Filter.principal (Set.Ioi 0)) (nhds 1)
    simpa using h.mono_left inf_le_left
  have hratio : Tendsto (fun v : ℝ => (1 - Real.exp (-v)) / v)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hquot := hbasic.div hexp one_ne_zero
    have hquot' : Tendsto ((fun v : ℝ => (Real.exp v - 1) / v) / Real.exp)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by simpa using hquot
    apply hquot'.congr'
    filter_upwards [self_mem_nhdsWithin] with v hv
    change 0 < v at hv
    symm
    change (1 - Real.exp (-v)) / v = ((Real.exp v - 1) / v) / Real.exp v
    rw [Real.exp_neg]
    field_simp [hv.ne', Real.exp_ne_zero]
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
  have hlog' : Tendsto (Real.log ∘ fun v : ℝ => (1 - Real.exp (-v)) / v)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by simpa using hlog
  apply hlog'.congr'
  filter_upwards [self_mem_nhdsWithin] with v hv
  change 0 < v at hv
  change Real.log ((1 - Real.exp (-v)) / v) = entry14KernelPrimitive v
  rw [entry14KernelPrimitive, Real.log_div]
  · have he : Real.exp (-v) < 1 := by
      rw [Real.exp_neg, inv_lt_one₀ (Real.exp_pos v)]
      exact Real.one_lt_exp_iff.mpr hv
    exact (sub_pos.mpr he).ne'
  · exact hv.ne'

private lemma entry14PrimitiveTerm_hasDerivAt (n : ℕ) (v : ℝ) :
    HasDerivAt (entry14PrimitiveTerm n)
      ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
        v ^ (2 * n + 1)) v := by
  unfold entry14PrimitiveTerm
  convert (hasDerivAt_pow (2 * n + 2) v).const_mul
    ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) /
      (2 * n + 2 : ℕ)) using 1
  rw [show 2 * n + 2 - 1 = 2 * n + 1 by omega]
  have hne : ((2 * n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

private lemma entry14PolyPrimitive_tendsto_zero_right (N : ℕ) :
    Tendsto (entry14PolyPrimitive N) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hcont : ContinuousAt (entry14PolyPrimitive N) 0 := by
    unfold entry14PolyPrimitive entry14PrimitiveTerm
    fun_prop
  have hzero : entry14PolyPrimitive N 0 = 0 := by
    simp [entry14PolyPrimitive, entry14PrimitiveTerm]
  change Tendsto (entry14PolyPrimitive N)
    (nhds 0 ⊓ Filter.principal (Set.Ioi 0)) (nhds 0)
  have ht := hcont.tendsto.mono_left
    (show nhds 0 ⊓ Filter.principal (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  simpa only [hzero] using ht

private lemma entry14Primitive_tendsto_zero_right (N : ℕ) :
    Tendsto (entry14Primitive N) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  change Tendsto (fun v => entry14KernelPrimitive v + entry14PolyPrimitive N v)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  simpa only [zero_add] using
    entry14KernelPrimitive_tendsto_zero_right.add
      (entry14PolyPrimitive_tendsto_zero_right N)

private lemma entry14KernelPrimitive_hasDerivAt {v : ℝ} (hv : 0 < v) :
    HasDerivAt entry14KernelPrimitive
      (1 / (Real.exp v - 1) - 1 / v) v := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-v)) v := by
    convert (hasDerivAt_id v).neg.exp using 1 <;> simp
  have hinner : HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) (Real.exp (-v)) v := by
    convert (hasDerivAt_const v (1 : ℝ)).sub hexp using 1
    ring
  have hinnerPos : 0 < 1 - Real.exp (-v) := by
    rw [sub_pos, Real.exp_neg, inv_lt_one₀ (Real.exp_pos v)]
    exact Real.one_lt_exp_iff.mpr hv
  have hlogInner := (Real.hasDerivAt_log hinnerPos.ne').comp v hinner
  have hlogV := Real.hasDerivAt_log hv.ne'
  have hderiv := hlogInner.sub hlogV
  change HasDerivAt entry14KernelPrimitive _ v
  apply hderiv.congr_deriv
  rw [Real.exp_neg]
  have he : Real.exp v ≠ 0 := Real.exp_ne_zero v
  have he1 : Real.exp v - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact (Real.exp_eq_one_iff v).not.mpr hv.ne'
  field_simp [he, he1, hv.ne']

private lemma entry14Primitive_hasDerivAt (N : ℕ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (entry14Primitive N) (entry14Remainder N v) v := by
  have hsum : HasDerivAt (fun y : ℝ => ∑ n ∈ range N, entry14PrimitiveTerm n y)
      (∑ n ∈ range N,
        (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          v ^ (2 * n + 1)) v :=
    HasDerivAt.fun_sum fun n _ => entry14PrimitiveTerm_hasDerivAt n v
  have hpoly : HasDerivAt (entry14PolyPrimitive N)
      (1 / 2 - ∑ n ∈ range N,
        (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          v ^ (2 * n + 1)) v := by
    unfold entry14PolyPrimitive
    convert ((hasDerivAt_id v).div_const 2).sub hsum using 1
    · ext y
      rfl
  have h := (entry14KernelPrimitive_hasDerivAt hv).add hpoly
  unfold entry14Primitive
  apply h.congr_deriv
  rw [← entry14Kernel_eq N v hv.ne']
  ring

private def entry14ScaledPrimitive (N : ℕ) (x t : ℝ) : ℝ :=
  entry14Primitive N (x * Real.log t) / x

private lemma entry14ScaledPrimitive_hasDerivAt (N : ℕ) {x t : ℝ}
    (hx : 0 < x) (ht : 1 < t) :
    HasDerivAt (entry14ScaledPrimitive N x) (entry14Phi N x t) t := by
  have hlog : HasDerivAt (fun y : ℝ => x * Real.log y) (x / t) t := by
    simpa only [div_eq_mul_inv] using (Real.hasDerivAt_log (by linarith)).const_mul x
  have harg : 0 < x * Real.log t := mul_pos hx (Real.log_pos ht)
  have hcomp := (entry14Primitive_hasDerivAt N harg).comp t hlog
  have hdiv := hcomp.div_const x
  unfold entry14ScaledPrimitive entry14Phi
  convert hdiv using 1
  · rfl
  · field_simp [hx.ne', (by linarith : t ≠ 0)]

private lemma entry14ScaledPrimitive_tendsto_one_right (N : ℕ) {x : ℝ} (hx : 0 < x) :
    Tendsto (entry14ScaledPrimitive N x) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog : Tendsto (fun t : ℝ => x * Real.log t)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have h : Tendsto (fun t : ℝ => x * Real.log t)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (x * Real.log 1)) :=
      tendsto_const_nhds.mul
        ((Real.continuousAt_log one_ne_zero).tendsto.mono_left inf_le_left)
    simpa using h
  have harg : Tendsto (fun t : ℝ => x * Real.log t)
      (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hlog, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos hx (Real.log_pos ht)
  have hprim := (entry14Primitive_tendsto_zero_right N).comp harg
  unfold entry14ScaledPrimitive
  simpa using hprim.div_const x

private lemma entry14Phi_integral (N : ℕ) {x T : ℝ} (hx : 0 < x) (hT : 1 < T) :
    ∫ t in (1 : ℝ)..T, entry14Phi N x t =
      entry14Primitive N (x * Real.log T) / x := by
  have hderiv : ∀ t ∈ Set.Ioo (1 : ℝ) T,
      HasDerivAt (entry14ScaledPrimitive N x) (entry14Phi N x t) t :=
    fun t ht => entry14ScaledPrimitive_hasDerivAt N hx ht.1
  have hcont : ContinuousOn (entry14Phi N x) (Set.uIcc (1 : ℝ) T) := by
    rw [Set.uIcc_of_le hT.le]
    intro t ht
    exact (entry14Phi_hasDerivAt N x t (lt_of_lt_of_le zero_lt_one ht.1)).continuousAt
      |>.continuousWithinAt
  have hint : IntervalIntegrable (entry14Phi N x) volume 1 T := hcont.intervalIntegrable
  have hright : Tendsto (entry14ScaledPrimitive N x) (nhdsWithin T (Set.Iio T))
      (nhds (entry14ScaledPrimitive N x T)) :=
    (entry14ScaledPrimitive_hasDerivAt N hx hT).continuousAt.tendsto.mono_left inf_le_left
  simpa [entry14ScaledPrimitive] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hT hderiv hint
      (entry14ScaledPrimitive_tendsto_one_right N hx) hright

def chapter7Entry14A0Approx (m : ℕ) : ℝ :=
  (∑ k ∈ Icc 2 m, 1 / ((k : ℝ) * Real.log k)) -
    Real.log (Real.log m)

def chapter7StieltjesA (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * c k / (k.factorial : ℝ)

/-- **Two definitions of the normalized Stieltjes coefficients agree.** For every real sequence
$(c_k)_{k \ge 0}$, the coefficients $A_k = (-1)^k c_k / k!$ defined for the asymptotic expansion of
$\sum 1/(n(n^x - 1))$ are, by definition, the coefficients $A_k$ used in the expansion of
$\sum 1/(n^{s+1} \log n)$ in the Stieltjes constants. -/
theorem chapter7StieltjesA_eq_entry14Bernoulliasymptotic :
    chapter7StieltjesA = Entry14Bernoulliasymptotic.chapter7StieltjesA := rfl

def chapter7Entry14Coeff (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  -((bernoulli (2 * k) : ℚ) : ℝ) * chapter7StieltjesA c (2 * k - 1) /
    (2 * k)

def chapter7Entry14Approx (a0 : ℝ) (c : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (a0 - Real.log x) / x +
    (1 - Real.eulerMascheroniConstant) / 2 +
    ∑ j ∈ range N, chapter7Entry14Coeff c (j + 1) * x ^ (2 * j + 1)

def chapter7Entry14Term (x : ℝ) (j : ℕ) : ℝ :=
  let k : ℝ := j + 2
  1 / (k * (Real.rpow k x - 1))

def chapter7Entry14Sum (x : ℝ) : ℝ :=
  ∑' j : ℕ, chapter7Entry14Term x j

/-- **Convergence of $\sum 1/(n(n^x - 1))$.** For every real $x > 0$ the series
$\sum_{n \ge 2} \frac{1}{n(n^x - 1)}$ converges absolutely. -/
theorem summable_chapter7Entry14Term (x : ℝ) (hx : 0 < x) :
    Summable (chapter7Entry14Term x) := by
  have hp : 1 < x + 1 := by linarith
  have hs0 : Summable (fun n : ℕ => ((n : ℝ) ^ (x + 1))⁻¹) :=
    (Real.summable_nat_rpow_inv (p := x + 1)).mpr hp
  have hs1 : Summable (fun j : ℕ => ((((j + 2 : ℕ) : ℝ) ^ (x + 1))⁻¹)) :=
    (summable_nat_add_iff 2).mpr hs0
  have hs : Summable (fun j : ℕ => 2 * (((j : ℝ) + 2) ^ (x + 1))⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hs1.mul_left 2
  apply hs.of_norm_bounded_eventually
  have hpow : Tendsto (fun j : ℕ => (j : ℝ) ^ x) atTop atTop :=
    (tendsto_rpow_atTop hx).comp tendsto_natCast_atTop_atTop
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hpow.eventually (eventually_ge_atTop 2)] with j hj
  let y : ℝ := (j : ℝ) + 2
  have hy : 0 < y := by
    dsimp [y]
    positivity
  have hjle : (j : ℝ) ^ x ≤ y ^ x := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg j)
    · dsimp [y]
      linarith
    · exact hx.le
  have hy2 : 2 ≤ y ^ x := hj.trans hjle
  have hhalf : y ^ x / 2 ≤ y ^ x - 1 := by linarith
  have hden : 0 < y * (y ^ x / 2) := by positivity
  have hcmp : 1 / (y * (y ^ x - 1)) ≤ 1 / (y * (y ^ x / 2)) :=
    one_div_le_one_div_of_le hden (mul_le_mul_of_nonneg_left hhalf hy.le)
  rw [chapter7Entry14Term]
  change ‖1 / (y * (y ^ x - 1))‖ ≤ 2 * (y ^ (x + 1))⁻¹
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (mul_pos hy (by linarith)))]
  calc
    1 / (y * (y ^ x - 1)) ≤ 1 / (y * (y ^ x / 2)) := hcmp
    _ = 2 * (y ^ (x + 1))⁻¹ := by
      rw [Real.rpow_add hy]
      simp only [Real.rpow_one]
      field_simp

def chapter7StieltjesApprox (k m : ℕ) : ℝ :=
  (∑ j ∈ Icc 1 m, Real.log (j : ℝ) ^ k / j) -
    Real.log (m : ℝ) ^ (k + 1) / (k + 1)

/-- **Two definitions of the Stieltjes approximants agree.** For all $k, m \ge 0$, the approximant
$\sum_{j=1}^{m} (\log j)^k / j - (\log m)^{k+1} / (k+1)$ defined for the asymptotic expansion of
$\sum 1/(n(n^x - 1))$ is, by definition, the approximant used for the existence of the Stieltjes
constants. -/
theorem chapter7StieltjesApprox_eq_entry13Bernoullipolyadd :
    chapter7StieltjesApprox = Entry13Bernoullipolyadd.chapter7StieltjesApprox := rfl

private lemma entry14Delta_sum (N m : ℕ) (x : ℝ) :
    ∑ j ∈ range m, entry14Delta N x j =
      (∑ j ∈ range m, entry14Phi N x ((j : ℝ) + 2)) -
        ∫ t in (1 : ℝ)..((m : ℝ) + 1), entry14Phi N x t := by
  have hint : ∀ k < m, IntervalIntegrable (entry14Phi N x) volume
      ((k : ℝ) + 1) (((k + 1 : ℕ) : ℝ) + 1) := by
    intro k _
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by push_cast; linarith : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 1)]
    intro t ht
    have ht0 : 0 < t := by
      have hk0 := (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))
      linarith [ht.1]
    exact (entry14Phi_hasDerivAt N x t ht0).continuousAt.continuousWithinAt
  have hInt := intervalIntegral.sum_integral_adjacent_intervals
    (f := entry14Phi N x) (a := fun k : ℕ => (k : ℝ) + 1) hint
  have hInt' : (∑ k ∈ range m,
      ∫ t in ((k : ℝ) + 1)..((k : ℝ) + 2), entry14Phi N x t) =
      ∫ t in (1 : ℝ)..((m : ℝ) + 1), entry14Phi N x t := by
    convert hInt using 1
    · apply sum_congr rfl
      intro k _
      congr 1
      push_cast
      ring
    · norm_num
  unfold entry14Delta
  rw [sum_sub_distrib, hInt']

private lemma entry14Term_expansion (N j : ℕ) {x : ℝ} (hx : 0 < x) :
    chapter7Entry14Term x j =
      (1 / x) * (1 / (((j : ℝ) + 2) * Real.log ((j : ℝ) + 2))) -
        (1 / 2) * (1 / ((j : ℝ) + 2)) +
        ∑ n ∈ range N,
          ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
              x ^ (2 * n + 1)) *
            (Real.log ((j : ℝ) + 2) ^ (2 * n + 1) / ((j : ℝ) + 2)) +
        entry14Phi N x ((j : ℝ) + 2) := by
  let k : ℝ := (j : ℝ) + 2
  have hk : 0 < k := by unfold k; positivity
  have hk1 : 1 < k := by
    unfold k
    have := (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
    linarith
  have hlog : 0 < Real.log k := Real.log_pos hk1
  have hv : 0 < x * Real.log k := mul_pos hx hlog
  have hexp : Real.exp (x * Real.log k) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact (Real.exp_eq_one_iff _).not.mpr hv.ne'
  have hkernel := entry14Kernel_eq N (x * Real.log k) hv.ne'
  have hsolve : 1 / (Real.exp (x * Real.log k) - 1) =
      1 / (x * Real.log k) - 1 / 2 +
        ∑ n ∈ range N,
          (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
            (x * Real.log k) ^ (2 * n + 1) +
        entry14Remainder N (x * Real.log k) := by
    linarith [hkernel]
  have hpoly : (∑ n ∈ range N,
      (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
        (x * Real.log k) ^ (2 * n + 1)) / k =
      ∑ n ∈ range N,
        ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
            x ^ (2 * n + 1)) * (Real.log k ^ (2 * n + 1) / k) := by
    rw [sum_div]
    apply sum_congr rfl
    intro n _
    rw [mul_pow]
    ring
  rw [chapter7Entry14Term]
  change 1 / (k * (Real.rpow k x - 1)) =
    (1 / x) * (1 / (k * Real.log k)) - (1 / 2) * (1 / k) +
      ∑ n ∈ range N,
        ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
            x ^ (2 * n + 1)) * (Real.log k ^ (2 * n + 1) / k) +
        entry14Phi N x k
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hk x]
  rw [mul_comm (Real.log k) x]
  change 1 / (k * (Real.exp (x * Real.log k) - 1)) = _
  change _ = (1 / x) * (1 / (k * Real.log k)) - (1 / 2) * (1 / k) +
    ∑ n ∈ range N,
      ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          x ^ (2 * n + 1)) * (Real.log k ^ (2 * n + 1) / k) +
      entry14Remainder N (x * Real.log k) / k
  calc
    1 / (k * (Real.exp (x * Real.log k) - 1)) =
        (1 / (Real.exp (x * Real.log k) - 1)) / k := by
      field_simp [hk.ne', hexp]
    _ = (1 / (x * Real.log k) - 1 / 2 +
          ∑ n ∈ range N,
            (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
              (x * Real.log k) ^ (2 * n + 1) +
          entry14Remainder N (x * Real.log k)) / k := by rw [hsolve]
    _ = _ := by
      rw [add_div, add_div, sub_div, hpoly]
      simp only [one_div, mul_inv]
      ring

private lemma entry14_sum_range_shift_two (f : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ range m, f (j + 2) = ∑ k ∈ Icc 2 (m + 1), f k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1 + 1), ih]

private lemma entry14_sum_range_shift_one (f : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ range m, f (j + 1) = ∑ k ∈ Icc 1 m, f k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]

private lemma entry14_harmonic_Icc (m : ℕ) :
    (((harmonic m : ℚ)) : ℝ) = ∑ k ∈ Icc 1 m, (k : ℝ)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [harmonic_succ]
      push_cast
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ← ih]
      simp only [Nat.cast_add, Nat.cast_one]

private def entry14FiniteMain (N : ℕ) (x : ℝ) (m : ℕ) : ℝ :=
  (chapter7Entry14A0Approx (m + 1) - Real.log x) / x +
    (1 - ((((harmonic (m + 1) : ℚ)) : ℝ) - Real.log ((m : ℝ) + 1))) / 2 +
    ∑ n ∈ range N,
      ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
        x ^ (2 * n + 1)) * chapter7StieltjesApprox (2 * n + 1) (m + 1)

private def entry14Boundary (x : ℝ) (m : ℕ) : ℝ :=
  Real.log (1 - Real.exp (-x * Real.log ((m : ℝ) + 1))) / x

private lemma entry14Primitive_expansion (N m : ℕ) {x : ℝ} (hx : 0 < x)
    (hm : 1 ≤ m) :
    entry14Primitive N (x * Real.log ((m : ℝ) + 1)) / x =
      entry14Boundary x m - Real.log x / x - Real.log (Real.log ((m : ℝ) + 1)) / x +
        Real.log ((m : ℝ) + 1) / 2 -
        ∑ n ∈ range N,
          (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
            x ^ (2 * n + 1) * Real.log ((m : ℝ) + 1) ^ (2 * n + 2) /
              (2 * n + 2 : ℕ) := by
  let T : ℝ := (m : ℝ) + 1
  have hT : 1 < T := by
    unfold T
    exact_mod_cast Nat.lt_add_one_iff.mpr (Nat.zero_lt_of_lt hm)
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hterms : (∑ n ∈ range N, entry14PrimitiveTerm n (x * Real.log T)) / x =
      ∑ n ∈ range N,
        (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          x ^ (2 * n + 1) * Real.log T ^ (2 * n + 2) / (2 * n + 2 : ℕ) := by
    rw [sum_div]
    apply sum_congr rfl
    intro n _
    unfold entry14PrimitiveTerm
    rw [mul_pow]
    field_simp [hx.ne']
    ring
  change entry14Primitive N (x * Real.log T) / x = _
  change _ = entry14Boundary x m - Real.log x / x - Real.log (Real.log T) / x +
    Real.log T / 2 - _
  unfold entry14Primitive entry14KernelPrimitive entry14PolyPrimitive entry14Boundary
  change (Real.log (1 - Real.exp (-(x * Real.log T))) - Real.log (x * Real.log T) +
      (x * Real.log T / 2 - ∑ n ∈ range N, entry14PrimitiveTerm n (x * Real.log T))) / x = _
  rw [Real.log_mul hx.ne' hlogT.ne', add_div, sub_div, sub_div, hterms]
  field_simp [hx.ne']
  ring

private lemma entry14Finite_identity (N m : ℕ) {x : ℝ} (hx : 0 < x) (hm : 1 ≤ m) :
    ∑ j ∈ range m, chapter7Entry14Term x j =
      entry14FiniteMain N x m + entry14Boundary x m +
        ∑ j ∈ range m, entry14Delta N x j := by
  let T : ℝ := (m : ℝ) + 1
  have hT : 1 < T := by
    unfold T
    exact_mod_cast Nat.lt_add_one_iff.mpr (Nat.zero_lt_of_lt hm)
  have hA : (∑ j ∈ range m,
      1 / (((j : ℝ) + 2) * Real.log ((j : ℝ) + 2))) =
      chapter7Entry14A0Approx (m + 1) + Real.log (Real.log T) := by
    have hs := entry14_sum_range_shift_two
      (fun k : ℕ => 1 / ((k : ℝ) * Real.log k)) m
    have hs' : (∑ j ∈ range m,
        1 / (((j : ℝ) + 2) * Real.log ((j : ℝ) + 2))) =
        ∑ k ∈ Icc 2 (m + 1), 1 / ((k : ℝ) * Real.log k) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using hs
    unfold chapter7Entry14A0Approx
    rw [hs']
    unfold T
    push_cast
    ring
  have hH : (∑ j ∈ range m, 1 / ((j : ℝ) + 2)) =
      (((harmonic (m + 1) : ℚ)) : ℝ) - 1 := by
    let f : ℕ → ℝ := fun k => (k : ℝ)⁻¹
    have hfront := Finset.sum_range_succ' (fun j : ℕ => f (j + 1)) m
    have hshift := entry14_sum_range_shift_one f (m + 1)
    have hhar := entry14_harmonic_Icc (m + 1)
    have htail : (∑ j ∈ range m, 1 / ((j : ℝ) + 2)) =
        ∑ j ∈ range m, f (j + 1 + 1) := by
      apply sum_congr rfl
      intro j _
      simp only [f, one_div, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    have heq : (∑ j ∈ range m, 1 / ((j : ℝ) + 2)) + 1 =
        (((harmonic (m + 1) : ℚ)) : ℝ) := by
      calc
        (∑ j ∈ range m, 1 / ((j : ℝ) + 2)) + 1 =
            ∑ j ∈ range (m + 1), f (j + 1) := by rw [hfront, htail]; simp [f]
        _ = ∑ k ∈ Icc 1 (m + 1), f k := hshift
        _ = (((harmonic (m + 1) : ℚ)) : ℝ) := hhar.symm
    linarith
  have hS : ∀ n < N,
      (∑ j ∈ range m,
        Real.log ((j : ℝ) + 2) ^ (2 * n + 1) / ((j : ℝ) + 2)) =
        chapter7StieltjesApprox (2 * n + 1) (m + 1) +
          Real.log T ^ (2 * n + 2) / (2 * n + 2 : ℕ) := by
    intro n _
    let f : ℕ → ℝ := fun k => Real.log (k : ℝ) ^ (2 * n + 1) / k
    have hfront := Finset.sum_range_succ' (fun j : ℕ => f (j + 1)) m
    have hshift := entry14_sum_range_shift_one f (m + 1)
    have htail : (∑ j ∈ range m,
        Real.log ((j : ℝ) + 2) ^ (2 * n + 1) / ((j : ℝ) + 2)) =
        ∑ j ∈ range m, f (j + 1 + 1) := by
      apply sum_congr rfl
      intro j _
      simp only [f, Nat.cast_add, Nat.cast_one]
      ring_nf
    have heq : (∑ j ∈ range m,
        Real.log ((j : ℝ) + 2) ^ (2 * n + 1) / ((j : ℝ) + 2)) =
        ∑ k ∈ Icc 1 (m + 1), f k := by
      calc
        (∑ j ∈ range m,
            Real.log ((j : ℝ) + 2) ^ (2 * n + 1) / ((j : ℝ) + 2)) =
            ∑ j ∈ range (m + 1), f (j + 1) := by rw [hfront, htail]; simp [f]
        _ = ∑ k ∈ Icc 1 (m + 1), f k := hshift
    rw [heq]
    unfold chapter7StieltjesApprox f
    unfold T
    push_cast
    ring
  have hPhi : (∑ j ∈ range m, entry14Phi N x ((j : ℝ) + 2)) =
      (∑ j ∈ range m, entry14Delta N x j) +
        entry14Primitive N (x * Real.log T) / x := by
    have hd := entry14Delta_sum N m x
    have hi := entry14Phi_integral N hx hT
    change _ = _ - ∫ t in (1 : ℝ)..T, entry14Phi N x t at hd
    rw [hi] at hd
    linarith
  have hpolySum : (∑ j ∈ range m, ∑ n ∈ range N,
      ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          x ^ (2 * n + 1)) *
        (Real.log ((j : ℝ) + 2) ^ (2 * n + 1) / ((j : ℝ) + 2))) =
      ∑ n ∈ range N,
        ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          x ^ (2 * n + 1)) *
          ∑ j ∈ range m,
            Real.log ((j : ℝ) + 2) ^ (2 * n + 1) / ((j : ℝ) + 2) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    rw [mul_sum]
  have hsum : (∑ j ∈ range m, chapter7Entry14Term x j) =
      (1 / x) * (∑ j ∈ range m,
        1 / (((j : ℝ) + 2) * Real.log ((j : ℝ) + 2))) -
      (1 / 2) * (∑ j ∈ range m, 1 / ((j : ℝ) + 2)) +
      ∑ n ∈ range N,
        ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          x ^ (2 * n + 1)) *
          ∑ j ∈ range m,
            Real.log ((j : ℝ) + 2) ^ (2 * n + 1) / ((j : ℝ) + 2) +
      ∑ j ∈ range m, entry14Phi N x ((j : ℝ) + 2) := by
    simp_rw [entry14Term_expansion N _ hx]
    rw [sum_add_distrib, sum_add_distrib, sum_sub_distrib, hpolySum]
    rw [← mul_sum, ← mul_sum]
  have hStSum : (∑ n ∈ range N,
      ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
        x ^ (2 * n + 1)) *
        ∑ j ∈ range m,
          Real.log ((j : ℝ) + 2) ^ (2 * n + 1) / ((j : ℝ) + 2)) =
      ∑ n ∈ range N,
        ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          x ^ (2 * n + 1)) *
          (chapter7StieltjesApprox (2 * n + 1) (m + 1) +
            Real.log T ^ (2 * n + 2) / (2 * n + 2 : ℕ)) := by
    apply sum_congr rfl
    intro n hn
    rw [hS n (mem_range.mp hn)]
  have hcancel : (∑ n ∈ range N,
      ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
        x ^ (2 * n + 1)) *
        (Real.log T ^ (2 * n + 2) / (2 * n + 2 : ℕ))) =
      ∑ n ∈ range N,
        (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          x ^ (2 * n + 1) * Real.log ((m : ℝ) + 1) ^ (2 * n + 2) /
            (2 * n + 2 : ℕ) := by
    unfold T
    apply sum_congr rfl
    intro n _
    ring
  rw [hsum, hA, hH, hPhi]
  rw [hStSum]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, entry14Primitive_expansion N m hx hm]
  unfold entry14FiniteMain
  change _ =
    ((chapter7Entry14A0Approx (m + 1) - Real.log x) / x +
      (1 - ((((harmonic (m + 1) : ℚ)) : ℝ) - Real.log T)) / 2 +
      ∑ n ∈ range N,
        ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          x ^ (2 * n + 1)) * chapter7StieltjesApprox (2 * n + 1) (m + 1)) +
      entry14Boundary x m + ∑ j ∈ range m, entry14Delta N x j
  unfold T
  push_cast
  ring_nf at hcancel ⊢

private lemma entry14Coeff_succ (c : ℕ → ℝ) (n : ℕ) :
    chapter7Entry14Coeff c (n + 1) =
      (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) * c (2 * n + 1) := by
  unfold chapter7Entry14Coeff chapter7StieltjesA
  rw [show 2 * (n + 1) = 2 * n + 2 by omega,
    show 2 * n + 2 - 1 = 2 * n + 1 by omega]
  have hsign : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    rw [pow_succ]
    simp
  have hfact : (2 * n + 2).factorial = (2 * n + 2) * (2 * n + 1).factorial := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.factorial_succ]
  rw [hsign, hfact]
  push_cast
  have hfac : (((2 * n + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hn : ((2 * n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

private lemma entry14_succ_tendsto_atTop :
    Tendsto (fun m : ℕ => m + 1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  exact eventually_atTop.2 ⟨b, fun m hm => by omega⟩

private lemma entry14FiniteMain_tendsto (a0 : ℝ) (c : ℕ → ℝ)
    (ha0 : Tendsto chapter7Entry14A0Approx atTop (nhds a0))
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (nhds (c k)))
    (N : ℕ) (x : ℝ) :
    Tendsto (entry14FiniteMain N x) atTop (nhds (chapter7Entry14Approx a0 c N x)) := by
  have ha : Tendsto (fun m : ℕ => chapter7Entry14A0Approx (m + 1)) atTop (nhds a0) :=
    ha0.comp entry14_succ_tendsto_atTop
  have hh0 := Real.tendsto_harmonic_sub_log.comp entry14_succ_tendsto_atTop
  have hh : Tendsto (fun m : ℕ =>
      (((harmonic (m + 1) : ℚ)) : ℝ) - Real.log ((m : ℝ) + 1)) atTop
      (nhds Real.eulerMascheroniConstant) := by
    refine hh0.congr' (Eventually.of_forall fun m => ?_)
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hs : Tendsto (fun m : ℕ => ∑ n ∈ range N,
      ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
        x ^ (2 * n + 1)) * chapter7StieltjesApprox (2 * n + 1) (m + 1)) atTop
      (nhds (∑ n ∈ range N,
        chapter7Entry14Coeff c (n + 1) * x ^ (2 * n + 1))) := by
    let A : ℕ → ℝ := fun n =>
      (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
        x ^ (2 * n + 1)
    have hterm (n : ℕ) : Tendsto
        (fun m : ℕ => A n * chapter7StieltjesApprox (2 * n + 1) (m + 1)) atTop
        (nhds (A n * c (2 * n + 1))) := by
      exact tendsto_const_nhds.mul
        ((hc (2 * n + 1)).comp entry14_succ_tendsto_atTop)
    have ht : Tendsto (fun m : ℕ => ∑ n ∈ range N,
        A n * chapter7StieltjesApprox (2 * n + 1) (m + 1)) atTop
        (nhds (∑ n ∈ range N, A n * c (2 * n + 1))) :=
      tendsto_finsetSum (range N) fun n _ => hterm n
    convert ht using 1
    congr 1
    apply sum_congr rfl
    intro n _
    dsimp [A]
    rw [entry14Coeff_succ]
    ring
  unfold entry14FiniteMain chapter7Entry14Approx
  exact (((ha.sub tendsto_const_nhds).div_const x).add
    ((tendsto_const_nhds.sub hh).div_const 2)).add hs

private lemma entry14Boundary_tendsto_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (entry14Boundary x) atTop (nhds 0) := by
  have hT : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop b)] with m hm
    linarith
  have hlog : Tendsto (fun m : ℕ => Real.log ((m : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hT
  have hxlog : Tendsto (fun m : ℕ => x * Real.log ((m : ℝ) + 1)) atTop atTop :=
    hlog.const_mul_atTop hx
  have hneg : Tendsto (fun m : ℕ => -(x * Real.log ((m : ℝ) + 1))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hxlog
  have hexp : Tendsto (fun m : ℕ => Real.exp (-(x * Real.log ((m : ℝ) + 1))))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hneg
  have hinner : Tendsto (fun m : ℕ =>
      1 - Real.exp (-(x * Real.log ((m : ℝ) + 1)))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hexp
  have hlogInner : Tendsto (fun m : ℕ =>
      Real.log (1 - Real.exp (-(x * Real.log ((m : ℝ) + 1))))) atTop (nhds 0) := by
    convert (Real.continuousAt_log one_ne_zero).tendsto.comp hinner using 1
    · ext m
      rfl
    · simp
  unfold entry14Boundary
  simpa only [neg_mul, zero_div] using hlogInner.div_const x

private lemma entry14Sum_eq_approx_add_error (a0 : ℝ) (c : ℕ → ℝ)
    (ha0 : Tendsto chapter7Entry14A0Approx atTop (nhds a0))
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (nhds (c k)))
    (N : ℕ) {x : ℝ} (hx : 0 < x) :
    chapter7Entry14Sum x = chapter7Entry14Approx a0 c N x +
      ∑' j : ℕ, entry14Delta N x j := by
  have hleft : Tendsto (fun m : ℕ => ∑ j ∈ range m, chapter7Entry14Term x j) atTop
      (nhds (chapter7Entry14Sum x)) := by
    exact (summable_chapter7Entry14Term x hx).hasSum.tendsto_sum_nat
  have hmain := entry14FiniteMain_tendsto a0 c ha0 hc N x
  have hboundary := entry14Boundary_tendsto_zero hx
  have hdelta := (entry14Delta_summable N hx.le).hasSum.tendsto_sum_nat
  have hright : Tendsto (fun m : ℕ =>
      entry14FiniteMain N x m + entry14Boundary x m +
        ∑ j ∈ range m, entry14Delta N x j) atTop
      (nhds (chapter7Entry14Approx a0 c N x + ∑' j : ℕ, entry14Delta N x j)) := by
    simpa only [add_zero] using (hmain.add hboundary).add hdelta
  have heq : ∀ᶠ m : ℕ in atTop,
      (∑ j ∈ range m, chapter7Entry14Term x j) =
        entry14FiniteMain N x m + entry14Boundary x m +
          ∑ j ∈ range m, entry14Delta N x j := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact entry14Finite_identity N m hx hm
  exact tendsto_nhds_unique hleft
    (hright.congr' (heq.mono fun _ h => h.symm))

/-- **Asymptotic expansion of $\sum 1/(n(n^x - 1))$ as $x \to 0^+$.** Let $a_0$ be a real number
such that $\sum_{n=2}^{m} \frac{1}{n \log n} - \log \log m$ tends to $a_0$ as $m \to \infty$, and
let $(c_k)_{k \ge 0}$ be real numbers such that, for every $k \ge 0$,
$\sum_{j=1}^{m} (\log j)^k / j - (\log m)^{k+1} / (k+1)$ tends to $c_k$ as $m \to \infty$. Then for
every real $x > 0$ the series $F(x) = \sum_{n \ge 2} \frac{1}{n(n^x - 1)}$ converges absolutely, and
for every $N \ge 0$,
$$F(x) = \frac{a_0 - \log x}{x} + \frac{1 - \gamma}{2}
  + \sum_{k=1}^{N} \frac{B_{2k}\, c_{2k-1}}{(2k)!} x^{2k-1} + O(x^{2N+1})
  \quad (x \to 0^+),$$
where $\gamma$ is Euler's constant and $B_{2k}$ are the Bernoulli numbers.

Proof: Truncated Laurent expansion of the exponential kernel, an exact partial-sum identity,
and a sum-versus-integral error bound, followed by passage to the defining limits.

Proves `Wanted` entry `ramanujan_part1_ch7_entry14_bernoullipolymult`.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7.
-/
theorem ramanujan_part1_ch7_entry14_bernoullipolymult
    (a0 : ℝ) (c : ℕ → ℝ)
    (ha0 : Tendsto chapter7Entry14A0Approx atTop (𝓝 a0))
    (hc : ∀ k : ℕ,
      Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k))) :
    (∀ x : ℝ, 0 < x → Summable (chapter7Entry14Term x)) ∧
      ∀ N : ℕ,
        IsBigO (nhdsWithin 0 (Set.Ioi 0))
          (fun x : ℝ => chapter7Entry14Sum x - chapter7Entry14Approx a0 c N x)
          (fun x : ℝ => x ^ (2 * N + 1)) := by
  refine ⟨summable_chapter7Entry14Term, fun N => ?_⟩
  let C := entry14Bound N * ∑' j : ℕ, entry14Majorant N j
  refine IsBigO.of_bound C ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have heq := entry14Sum_eq_approx_add_error a0 c ha0 hc N hx
  rw [heq, add_sub_cancel_left, Real.norm_eq_abs]
  simpa [C, abs_of_pos hx] using
    entry14Delta_tsum_abs_le N hx.le

end

end Entry14Bernoullipolymult

end MathlibExt.Analysis.Ramanujan.Part1Ch7
