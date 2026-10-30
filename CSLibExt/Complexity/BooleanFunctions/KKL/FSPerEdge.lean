/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.PBiasedTensorize
public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLUniform

/-!
# A damped KKL inequality under p-biased measures

Under the Bernoulli(`p`) product measure, integrating the capped per-coordinate
hypercontractive estimate over the noise parameter (as in `KKL.RhoOptimiseClose2` for
`p = 1/2`) gives, with `A = 4p(1-p)` and `δ = maxₑ Infₑ(1_A)`,
`2 · (∑_{S ≠ ∅} (A^{|S|-1} / A) f̂(S)²) · log (1 / δ) ≤ ∑ₑ Infₑ(1_A)`
for every `p ∈ (0, 1)` (`fpe_dampedVarLogGain`). The left side is a damped variance: the weight
`A^{|S|-1} / A` equals `1` for all `S` only at `p = 1/2`, where the inequality is the KKL inequality
with constant `2` (`fpe_kklGain_at_half`).

## Main results

* `StatMech.Probability.fpe_master_sub`: the capped estimate in the variable `u = 1 - ρ²/A`.
* `StatMech.Probability.fpe_dampedVarLogGain`: the damped KKL inequality for all `p ∈ (0, 1)`.
* `StatMech.Probability.fpe_kklGain_at_half`: the KKL inequality at `p = 1/2`, recovered from
  the `p`-biased argument.
-/

@[expose] public section

open scoped BigOperators
open Finset
open Real Filter Topology
open intervalIntegral MeasureTheory

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem fpe_summand_intervalIntegrable (A : ℝ) (cf : Finset ι → ℝ) (S : Finset ι) :
    IntervalIntegrable
      (fun u => 4 * (S.card : ℝ) * (A ^ (S.card - 1) / A) * (1 - u) ^ (S.card - 1) * cf S)
      MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

omit [Fintype ι] in
theorem fpe_integral_summand (A : ℝ) (cf : Finset ι → ℝ) (S : Finset ι) :
    (∫ u in (0 : ℝ)..1, 4 * (S.card : ℝ) * (A ^ (S.card - 1) / A) * (1 - u) ^ (S.card - 1) * cf S)
      = (if S = ∅ then 0 else 4 * (A ^ (S.card - 1) / A) * cf S) := by
  rw [show (fun u => 4 * (S.card : ℝ) * (A ^ (S.card - 1) / A) * (1 - u) ^ (S.card - 1) * cf S)
      = (fun u => (4 * (S.card : ℝ) * (A ^ (S.card - 1) / A) * cf S) * (1 - u) ^ (S.card - 1))
      from by funext u; ring]
  rw [intervalIntegral.integral_const_mul, cro2_integral_one_sub_pow]
  by_cases hS : S = ∅
  · subst hS; simp
  · rw [ite_eq_right hS]
    have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    have hh : (S.card - 1 : ℕ) + 1 = S.card := Nat.succ_pred_eq_of_pos hpos
    have hc1 : (↑(S.card - 1) + 1 : ℝ) = (S.card : ℝ) := by
      have := congrArg (Nat.cast (R := ℝ)) hh
      push_cast at this; linarith
    rw [hc1]
    have hcardpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hpos
    field_simp

/-- Integrating the damped total-influence weights over the noise parameter, with the `p`-biased
  scaling `A = 4p(1-p)`. -/
theorem fpe_integral_lhs (A : ℝ) (cf : Finset ι → ℝ) :
    (∫ u in (0 : ℝ)..1,
        ∑ S : Finset ι, 4 * (S.card : ℝ) * (A ^ (S.card - 1) / A) * (1 - u) ^ (S.card - 1) * cf S)
      = 4 * ∑ S ∈ (univ.erase (∅ : Finset ι)), (A ^ (S.card - 1) / A) * cf S := by
  rw [intervalIntegral.integral_finsetSum
      (fun S _ => fpe_summand_intervalIntegrable A cf S)]
  simp_rw [fpe_integral_summand A cf]
  rw [← Finset.add_sum_erase univ
      (fun S => if S = ∅ then (0 : ℝ) else 4 * (A ^ (S.card - 1) / A) * cf S) (Finset.mem_univ ∅)]
  rw [ite_eq_left rfl, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [ite_eq_right (Finset.ne_of_mem_erase hS)]; ring

/-- The capped per-coordinate estimate under `μ_p` in the variable `u`, with `ρ² = A (1 - u)` and `A
  = 4p(1-p)`. -/
theorem fpe_master_sub [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ)
        * ((4 * p * (1 - p)) ^ (S.card - 1) / (4 * p * (1 - p)))
        * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set A := 4 * p * (1 - p) with hA
  have hApos : 0 < A := by rw [hA]; nlinarith
  have hAle1 : A ≤ 1 := by rw [hA]; nlinarith [sq_nonneg (2 * p - 1)]
  have hu1' : (0 : ℝ) ≤ 1 - u := by linarith
  set ρ := Real.sqrt ((1 - u) * A) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρsq : ρ ^ 2 = (1 - u) * A := Real.sq_sqrt (mul_nonneg hu1' hApos.le)
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]
    apply Real.sqrt_le_one.mpr
    nlinarith [hu1', hApos.le, hAle1, hu0]
  set q' := 2 - u with hq'
  have hq1 : (1 : ℝ) ≤ q' := by rw [hq']; linarith
  have hq2 : q' ≤ 2 := by rw [hq']; linarith
  have hρsq' : ρ ^ 2 = (q' - 1) * 4 * p * (1 - p) := by
    rw [hρsq, hq', hA]; ring
  have Hcap := ptn_capped_hc hp0 hp1 hρ0 hρ1 hq1 hq2 hρsq' φ
  have hexp : (2 : ℝ) / q' - 1 = u / (2 - u) := by
    rw [hq', div_sub_one (by linarith : (2 : ℝ) - u ≠ 0)]; ring_nf
  rw [hexp] at Hcap
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  have hpow : ∀ S : Finset ι, (ρ ^ (S.card - 1)) ^ 2 = ((1 - u) * A) ^ (S.card - 1) := by
    intro S; rw [← pow_mul, mul_comm, pow_mul, hρsq]
  have hσ2 : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hppos : 0 < p * (1 - p) := by nlinarith
  have hAsigma : (1 / (ptn_sigma p) ^ 2) = 4 / A := by
    rw [hσ2, hA]
    rw [div_eq_div_iff (ne_of_gt hppos) (by positivity)]
    ring
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hLHSeq : (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2
        * (ptn_coeff p f S) ^ 2)
      = ∑ S : Finset ι, 4 * (S.card : ℝ) * (A ^ (S.card - 1) / A) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p f S) ^ 2 := by
    rw [hAsigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [hpow S, mul_pow]
    field_simp
  rw [hLHSeq] at Hcap
  exact Hcap

/-- Damped KKL inequality under the Bernoulli(`p`) measure, `0 < p < 1`: with `A = 4p(1-p)`, `2 ·
  (∑_{S ≠ ∅} (A^{|S|-1} / A) f̂(S)²) · log (1 / maxₑ Infₑ) ≤ ∑ₑ Infₑ`. -/
theorem fpe_dampedVarLogGain [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) :
    2 * (∑ S ∈ (univ.erase (∅ : Finset ι)),
          ((4 * p * (1 - p)) ^ (S.card - 1) / (4 * p * (1 - p)))
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set A := 4 * p * (1 - p) with hA
  have hApos : 0 < A := by rw [hA]; nlinarith
  set cf := fun S : Finset ι => (ptn_coeff p f S) ^ 2 with hcf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  set Q := ∑ S ∈ (univ.erase (∅ : Finset ι)), (A ^ (S.card - 1) / A) * cf S with hQ
  have hprob := OSSS.bernoulliWeight_isProbWeight (E := ι) hp0.le hp1.le
  have hTnn : 0 ≤ T := kkl_totalInfl_nonneg hprob f
  have hδnn : 0 ≤ δ := kkl_maxInfl_nonneg hprob f
  have hQnn : 0 ≤ Q := by
    rw [hQ]; exact Finset.sum_nonneg (fun S _ => by rw [hcf]; positivity)
  change 2 * Q * Real.log (1 / δ) ≤ T
  rcases lt_trichotomy δ 1 with hδ1 | hδ1 | hδ1
  · rcases eq_or_lt_of_le hδnn with hδ0 | hδ0
    · rw [← hδ0, div_zero, Real.log_zero, mul_zero]; exact hTnn
    · have ht : 0 < -(Real.log δ) := by have := Real.log_neg hδ0 hδ1; linarith
      have hlogeq : Real.log (1 / δ) = -(Real.log δ) := by
        rw [Real.log_div one_ne_zero (ne_of_gt hδ0), Real.log_one, zero_sub]
      have hIntLhs : (∫ u in (0 : ℝ)..1, ∑ S : Finset ι, 4 * (S.card : ℝ) * (A ^ (S.card - 1) / A)
          * (1 - u) ^ (S.card - 1) * cf S) = 4 * Q := by
        rw [fpe_integral_lhs A cf]
      have hIntRhs : (∫ u in (0 : ℝ)..1, δ ^ (u / (2 - u)) * T) ≤ T * (2 / (-(Real.log δ))) := by
        rw [intervalIntegral.integral_mul_const, mul_comm T _]
        exact mul_le_mul_of_nonneg_right (cro2_integral_rhs_le δ hδ0 hδ1) hTnn
      have hmono : (∫ u in (0 : ℝ)..1, ∑ S : Finset ι, 4 * (S.card : ℝ) * (A ^ (S.card - 1) / A)
            * (1 - u) ^ (S.card - 1) * cf S)
          ≤ (∫ u in (0 : ℝ)..1, δ ^ (u / (2 - u)) * T) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · apply Continuous.intervalIntegrable; fun_prop
        · exact (cro2_rpow_integrable δ hδ0).mul_const T
        · intro u hu
          simp only [Set.mem_Icc] at hu
          have hms := fpe_master_sub hp0 hp1 φ u hu.1 hu.2
          calc (∑ S : Finset ι,
              4 * (S.card : ℝ) * (A ^ (S.card - 1) / A) * (1 - u) ^ (S.card - 1) * cf S)
              = (∑ S : Finset ι,
                  4 * (S.card : ℝ) * ((4 * p * (1 - p)) ^ (S.card - 1) / (4 * p * (1 - p)))
                  * (1 - u) ^ (S.card - 1) * (ptn_coeff p f S) ^ 2) := by
                apply Finset.sum_congr rfl; intro S _; rw [hcf, hA]
            _ ≤ δ ^ (u / (2 - u)) * T := hms
      rw [hIntLhs] at hmono
      have hfin : 4 * Q ≤ T * (2 / (-(Real.log δ))) := le_trans hmono hIntRhs
      rw [hlogeq]
      rw [mul_div_assoc'] at hfin
      rw [le_div_iff₀ ht] at hfin
      nlinarith [hfin, ht]
  · rw [hδ1, div_one, Real.log_one, mul_zero]; exact hTnn
  · have hlog : Real.log (1 / δ) ≤ 0 := by
      rw [Real.log_div one_ne_zero (by linarith), Real.log_one, zero_sub, neg_nonpos]
      exact Real.log_nonneg (by linarith)
    nlinarith [hQnn, hTnn, hlog]

/-- At `p = 1/2` the damped variance is the variance. -/
theorem fpe_Q_eq_var_at_half (φ : ConfigSpace ι → Bool) :
    (∑ S ∈ (univ.erase (∅ : Finset ι)),
        ((4 * (1/2 : ℝ) * (1 - 1/2)) ^ (S.card - 1) / (4 * (1/2 : ℝ) * (1 - 1/2)))
          * (ptn_coeff (1/2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      = OSSS.var (OSSS.bernoulliWeight (1/2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  rw [ptn_var_eq_fourierWeight (by norm_num) (by norm_num)]
  apply Finset.sum_congr rfl
  intro S _
  rw [show (4 * (1/2 : ℝ) * (1 - 1/2)) = 1 by norm_num, one_pow, div_one, one_mul]

/-- The KKL inequality with constant `2` at `p = 1/2`, obtained from `fpe_dampedVarLogGain`. The
  same statement is `kkl_inequality_total fsr_pbiased_endpoint`, proved there by the
  uniform-cube argument. -/
theorem fpe_kklGain_at_half [Nonempty ι] (φ : ConfigSpace ι → Bool) :
    2 * OSSS.var (OSSS.bernoulliWeight (1/2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1/2 : ℝ))
            (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight (1/2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have h := fpe_dampedVarLogGain (p := (1/2 : ℝ)) (by norm_num) (by norm_num) φ
  rwa [fpe_Q_eq_var_at_half φ] at h

end StatMech.Probability
