/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.PrivacyLoss
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Privacy-loss tests: `ε = 0` boundary, randomized response, disjoint support

Boundary checks for `CSLibExt.Privacy.PrivacyLoss`: at `ε = 0` the loss
vanishes on support and `privacyLossExpectation` vanishes; for binary randomized response
with `p = 3/4` and `ε₀ = log 3`, the losses are `± log 3`,
`privacyLossExpectation = (1/2) log 3`, and the `ε₀ * (e^ε₀ - 1)` bound evaluates to
`2 log 3`. For the disjoint-support pair `PMF.pure true` / `PMF.pure false`,
`klDiv` is infinite while the real-valued `privacyLossExpectation` totalizes to `0`.
-/

@[expose] public section

open CSLibExt.Privacy.DifferentialPrivacy

open scoped ENNReal

namespace CSLibExtTest.Privacy.PrivacyLossTests

/-- `ε = 0` boundary: the loss vanishes on support. -/
theorem privacyLoss_eq_zero_of_dp_zero {Ω : Type*} (P Q : PMF Ω) (w : Ω)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp 0) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp 0) * P w)
    (hw : P w ≠ 0) :
    privacyLoss P Q w = 0 := by
  have h := abs_privacyLoss_le_of_dp_two_sided P Q 0 w (le_refl 0) hPQ hQP hw
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- `ε = 0` boundary: `privacyLossExpectation` vanishes. -/
theorem privacyLossExpectation_eq_zero_of_dp_zero {Ω : Type*} (P Q : PMF Ω)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp 0) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp 0) * P w) :
    privacyLossExpectation P Q = 0 := by
  have hlo := privacyLossExpectation_nonneg P Q 0 (le_refl 0) hPQ hQP
  have hhi := privacyLossExpectation_le_of_dp_two_sided P Q 0 (le_refl 0) hPQ hQP
  have hhi0 : privacyLossExpectation P Q ≤ 0 := by simpa using hhi
  exact le_antisymm hhi0 hlo

/-- Masses biased toward `true`: randomized response with `p = 3/4`. -/
theorem rrP_sum : ∑ b ∈ (Finset.univ : Finset Bool),
    (match b with
      | true => ENNReal.ofReal (3/4 : ℝ)
      | false => ENNReal.ofReal (1/4 : ℝ)) = 1 := by
  have hadd : ENNReal.ofReal (3/4 : ℝ) + ENNReal.ofReal (1/4 : ℝ) = 1 := by
    rw [← ENNReal.ofReal_add (p := (3/4 : ℝ)) (q := (1/4 : ℝ)) (by norm_num)
      (by norm_num),
      show (3/4 : ℝ) + 1/4 = 1 by norm_num, ENNReal.ofReal_one]
  rw [Fintype.univ_bool,
    Finset.sum_insert (show (true : Bool) ∉ ({false} : Finset Bool) from by decide),
    Finset.sum_singleton]
  show ENNReal.ofReal (3/4 : ℝ) + ENNReal.ofReal (1/4 : ℝ) = 1
  exact hadd

/-- Masses biased toward `false`: the swapped-bit counterpart. -/
theorem rrQ_sum : ∑ b ∈ (Finset.univ : Finset Bool),
    (match b with
      | true => ENNReal.ofReal (1/4 : ℝ)
      | false => ENNReal.ofReal (3/4 : ℝ)) = 1 := by
  have hadd : ENNReal.ofReal (1/4 : ℝ) + ENNReal.ofReal (3/4 : ℝ) = 1 := by
    rw [← ENNReal.ofReal_add (p := (1/4 : ℝ)) (q := (3/4 : ℝ)) (by norm_num)
      (by norm_num),
      show (1/4 : ℝ) + 3/4 = 1 by norm_num, ENNReal.ofReal_one]
  rw [Fintype.univ_bool,
    Finset.sum_insert (show (true : Bool) ∉ ({false} : Finset Bool) from by decide),
    Finset.sum_singleton]
  show ENNReal.ofReal (1/4 : ℝ) + ENNReal.ofReal (3/4 : ℝ) = 1
  exact hadd

/-- Randomized response reporting truthfully with probability `3/4`. -/
noncomputable def rrP : PMF Bool :=
  PMF.ofFinset (fun b => match b with
    | true => ENNReal.ofReal (3/4 : ℝ)
    | false => ENNReal.ofReal (1/4 : ℝ))
    Finset.univ rrP_sum (fun b hb => False.elim (hb (Finset.mem_univ b)))

/-- The swapped-bit counterpart. -/
noncomputable def rrQ : PMF Bool :=
  PMF.ofFinset (fun b => match b with
    | true => ENNReal.ofReal (1/4 : ℝ)
    | false => ENNReal.ofReal (3/4 : ℝ))
    Finset.univ rrQ_sum (fun b hb => False.elim (hb (Finset.mem_univ b)))

private theorem rrP_true : rrP true = ENNReal.ofReal (3/4 : ℝ) := by
  unfold rrP
  simp

private theorem rrP_false : rrP false = ENNReal.ofReal (1/4 : ℝ) := by
  unfold rrP
  simp

private theorem rrQ_true : rrQ true = ENNReal.ofReal (1/4 : ℝ) := by
  unfold rrQ
  simp

private theorem rrQ_false : rrQ false = ENNReal.ofReal (3/4 : ℝ) := by
  unfold rrQ
  simp

private theorem rrP_true_toReal : (rrP true).toReal = (3/4 : ℝ) := by
  rw [rrP_true]
  exact ENNReal.toReal_ofReal (by norm_num)

private theorem rrP_false_toReal : (rrP false).toReal = (1/4 : ℝ) := by
  rw [rrP_false]
  exact ENNReal.toReal_ofReal (by norm_num)

private theorem rrQ_true_toReal : (rrQ true).toReal = (1/4 : ℝ) := by
  rw [rrQ_true]
  exact ENNReal.toReal_ofReal (by norm_num)

private theorem rrQ_false_toReal : (rrQ false).toReal = (3/4 : ℝ) := by
  rw [rrQ_false]
  exact ENNReal.toReal_ofReal (by norm_num)

/-- Privacy loss at `true` is `log 3`. -/
theorem rr_loss_true : privacyLoss rrP rrQ true = Real.log 3 := by
  show Real.log ((rrP true).toReal / (rrQ true).toReal) = Real.log 3
  rw [rrP_true_toReal, rrQ_true_toReal]
  congr 1
  norm_num

/-- Privacy loss at `false` is `-log 3`. -/
theorem rr_loss_false : privacyLoss rrP rrQ false = -Real.log 3 := by
  show Real.log ((rrP false).toReal / (rrQ false).toReal) = -Real.log 3
  rw [rrP_false_toReal, rrQ_false_toReal]
  have h13 : (1/4 : ℝ) / (3/4) = 1/3 := by norm_num
  rw [h13, show (1/3 : ℝ) = 3⁻¹ by norm_num]
  exact Real.log_inv 3

/-- `privacyLossExpectation` of randomized response is `(1/2) log 3`. -/
theorem rr_kl : privacyLossExpectation rrP rrQ = 1/2 * Real.log 3 := by
  show (∑' b, (rrP b).toReal * privacyLoss rrP rrQ b) = _
  rw [tsum_fintype, Fintype.univ_bool,
    Finset.sum_insert (show (true : Bool) ∉ ({false} : Finset Bool) from by decide),
    Finset.sum_singleton]
  show (rrP true).toReal * privacyLoss rrP rrQ true +
      (rrP false).toReal * privacyLoss rrP rrQ false = _
  rw [rrP_true_toReal, rr_loss_true, rrP_false_toReal, rr_loss_false]
  ring

private theorem rr_exp_log : Real.exp (Real.log 3) = 3 :=
  Real.exp_log (by norm_num)

/-- Randomized response satisfies the `ε₀ = log 3` bound one way. -/
private theorem rr_hPQ :
    ∀ b, rrP b ≤ ENNReal.ofReal (Real.exp (Real.log 3)) * rrQ b := by
  intro b
  cases b
  · rw [rrP_false, rrQ_false, rr_exp_log,
      ← ENNReal.ofReal_mul (p := (3 : ℝ)) (q := (3/4 : ℝ)) (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    norm_num
  · rw [rrP_true, rrQ_true, rr_exp_log,
      ← ENNReal.ofReal_mul (p := (3 : ℝ)) (q := (1/4 : ℝ)) (by norm_num),
      show (3 : ℝ) * (1/4) = 3/4 by norm_num]

/-- Randomized response satisfies the `ε₀ = log 3` bound the other way. -/
private theorem rr_hQP :
    ∀ b, rrQ b ≤ ENNReal.ofReal (Real.exp (Real.log 3)) * rrP b := by
  intro b
  cases b
  · rw [rrQ_false, rrP_false, rr_exp_log,
      ← ENNReal.ofReal_mul (p := (3 : ℝ)) (q := (1/4 : ℝ)) (by norm_num),
      show (3 : ℝ) * (1/4) = 3/4 by norm_num]
  · rw [rrQ_true, rrP_true, rr_exp_log,
      ← ENNReal.ofReal_mul (p := (3 : ℝ)) (q := (3/4 : ℝ)) (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    norm_num

/-- The KL upper bound applies to randomized response. -/
theorem rr_kl_le_p3 :
    privacyLossExpectation rrP rrQ ≤ Real.log 3 * (Real.exp (Real.log 3) - 1) :=
  privacyLossExpectation_le_of_dp_two_sided rrP rrQ (Real.log 3)
    (Real.log_nonneg (by norm_num)) rr_hPQ rr_hQP

/-- The bound evaluates to `2 log 3` at `ε₀ = log 3`. -/
theorem rr_bound_eq :
    Real.log 3 * (Real.exp (Real.log 3) - 1) = 2 * Real.log 3 := by
  rw [rr_exp_log]
  ring

/-- End to end: `(1/2) log 3 ≤ 2 log 3` via the KL upper bound. -/
theorem rr_kl_le_two_via_p3 : (1/2 : ℝ) * Real.log 3 ≤ 2 * Real.log 3 := by
  rw [← rr_kl, ← rr_bound_eq]
  exact rr_kl_le_p3

private theorem pureTrue_true : (PMF.pure true : PMF Bool) true = 1 := by
  simp [PMF.pure_apply]

private theorem pureFalse_true : (PMF.pure false : PMF Bool) true = 0 := by
  simp [PMF.pure_apply]

private theorem pureTrue_false : (PMF.pure true : PMF Bool) false = 0 := by
  simp [PMF.pure_apply]

private theorem pureFalse_false : (PMF.pure false : PMF Bool) false = 1 := by
  simp [PMF.pure_apply]

/-- Regression: disjoint supports give infinite `klDiv`, not `0`.
`PMF.pure true` charges `true` while `PMF.pure false` does not. -/
theorem klDiv_pure_true_false_eq_top :
    InformationTheory.klDiv (PMF.pure true : PMF Bool).toMeasure
      (PMF.pure false : PMF Bool).toMeasure = ∞ :=
  klDiv_toMeasure_eq_top_of_not_ac_witness _ _ true
    (by rw [pureTrue_true]; exact one_ne_zero) pureFalse_true

/-- Contrast: the real-valued loss expectation totalizes to `0` on disjoint
supports, so it is not the KL divergence without the two-sided bounds. -/
theorem privacyLossExpectation_pure_true_false_eq_zero :
    privacyLossExpectation (PMF.pure true : PMF Bool)
      (PMF.pure false : PMF Bool) = 0 := by
  show (∑' b, ((PMF.pure true : PMF Bool) b).toReal * privacyLoss _ _ b) = _
  rw [tsum_fintype, Fintype.univ_bool,
    Finset.sum_insert (show (true : Bool) ∉ ({false} : Finset Bool) from by decide),
    Finset.sum_singleton]
  show ((PMF.pure true : PMF Bool) true).toReal * privacyLoss _ _ true +
      ((PMF.pure true : PMF Bool) false).toReal * privacyLoss _ _ false = _
  simp only [privacyLoss]
  rw [pureTrue_true, pureTrue_false, pureFalse_true, pureFalse_false,
    ENNReal.toReal_one, ENNReal.toReal_zero]
  simp

#print axioms privacyLossExpectation_nonneg
#print axioms privacyLossExpectation_le_of_dp_two_sided
#print axioms klDiv_toMeasure_eq_ofReal_privacyLossExpectation
#print axioms klDiv_toMeasure_le_of_dp_two_sided
#print axioms toReal_klDiv_toMeasure_eq_privacyLossExpectation
#print axioms klDiv_toMeasure_eq_top_of_not_ac_witness
#print axioms privacyLoss_le_of_isDP
#print axioms privacyLossExpectation_nonneg_of_isDP
#print axioms privacyLossExpectation_le_of_isDP
#print axioms klDiv_toMeasure_le_of_isDP

end CSLibExtTest.Privacy.PrivacyLossTests
