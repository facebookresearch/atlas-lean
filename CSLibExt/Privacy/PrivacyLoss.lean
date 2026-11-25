/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DifferentialPrivacy
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Privacy-loss random variable and KL bound

For discrete distributions `P Q : PMF Ω`, the privacy loss at `w` is
`log (P w / Q w)` on real-valued masses, and `privacyLossExpectation P Q` is the
`P`-expectation of the loss. Under two-sided pointwise bounds
`P w ≤ e^ε * Q w` and `Q w ≤ e^ε * P w`, the loss is bounded by `ε` on
the common support, the expectation is nonnegative (Gibbs), agrees with
Mathlib's `InformationTheory.klDiv` on `P.toMeasure` and `Q.toMeasure`, and
is at most `ε * (e^ε - 1)`.

The real-valued expectation is only meaningful as KL divergence under the
two-sided bounds: off the common support it totalizes to `0` (both `1 / 0`
and `log 0` are `0`), where the true KL divergence is infinite. The headline
results are therefore stated with `klDiv`; the real sum is kept as the
conditional quantity `privacyLossExpectation` with its domain documented.

This is the discrete case of Dwork and Roth, *The Algorithmic
Foundations of Differential Privacy* (2014), Lemma 3.18: a two-sided
`D∞ ≤ ε` bound implies `KL ≤ ε * (e^ε - 1)`.

Not covered here: no `(ε, δ)` approximate-DP variant.
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

open scoped ENNReal MeasureTheory

/-- Privacy loss of outcome `w`: `log` of the ratio of real-valued masses. -/
noncomputable def privacyLoss {Ω : Type*} (P Q : PMF Ω) (w : Ω) : ℝ :=
  Real.log ((P w).toReal / (Q w).toReal)

/-- Real-valued loss expectation: the `P`-expectation of `privacyLoss`.
Agreement with `InformationTheory.klDiv P.toMeasure Q.toMeasure` needs
absolute continuity of `P.toMeasure` with respect to `Q.toMeasure` together
with finiteness/integrability of the log-likelihood ratio. The two-sided
pointwise DP bounds assumed below are one sufficient condition (see
`klDiv_toMeasure_eq_ofReal_privacyLossExpectation`); a `P`-charged outcome
missed by `Q` contributes `0` to this sum while making the true divergence
infinite (see `klDiv_toMeasure_eq_top_of_not_ac_witness`). -/
noncomputable def privacyLossExpectation {Ω : Type*} (P Q : PMF Ω) : ℝ :=
  ∑' w, (P w).toReal * privacyLoss P Q w

/-- Real-valued form of a pointwise DP bound. -/
private theorem toReal_le_of_dp_le {Ω : Type*} (P Q : PMF Ω) (ε : ℝ) (w : Ω)
    (h : P w ≤ ENNReal.ofReal (Real.exp ε) * Q w) :
    (P w).toReal ≤ Real.exp ε * (Q w).toReal := by
  have hfin : ENNReal.ofReal (Real.exp ε) * Q w ≠ Top.top :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Q.apply_ne_top w)
  have h' := (ENNReal.toReal_le_toReal (P.apply_ne_top w) hfin).mpr h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos ε).le] at h'

/-- Two-sided pointwise bounds force outcomes to vanish together. -/
private theorem eq_zero_iff_of_dp_two_sided {Ω : Type*} (P Q : PMF Ω) (ε : ℝ)
    (w : Ω)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    P w = 0 ↔ Q w = 0 := by
  constructor
  · intro h
    have hQ := hQP w
    rw [h, mul_zero] at hQ
    exact le_antisymm hQ zero_le
  · intro h
    have hP := hPQ w
    rw [h, mul_zero] at hP
    exact le_antisymm hP zero_le

/-- Two-sided pointwise DP bounds force common support. -/
theorem support_eq_of_dp_two_sided {Ω : Type*} (P Q : PMF Ω) (ε : ℝ)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    P.support = Q.support := by
  ext w
  rw [PMF.mem_support_iff, PMF.mem_support_iff]
  exact not_congr (eq_zero_iff_of_dp_two_sided P Q ε w hPQ hQP)

/-- A one-sided pointwise bound gives `privacyLoss ≤ ε` at every outcome. -/
theorem privacyLoss_le_of_dp_le {Ω : Type*} (P Q : PMF Ω) (ε : ℝ) (w : Ω)
    (hε : 0 ≤ ε)
    (h : P w ≤ ENNReal.ofReal (Real.exp ε) * Q w) :
    privacyLoss P Q w ≤ ε := by
  have hR := toReal_le_of_dp_le P Q ε w h
  by_cases hQ : (Q w).toReal = 0
  · have hP : (P w).toReal = 0 :=
      le_antisymm (by simpa [hQ] using hR) ENNReal.toReal_nonneg
    show Real.log ((P w).toReal / (Q w).toReal) ≤ ε
    rw [hP, hQ, zero_div, Real.log_zero]
    exact hε
  · by_cases hP : (P w).toReal = 0
    · show Real.log ((P w).toReal / (Q w).toReal) ≤ ε
      rw [hP, zero_div, Real.log_zero]
      exact hε
    · have hQpos : 0 < (Q w).toReal :=
        lt_of_le_of_ne' ENNReal.toReal_nonneg hQ
      have hPpos : 0 < (P w).toReal :=
        lt_of_le_of_ne' ENNReal.toReal_nonneg hP
      have hdiv : (P w).toReal / (Q w).toReal ≤ Real.exp ε :=
        (div_le_iff₀ hQpos).mpr hR
      show Real.log ((P w).toReal / (Q w).toReal) ≤ ε
      rw [← Real.log_exp ε]
      exact Real.log_le_log (div_pos hPpos hQpos) hdiv

/-- On support, the two-sided bound gives `|privacyLoss| ≤ ε`. -/
theorem abs_privacyLoss_le_of_dp_two_sided {Ω : Type*} (P Q : PMF Ω) (ε : ℝ)
    (w : Ω) (hε : 0 ≤ ε)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w)
    (hw : P w ≠ 0) :
    |privacyLoss P Q w| ≤ ε := by
  have hQw : Q w ≠ 0 :=
    fun h => hw ((eq_zero_iff_of_dp_two_sided P Q ε w hPQ hQP).mpr h)
  have hPpos : 0 < (P w).toReal := ENNReal.toReal_pos hw (P.apply_ne_top w)
  have hQpos : 0 < (Q w).toReal := ENNReal.toReal_pos hQw (Q.apply_ne_top w)
  have hneg : privacyLoss Q P w = -privacyLoss P Q w := by
    show Real.log _ = -Real.log _
    rw [Real.log_div (ne_of_gt hQpos) (ne_of_gt hPpos),
      Real.log_div (ne_of_gt hPpos) (ne_of_gt hQpos), neg_sub]
  have h2 : privacyLoss Q P w ≤ ε := privacyLoss_le_of_dp_le Q P ε w hε (hQP w)
  rw [hneg] at h2
  rw [abs_le]
  exact ⟨(neg_le).mp h2, privacyLoss_le_of_dp_le P Q ε w hε (hPQ w)⟩

/-- Real-valued PMF masses are summable. -/
private theorem summable_toReal_apply {Ω : Type*} (P : PMF Ω) :
    Summable fun w => (P w).toReal :=
  ENNReal.summable_toReal P.tsum_coe_ne_top

/-- Real-valued PMF masses sum to one. -/
private theorem tsum_toReal_apply {Ω : Type*} (P : PMF Ω) :
    ∑' w, (P w).toReal = 1 := by
  have h := ENNReal.tsum_toReal_eq (fun w => P.apply_ne_top w)
  rw [P.tsum_coe, ENNReal.toReal_one] at h
  exact h.symm

/-- Expectation summands are bounded by `ε * P w`, hence summable. Apply twice
for the symmetric term before combining series. -/
theorem summable_privacyLossTerm_of_dp_two_sided {Ω : Type*} (P Q : PMF Ω) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    Summable fun w => (P w).toReal * privacyLoss P Q w := by
  apply Summable.of_norm_bounded ((summable_toReal_apply P).mul_left ε)
  intro w
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hw : P w = 0
  · have hPw : (P w).toReal = 0 := by simp [hw]
    simp [hPw]
  · have habs := abs_privacyLoss_le_of_dp_two_sided P Q ε w hε hPQ hQP hw
    have hnn : 0 ≤ (P w).toReal := ENNReal.toReal_nonneg
    rw [abs_of_nonneg hnn, mul_comm ε ((P w).toReal)]
    exact mul_le_mul_of_nonneg_left habs hnn

/-- The Gibbs comparison term is the negated expectation summand. -/
private theorem gibbs_term_eq_neg {Ω : Type*} (P Q : PMF Ω) (ε : ℝ) (w : Ω)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    (P w).toReal * Real.log ((Q w).toReal / (P w).toReal) =
      -((P w).toReal * privacyLoss P Q w) := by
  by_cases hw : P w = 0
  · have hPw : (P w).toReal = 0 := by simp [hw]
    simp [hPw]
  · have hQw : Q w ≠ 0 :=
      fun h => hw ((eq_zero_iff_of_dp_two_sided P Q ε w hPQ hQP).mpr h)
    have hPpos : 0 < (P w).toReal := ENNReal.toReal_pos hw (P.apply_ne_top w)
    have hQpos : 0 < (Q w).toReal := ENNReal.toReal_pos hQw (Q.apply_ne_top w)
    show (P w).toReal * Real.log _ = -((P w).toReal * Real.log _)
    rw [Real.log_div (ne_of_gt hQpos) (ne_of_gt hPpos),
      Real.log_div (ne_of_gt hPpos) (ne_of_gt hQpos)]
    ring

/-- Gibbs pointwise inequality via `log x ≤ x - 1` at `Q w / P w`. -/
private theorem gibbs_le {Ω : Type*} (P Q : PMF Ω) (ε : ℝ) (w : Ω)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    (P w).toReal * Real.log ((Q w).toReal / (P w).toReal) ≤
      (P w).toReal * ((Q w).toReal / (P w).toReal - 1) := by
  by_cases hw : P w = 0
  · have hPw : (P w).toReal = 0 := by simp [hw]
    simp [hPw]
  · have hQw : Q w ≠ 0 :=
      fun h => hw ((eq_zero_iff_of_dp_two_sided P Q ε w hPQ hQP).mpr h)
    have hPpos : 0 < (P w).toReal := ENNReal.toReal_pos hw (P.apply_ne_top w)
    have hQpos : 0 < (Q w).toReal := ENNReal.toReal_pos hQw (Q.apply_ne_top w)
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hPpos)
    exact Real.log_le_sub_one_of_pos (div_pos hQpos hPpos)

/-- The Gibbs majorant telescopes to `Q w - P w` pointwise. -/
private theorem gibbs_rhs_eq {Ω : Type*} (P Q : PMF Ω) (ε : ℝ) (w : Ω)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    (P w).toReal * ((Q w).toReal / (P w).toReal - 1) =
      (Q w).toReal - (P w).toReal := by
  by_cases hw : P w = 0
  · have hQw : Q w = 0 := (eq_zero_iff_of_dp_two_sided P Q ε w hPQ hQP).mp hw
    have hPw : (P w).toReal = 0 := by simp [hw]
    have hQ0 : (Q w).toReal = 0 := by simp [hQw]
    simp [hPw, hQ0]
  · have hPpos : 0 < (P w).toReal := ENNReal.toReal_pos hw (P.apply_ne_top w)
    have hcancel : (P w).toReal * ((Q w).toReal / (P w).toReal) = (Q w).toReal :=
      mul_div_cancel₀ _ (ne_of_gt hPpos)
    rw [mul_sub, hcancel, mul_one]

/-- Gibbs inequality: `privacyLossExpectation` is nonnegative under two-sided bounds. -/
theorem privacyLossExpectation_nonneg {Ω : Type*} (P Q : PMF Ω) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    0 ≤ privacyLossExpectation P Q := by
  have ht : Summable fun w => (P w).toReal * privacyLoss P Q w :=
    summable_privacyLossTerm_of_dp_two_sided P Q ε hε hPQ hQP
  have hu : Summable fun w => (P w).toReal * Real.log ((Q w).toReal / (P w).toReal) :=
    (summable_congr (fun w => gibbs_term_eq_neg P Q ε w hPQ hQP)).mpr ht.neg
  have hv : Summable fun w => (P w).toReal * ((Q w).toReal / (P w).toReal - 1) :=
    (summable_congr (fun w => gibbs_rhs_eq P Q ε w hPQ hQP)).mpr
      ((summable_toReal_apply Q).sub (summable_toReal_apply P))
  have hsum : ∑' w, (P w).toReal * Real.log ((Q w).toReal / (P w).toReal) =
      -privacyLossExpectation P Q := by
    rw [tsum_congr (fun w => gibbs_term_eq_neg P Q ε w hPQ hQP)]
    exact tsum_neg
  have hzero : ∑' w, (P w).toReal * ((Q w).toReal / (P w).toReal - 1) = 0 := by
    rw [tsum_congr (fun w => gibbs_rhs_eq P Q ε w hPQ hQP),
      Summable.tsum_sub (summable_toReal_apply Q) (summable_toReal_apply P),
      tsum_toReal_apply Q, tsum_toReal_apply P, sub_self]
  have hle : ∑' w, (P w).toReal * Real.log ((Q w).toReal / (P w).toReal) ≤
      ∑' w, (P w).toReal * ((Q w).toReal / (P w).toReal - 1) :=
    Summable.tsum_le_tsum (fun w => gibbs_le P Q ε w hPQ hQP) hu hv
  rw [hsum, hzero] at hle
  exact neg_nonpos.mp hle

/-- The symmetrized summand is bounded by `ε * |P w - Q w|`. -/
private theorem symm_term_le {Ω : Type*} (P Q : PMF Ω) (ε : ℝ) (w : Ω)
    (hε : 0 ≤ ε)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    ((P w).toReal - (Q w).toReal) * privacyLoss P Q w ≤
      ε * |(P w).toReal - (Q w).toReal| := by
  by_cases hw : P w = 0
  · have hQw : Q w = 0 := (eq_zero_iff_of_dp_two_sided P Q ε w hPQ hQP).mp hw
    have hPw : (P w).toReal = 0 := by simp [hw]
    have hQ0 : (Q w).toReal = 0 := by simp [hQw]
    simp [hPw, hQ0]
  · have habs := abs_privacyLoss_le_of_dp_two_sided P Q ε w hε hPQ hQP hw
    calc ((P w).toReal - (Q w).toReal) * privacyLoss P Q w
        ≤ |(P w).toReal - (Q w).toReal| * |privacyLoss P Q w| := by
          rw [← abs_mul]
          exact le_abs_self _
      _ ≤ |(P w).toReal - (Q w).toReal| * ε :=
          mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ = ε * |(P w).toReal - (Q w).toReal| := mul_comm _ _

/-- Variation is bounded by `(e^ε - 1)` times the pointwise minimum. -/
private theorem abs_sub_le_exp_sub_one_mul_min {Ω : Type*} (P Q : PMF Ω) (ε : ℝ)
    (w : Ω)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    |(P w).toReal - (Q w).toReal| ≤
      (Real.exp ε - 1) * min (P w).toReal (Q w).toReal := by
  have hR1 := toReal_le_of_dp_le P Q ε w (hPQ w)
  have hR2 := toReal_le_of_dp_le Q P ε w (hQP w)
  by_cases hw : P w = 0
  · have hQw : Q w = 0 := (eq_zero_iff_of_dp_two_sided P Q ε w hPQ hQP).mp hw
    have hPw : (P w).toReal = 0 := by simp [hw]
    have hQ0 : (Q w).toReal = 0 := by simp [hQw]
    simp [hPw, hQ0]
  · rcases le_total (P w).toReal (Q w).toReal with hle | hle
    · rw [abs_of_nonpos (sub_nonpos.mpr hle), min_eq_left hle, neg_sub]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hle), min_eq_right hle]
      linarith

/-- Adding loss summands in both directions symmetrizes to `(p - q) * L`. -/
private theorem add_privacyLossTerm_eq {Ω : Type*} (P Q : PMF Ω) (ε : ℝ) (w : Ω)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    (P w).toReal * privacyLoss P Q w + (Q w).toReal * privacyLoss Q P w =
      ((P w).toReal - (Q w).toReal) * privacyLoss P Q w := by
  by_cases hw : P w = 0
  · have hQw : Q w = 0 := (eq_zero_iff_of_dp_two_sided P Q ε w hPQ hQP).mp hw
    have hPw : (P w).toReal = 0 := by simp [hw]
    have hQ0 : (Q w).toReal = 0 := by simp [hQw]
    simp [hPw, hQ0]
  · have hQw : Q w ≠ 0 :=
      fun h => hw ((eq_zero_iff_of_dp_two_sided P Q ε w hPQ hQP).mpr h)
    have hPpos : 0 < (P w).toReal := ENNReal.toReal_pos hw (P.apply_ne_top w)
    have hQpos : 0 < (Q w).toReal := ENNReal.toReal_pos hQw (Q.apply_ne_top w)
    have hneg : privacyLoss Q P w = -privacyLoss P Q w := by
      show Real.log _ = -Real.log _
      rw [Real.log_div (ne_of_gt hQpos) (ne_of_gt hPpos),
        Real.log_div (ne_of_gt hPpos) (ne_of_gt hQpos), neg_sub]
    rw [hneg]
    ring

/-- Loss-expectation upper bound from two-sided DP bounds
(discrete Dwork-Roth Lemma 3.18 core estimate):
`privacyLossExpectation P Q ≤ ε * (e^ε - 1)`. -/
theorem privacyLossExpectation_le_of_dp_two_sided {Ω : Type*} (P Q : PMF Ω) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    privacyLossExpectation P Q ≤ ε * (Real.exp ε - 1) := by
  have htP := summable_privacyLossTerm_of_dp_two_sided P Q ε hε hPQ hQP
  have htQ := summable_privacyLossTerm_of_dp_two_sided Q P ε hε hQP hPQ
  have hnonnegQ := privacyLossExpectation_nonneg Q P ε hε hQP hPQ
  have hs : Summable fun w => ((P w).toReal - (Q w).toReal) * privacyLoss P Q w :=
    (summable_congr (fun w => (add_privacyLossTerm_eq P Q ε w hPQ hQP).symm)).mpr
      (htP.add htQ)
  have hadd : ∑' w, ((P w).toReal - (Q w).toReal) * privacyLoss P Q w =
      privacyLossExpectation P Q + privacyLossExpectation Q P := by
    rw [tsum_congr (fun w => (add_privacyLossTerm_eq P Q ε w hPQ hQP).symm)]
    exact Summable.tsum_add htP htQ
  have hPsub := summable_toReal_apply P
  have hQsub := summable_toReal_apply Q
  have habs : Summable fun w => |(P w).toReal - (Q w).toReal| :=
    Summable.of_nonneg_of_le (fun w => abs_nonneg _) (fun w => by
      have hp0 : 0 ≤ (P w).toReal := ENNReal.toReal_nonneg
      have hq0 : 0 ≤ (Q w).toReal := ENNReal.toReal_nonneg
      exact abs_le.mpr ⟨by linarith, by linarith⟩) (hPsub.add hQsub)
  have heps : Summable fun w => ε * |(P w).toReal - (Q w).toReal| :=
    habs.mul_left ε
  have hmin : Summable fun w => min (P w).toReal (Q w).toReal :=
    Summable.of_nonneg_of_le
      (fun w => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun w => min_le_left _ _) hPsub
  have hexp : Summable fun w => (Real.exp ε - 1) * min (P w).toReal (Q w).toReal :=
    hmin.mul_left _
  have hE1 : (0 : ℝ) ≤ Real.exp ε - 1 := by
    have h := Real.add_one_le_exp ε
    linarith
  have hstep1 : ∑' w, ((P w).toReal - (Q w).toReal) * privacyLoss P Q w ≤
      ∑' w, ε * |(P w).toReal - (Q w).toReal| :=
    Summable.tsum_le_tsum (fun w => symm_term_le P Q ε w hε hPQ hQP) hs heps
  have hmin1 : ∑' w, min (P w).toReal (Q w).toReal ≤ 1 := by
    rw [← tsum_toReal_apply P]
    exact Summable.tsum_le_tsum (fun w => min_le_left _ _) hmin hPsub
  have habs_le : ∑' w, |(P w).toReal - (Q w).toReal| ≤
      ∑' w, (Real.exp ε - 1) * min (P w).toReal (Q w).toReal :=
    Summable.tsum_le_tsum
      (fun w => abs_sub_le_exp_sub_one_mul_min P Q ε w hPQ hQP) habs hexp
  calc privacyLossExpectation P Q ≤ privacyLossExpectation P Q + privacyLossExpectation Q P := le_add_of_nonneg_right hnonnegQ
    _ = ∑' w, ((P w).toReal - (Q w).toReal) * privacyLoss P Q w := hadd.symm
    _ ≤ ∑' w, ε * |(P w).toReal - (Q w).toReal| := hstep1
    _ = ε * ∑' w, |(P w).toReal - (Q w).toReal| := tsum_mul_left
    _ ≤ ε * (∑' w, (Real.exp ε - 1) * min (P w).toReal (Q w).toReal) :=
        mul_le_mul_of_nonneg_left habs_le hε
    _ = ε * ((Real.exp ε - 1) * ∑' w, min (P w).toReal (Q w).toReal) := by
        rw [tsum_mul_left]
    _ ≤ ε * ((Real.exp ε - 1) * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin1 hE1) hε
    _ = ε * (Real.exp ε - 1) := by ring

/-- One-sided mechanism bound: `IsDP` gives `privacyLoss ≤ ε` without symmetry. -/
theorem privacyLoss_le_of_isDP {Database Output : Type*} (M : Database → PMF Output)
    (adj : Database → Database → Prop) (ε : ℝ) (d d₂ : Database)
    (hM : IsDP M adj ε) (hadj : adj d d₂) (o : Output) :
    privacyLoss (M d) (M d₂) o ≤ ε :=
  privacyLoss_le_of_dp_le (M d) (M d₂) ε o hM.1 (hM.2 d d₂ hadj o)

/-- Mechanism loss expectation is nonnegative when adjacency holds both ways. -/
theorem privacyLossExpectation_nonneg_of_isDP {Database Output : Type*} (M : Database → PMF Output)
    (adj : Database → Database → Prop) (ε : ℝ) (d d₂ : Database)
    (hM : IsDP M adj ε) (hadj : adj d d₂) (hadj_symm : adj d₂ d) :
    0 ≤ privacyLossExpectation (M d) (M d₂) :=
  privacyLossExpectation_nonneg (M d) (M d₂) ε hM.1 (fun o => hM.2 d d₂ hadj o)
    (fun o => hM.2 d₂ d hadj_symm o)

/-- Mechanism loss-expectation upper bound when adjacency holds both ways. -/
theorem privacyLossExpectation_le_of_isDP {Database Output : Type*} (M : Database → PMF Output)
    (adj : Database → Database → Prop) (ε : ℝ) (d d₂ : Database)
    (hM : IsDP M adj ε) (hadj : adj d d₂) (hadj_symm : adj d₂ d) :
    privacyLossExpectation (M d) (M d₂) ≤ ε * (Real.exp ε - 1) :=
  privacyLossExpectation_le_of_dp_two_sided (M d) (M d₂) ε hM.1 (fun o => hM.2 d d₂ hadj o)
    (fun o => hM.2 d₂ d hadj_symm o)

/-- `P.toMeasure` is supported on `P.support`. -/
private theorem ae_mem_support_toMeasure {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : PMF Ω) :
    ∀ᵐ w ∂P.toMeasure, w ∈ P.support := by
  rw [MeasureTheory.ae_iff]
  show P.toMeasure P.supportᶜ = 0
  rw [P.toMeasure_apply_eq_toOuterMeasure, PMF.toOuterMeasure_apply_eq_zero_iff]
  exact disjoint_compl_right

/-- Two-sided pointwise bounds give absolute continuity of the PMF measures:
a `Q`-null set is disjoint from the common support, hence `P`-null. -/
private theorem toMeasure_ac_of_dp_two_sided {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P Q : PMF Ω) (ε : ℝ)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    P.toMeasure ≪ Q.toMeasure := by
  intro s hs
  rw [Q.toMeasure_apply_eq_toOuterMeasure, PMF.toOuterMeasure_apply_eq_zero_iff] at hs
  rw [P.toMeasure_apply_eq_toOuterMeasure, PMF.toOuterMeasure_apply_eq_zero_iff]
  rwa [← support_eq_of_dp_two_sided P Q ε hPQ hQP] at hs

/-- Under two-sided bounds, `P.toMeasure` has density `P w / Q w` against
`Q.toMeasure`. -/
private theorem toMeasure_eq_withDensity_div {Ω : Type*} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P Q : PMF Ω) (ε : ℝ)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    P.toMeasure = Q.toMeasure.withDensity fun w => P w / Q w := by
  apply MeasureTheory.Measure.ext_of_singleton
  intro a
  rw [MeasureTheory.withDensity_apply _ (MeasurableSet.singleton a),
    MeasureTheory.lintegral_singleton,
    P.toMeasure_apply_singleton _ (MeasurableSet.singleton a),
    Q.toMeasure_apply_singleton _ (MeasurableSet.singleton a)]
  by_cases hQa : Q a = 0
  · have hPa : P a = 0 := (eq_zero_iff_of_dp_two_sided P Q ε a hPQ hQP).mpr hQa
    simp [hPa, hQa]
  · exact (ENNReal.div_mul_cancel hQa (Q.apply_ne_top a)).symm

/-- The Radon-Nikodym derivative of the PMF measures is the mass ratio, a.e. -/
private theorem rnDeriv_toMeasure_ae_eq_div {Ω : Type*} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P Q : PMF Ω) (ε : ℝ)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    P.toMeasure.rnDeriv Q.toMeasure =ᵐ[P.toMeasure] fun w => P w / Q w := by
  have hac := toMeasure_ac_of_dp_two_sided P Q ε hPQ hQP
  have hρ := toMeasure_eq_withDensity_div P Q ε hPQ hQP
  have hQ : P.toMeasure.rnDeriv Q.toMeasure =ᵐ[Q.toMeasure] fun w => P w / Q w := by
    rw [hρ]
    exact MeasureTheory.Measure.rnDeriv_withDensity _
      (measurable_of_countable fun w => P w / Q w)
  exact MeasureTheory.ae_iff.mpr (hac (MeasureTheory.ae_iff.mp hQ))

/-- The log-likelihood ratio agrees a.e. with `privacyLoss` under two-sided bounds. -/
private theorem llr_toMeasure_ae_eq_privacyLoss {Ω : Type*} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P Q : PMF Ω) (ε : ℝ)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    MeasureTheory.llr P.toMeasure Q.toMeasure =ᵐ[P.toMeasure] privacyLoss P Q := by
  have hrn := rnDeriv_toMeasure_ae_eq_div P Q ε hPQ hQP
  have hmem := ae_mem_support_toMeasure P
  filter_upwards [hrn, hmem] with w hrw hsup
  simp only [MeasureTheory.llr, hrw, ENNReal.toReal_div, privacyLoss]

/-- The log-likelihood ratio is integrable: it is a.e. bounded by `ε`. -/
private theorem integrable_llr_toMeasure {Ω : Type*} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P Q : PMF Ω) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    MeasureTheory.Integrable (MeasureTheory.llr P.toMeasure Q.toMeasure) P.toMeasure := by
  have hllr := llr_toMeasure_ae_eq_privacyLoss P Q ε hPQ hQP
  have hmem := ae_mem_support_toMeasure P
  refine MeasureTheory.Integrable.of_bound
    (MeasureTheory.measurable_llr _ _).aestronglyMeasurable ε ?_
  filter_upwards [hllr, hmem] with w hw hsup
  have hPw : P w ≠ 0 := (PMF.mem_support_iff _ _).mp hsup
  rw [hw, Real.norm_eq_abs]
  exact abs_privacyLoss_le_of_dp_two_sided P Q ε w hε hPQ hQP hPw

/-- The `llr` integral against `P.toMeasure` is the loss expectation. -/
private theorem integral_llr_toMeasure_eq_privacyLossExpectation {Ω : Type*} [Countable Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (P Q : PMF Ω) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    ∫ w, MeasureTheory.llr P.toMeasure Q.toMeasure w ∂P.toMeasure
      = privacyLossExpectation P Q := by
  have hllr := llr_toMeasure_ae_eq_privacyLoss P Q ε hPQ hQP
  have hint := integrable_llr_toMeasure P Q ε hε hPQ hQP
  rw [MeasureTheory.integral_congr_ae hllr, PMF.integral_eq_tsum P _ (hint.congr hllr)]
  apply tsum_congr
  intro w
  rw [smul_eq_mul]

/-- Agreement: under two-sided DP bounds, `klDiv` on the PMF measures is the
`ENNReal` cast of the loss expectation. -/
theorem klDiv_toMeasure_eq_ofReal_privacyLossExpectation {Ω : Type*} [Countable Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (P Q : PMF Ω) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    InformationTheory.klDiv P.toMeasure Q.toMeasure
      = ENNReal.ofReal (privacyLossExpectation P Q) := by
  have hac := toMeasure_ac_of_dp_two_sided P Q ε hPQ hQP
  have hint := integrable_llr_toMeasure P Q ε hε hPQ hQP
  have hval := integral_llr_toMeasure_eq_privacyLossExpectation P Q ε hε hPQ hQP
  rw [InformationTheory.klDiv_of_ac_of_integrable hac hint, hval,
    MeasureTheory.probReal_univ, MeasureTheory.probReal_univ]
  congr 1
  ring

/-- The `klDiv` upper bound from two-sided DP bounds
(discrete Dwork-Roth Lemma 3.18). -/
theorem klDiv_toMeasure_le_of_dp_two_sided {Ω : Type*} [Countable Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (P Q : PMF Ω) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    InformationTheory.klDiv P.toMeasure Q.toMeasure
      ≤ ENNReal.ofReal (ε * (Real.exp ε - 1)) := by
  rw [klDiv_toMeasure_eq_ofReal_privacyLossExpectation P Q ε hε hPQ hQP]
  apply ENNReal.ofReal_le_ofReal
  exact privacyLossExpectation_le_of_dp_two_sided P Q ε hε hPQ hQP

/-- The real value of `klDiv` is the loss expectation under two-sided bounds. -/
theorem toReal_klDiv_toMeasure_eq_privacyLossExpectation {Ω : Type*} [Countable Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (P Q : PMF Ω) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    (InformationTheory.klDiv P.toMeasure Q.toMeasure).toReal
      = privacyLossExpectation P Q := by
  rw [klDiv_toMeasure_eq_ofReal_privacyLossExpectation P Q ε hε hPQ hQP,
    ENNReal.toReal_ofReal
      (privacyLossExpectation_nonneg P Q ε hε hPQ hQP)]

/-- A non-absolute-continuity witness gives infinite `klDiv`: if `P` charges
`a` and `Q` does not, `P.toMeasure` is not absolutely continuous with respect
to `Q.toMeasure`. -/
theorem klDiv_toMeasure_eq_top_of_not_ac_witness {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P Q : PMF Ω) (a : Ω) (hP : P a ≠ 0) (hQ : Q a = 0) :
    InformationTheory.klDiv P.toMeasure Q.toMeasure = ∞ := by
  apply InformationTheory.klDiv_of_not_ac
  intro hac
  have h1 : Q.toMeasure {a} = 0 := by
    rw [Q.toMeasure_apply_singleton _ (MeasurableSet.singleton a), hQ]
  have h2 := hac h1
  rw [P.toMeasure_apply_singleton _ (MeasurableSet.singleton a)] at h2
  exact hP h2

/-- Mechanism `klDiv` upper bound when adjacency holds both ways. -/
theorem klDiv_toMeasure_le_of_isDP {Database Output : Type*} [Countable Output]
    [MeasurableSpace Output] [MeasurableSingletonClass Output]
    (M : Database → PMF Output)
    (adj : Database → Database → Prop) (ε : ℝ) (d d₂ : Database)
    (hM : IsDP M adj ε) (hadj : adj d d₂) (hadj_symm : adj d₂ d) :
    InformationTheory.klDiv (M d).toMeasure (M d₂).toMeasure
      ≤ ENNReal.ofReal (ε * (Real.exp ε - 1)) :=
  klDiv_toMeasure_le_of_dp_two_sided (M d) (M d₂) ε hM.1
    (fun o => hM.2 d d₂ hadj o) (fun o => hM.2 d₂ d hadj_symm o)

end CSLibExt.Privacy.DifferentialPrivacy
