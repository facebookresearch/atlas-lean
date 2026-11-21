/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DifferentialPrivacy
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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
`log (P w / Q w)` on real-valued masses, and `klPMF P Q` is the
`P`-expectation of the loss. Under two-sided pointwise bounds
`P w ≤ e^ε * Q w` and `Q w ≤ e^ε * P w`, the loss is bounded by `ε` on
the common support, `klPMF` is nonnegative (Gibbs), and
`klPMF P Q ≤ ε * (e^ε - 1)`.

This is the discrete case of Dwork and Roth, *The Algorithmic
Foundations of Differential Privacy* (2014), Lemma 3.18: a two-sided
`D∞ ≤ ε` bound implies `KL ≤ ε * (e^ε - 1)`.

Not covered here: no bridge to Mathlib's measure-theoretic `klDiv`,
and no `(ε, δ)` approximate-DP variant.
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

/-- Privacy loss of outcome `w`: `log` of the ratio of real-valued masses. -/
noncomputable def privacyLoss {Ω : Type*} (P Q : PMF Ω) (w : Ω) : ℝ :=
  Real.log ((P w).toReal / (Q w).toReal)

/-- Discrete KL divergence: the `P`-expectation of `privacyLoss`.
Support mismatch is excluded by hypotheses: the theorems below assume
two-sided pointwise DP bounds, which force common support. -/
noncomputable def klPMF {Ω : Type*} (P Q : PMF Ω) : ℝ :=
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

/-- KL summands are bounded by `ε * P w`, hence summable. Apply twice
for the symmetric term before combining series. -/
theorem summable_klTerm_of_dp_two_sided {Ω : Type*} (P Q : PMF Ω) (ε : ℝ)
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

/-- The Gibbs comparison term is the negated KL summand. -/
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

/-- Gibbs inequality: `klPMF` is nonnegative under two-sided bounds. -/
theorem klPMF_nonneg {Ω : Type*} (P Q : PMF Ω) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    0 ≤ klPMF P Q := by
  have ht : Summable fun w => (P w).toReal * privacyLoss P Q w :=
    summable_klTerm_of_dp_two_sided P Q ε hε hPQ hQP
  have hu : Summable fun w => (P w).toReal * Real.log ((Q w).toReal / (P w).toReal) :=
    (summable_congr (fun w => gibbs_term_eq_neg P Q ε w hPQ hQP)).mpr ht.neg
  have hv : Summable fun w => (P w).toReal * ((Q w).toReal / (P w).toReal - 1) :=
    (summable_congr (fun w => gibbs_rhs_eq P Q ε w hPQ hQP)).mpr
      ((summable_toReal_apply Q).sub (summable_toReal_apply P))
  have hsum : ∑' w, (P w).toReal * Real.log ((Q w).toReal / (P w).toReal) =
      -klPMF P Q := by
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

/-- Adding KL summands in both directions symmetrizes to `(p - q) * L`. -/
private theorem add_klTerm_eq {Ω : Type*} (P Q : PMF Ω) (ε : ℝ) (w : Ω)
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

/-- KL upper bound from two-sided DP bounds (discrete Dwork-Roth Lemma 3.18):
`klPMF P Q ≤ ε * (e^ε - 1)`. -/
theorem klPMF_le_of_dp_two_sided {Ω : Type*} (P Q : PMF Ω) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hPQ : ∀ w, P w ≤ ENNReal.ofReal (Real.exp ε) * Q w)
    (hQP : ∀ w, Q w ≤ ENNReal.ofReal (Real.exp ε) * P w) :
    klPMF P Q ≤ ε * (Real.exp ε - 1) := by
  have htP := summable_klTerm_of_dp_two_sided P Q ε hε hPQ hQP
  have htQ := summable_klTerm_of_dp_two_sided Q P ε hε hQP hPQ
  have hnonnegQ := klPMF_nonneg Q P ε hε hQP hPQ
  have hs : Summable fun w => ((P w).toReal - (Q w).toReal) * privacyLoss P Q w :=
    (summable_congr (fun w => (add_klTerm_eq P Q ε w hPQ hQP).symm)).mpr
      (htP.add htQ)
  have hadd : ∑' w, ((P w).toReal - (Q w).toReal) * privacyLoss P Q w =
      klPMF P Q + klPMF Q P := by
    rw [tsum_congr (fun w => (add_klTerm_eq P Q ε w hPQ hQP).symm)]
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
  calc klPMF P Q ≤ klPMF P Q + klPMF Q P := le_add_of_nonneg_right hnonnegQ
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

/-- Mechanism KL is nonnegative when adjacency holds both ways. -/
theorem klPMF_nonneg_of_isDP {Database Output : Type*} (M : Database → PMF Output)
    (adj : Database → Database → Prop) (ε : ℝ) (d d₂ : Database)
    (hM : IsDP M adj ε) (hadj : adj d d₂) (hadj_symm : adj d₂ d) :
    0 ≤ klPMF (M d) (M d₂) :=
  klPMF_nonneg (M d) (M d₂) ε hM.1 (fun o => hM.2 d d₂ hadj o)
    (fun o => hM.2 d₂ d hadj_symm o)

/-- Mechanism KL upper bound when adjacency holds both ways. -/
theorem klPMF_le_of_isDP {Database Output : Type*} (M : Database → PMF Output)
    (adj : Database → Database → Prop) (ε : ℝ) (d d₂ : Database)
    (hM : IsDP M adj ε) (hadj : adj d d₂) (hadj_symm : adj d₂ d) :
    klPMF (M d) (M d₂) ≤ ε * (Real.exp ε - 1) :=
  klPMF_le_of_dp_two_sided (M d) (M d₂) ε hM.1 (fun o => hM.2 d d₂ hadj o)
    (fun o => hM.2 d₂ d hadj_symm o)

end CSLibExt.Privacy.DifferentialPrivacy
