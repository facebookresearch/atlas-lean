/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.CommonCovarianceLikelihood
public import MathlibExt.LinearAlgebra.Matrix.MatchedSNRQuotient
public import MathlibExt.Probability.Decision.BinaryCostAdapter

/-!
# Gaussian matched-filter decision rule

## i. Overview

For two multivariate Gaussian laws with a common positive definite
covariance `R` and means `s0` and `s1`, the log-likelihood ratio is
affine in the observation: it is the matched statistic
`(s1 - s0)ᵀ R⁻¹ y` minus half the whitened energy gap
`(s1ᵀ R⁻¹ s1 - s0ᵀ R⁻¹ s0) / 2`. Combining that ratio with a finite
binary cost matrix gives an explicit threshold test: decide `true`
when the statistic exceeds a threshold consisting of the log
prior-cost ratio plus half the energy gap, decide the declared tie
value on equality, and decide `false` below the threshold. This
module proves that this threshold rule is exactly the finite-cost
Bayes rule applied to the two Gaussian densities, that it minimizes
the original-cost Bayes risk over all Markov decision kernels, and
that the underlying statistic is the output of the matched weight
`R⁻¹ (s1 - s0)`, which attains and maximizes the deterministic
matched-filter signal-to-noise quotient. Equal means are handled
separately: the matched weight vanishes and the rule reduces to a
prior-cost comparison that ignores the observation.

## ii. Key results

- `binaryCostRule_gaussian_eq_matchedFilterRule`: the finite-cost
  Bayes rule on the two Gaussian densities is, pointwise and
  including the tie branch, the explicit matched-filter threshold
  rule.
- `matchedFilterRule_minimizes_binaryCostAvgRisk`: the threshold
  rule is Bayes optimal for the original costs over all Markov
  decision kernels.
- `matchedStatistic_eq_dotProduct_matchedWeight`: the statistic is
  the output of the matched weight `R⁻¹ (s1 - s0)`.
- `matchedSNR_matchedWeight`,
  `matchedSNR_le_matchedSNR_matchedWeight`, and
  `matchedSNR_eq_matchedSNR_matchedWeight_iff`: the matched weight
  attains the whitened energy, maximizes the matched
  signal-to-noise quotient, and is unique up to nonzero scaling.
- `matchedWeight_eq_zero_iff` and `matchedFilterRule_of_eq`: the
  equal-means case, where there is no signal-to-noise direction and
  the decision is prior-cost only.

## iii. Table of contents

- A. Matched statistic, threshold, and rule
- B. The threshold rule on Gaussian densities
- C. Bayes optimality
- D. The statistic and the matched-SNR direction
- E. Equal means
- F. Validation

## iv. References

- H. L. Van Trees, *Detection, Estimation, and Modulation Theory,
  Part I: Detection, Estimation, and Linear Modulation Theory*,
  Wiley, 1968 (reprinted 2001): matched filters, likelihood-ratio
  tests, and Bayes decision rules for Gaussian observations.
- S. M. Kay, *Fundamentals of Statistical Signal Processing,
  Volume I: Estimation Theory* and *Volume II: Detection Theory*,
  Prentice Hall, 1993/1998: matched-filter signal-to-noise ratio
  and minimum-probability-of-error and Bayes-cost detection.

## A. Matched statistic, threshold, and rule

The three definitions owned by this module: the statistic, the
finite-cost threshold, and the threshold rule with its tie branch.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal NNReal

namespace PhyslibExt.Instrumentation.GaussianMatchedDecision

open MathlibExt.Probability.Decision.BinaryCostAdapter
open MathlibExt.LinearAlgebra.Matrix.MatchedSNRQuotient

/-- The matched-filter statistic `(s1 - s0)ᵀ R⁻¹ y`. -/
noncomputable def matchedStatistic {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (y : EuclideanSpace ℝ ι) : ℝ :=
  ofLp (s1 - s0) ⬝ᵥ R⁻¹ *ᵥ ofLp y

/-- The finite-cost matched-filter threshold
`log (pi0 (C10 - C00) / (pi1 (C01 - C11))) + (s1ᵀ R⁻¹ s1 - s0ᵀ R⁻¹ s0) / 2`. -/
noncomputable def matchedThreshold {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (pi0 pi1 C00 C01 C10 C11 : ℝ) : ℝ :=
  Real.log (pi0 * (C10 - C00) / (pi1 * (C01 - C11))) +
    (ofLp s1 ⬝ᵥ R⁻¹ *ᵥ ofLp s1 - ofLp s0 ⬝ᵥ R⁻¹ *ᵥ ofLp s0) / 2

/-- The finite-cost Gaussian matched-filter test: decide `true` when the statistic exceeds the
threshold, the declared tie decision `tie` when they are equal, and `false` otherwise. -/
noncomputable def matchedFilterRule {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (pi0 pi1 C00 C01 C10 C11 : ℝ) (tie : Bool)
    (y : EuclideanSpace ℝ ι) : Bool :=
  if matchedThreshold s1 s0 R pi0 pi1 C00 C01 C10 C11 < matchedStatistic s1 s0 R y then true
  else if matchedStatistic s1 s0 R y = matchedThreshold s1 s0 R pi0 pi1 C00 C01 C10 C11 then tie
  else false

/-! ## B. The threshold rule on Gaussian densities -/

/-- Positivity of the Gaussian density for positive definite covariance. -/
private lemma pdf_pos {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef)
    (y : EuclideanSpace ℝ ι) :
    0 < MetaMathlibExt.multivariateGaussianPDFReal s R y := by
  unfold MetaMathlibExt.multivariateGaussianPDFReal
  have h1 : 0 < √(2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < √R.det := Real.sqrt_pos.2 hR.det_pos
  positivity

/-- Measurability of the Gaussian density. -/
private lemma pdf_measurable {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) :
    Measurable (fun x => MetaMathlibExt.multivariateGaussianPDFReal s R x) := by
  unfold MetaMathlibExt.multivariateGaussianPDFReal
  fun_prop

/-- The signal difference is nonzero as a function when the means differ. -/
private lemma ofLp_sub_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (hs : s1 ≠ s0) : ofLp (s1 - s0) ≠ 0 := by
  intro h
  rw [WithLp.ofLp_eq_zero] at h
  exact hs (sub_eq_zero.mp h)

/-- **Decide 1 iff the matched statistic exceeds the threshold.** For positive definite `R`,
positive priors and costs with `C00 < C10`, `C11 < C01`, the finite-cost Bayes rule of the
adapter applied to the Gaussian densities of `N(s0, R)` and `N(s1, R)` is, at every observation
and including the tie branch, the explicit matched-filter threshold rule. -/
theorem binaryCostRule_gaussian_eq_matchedFilterRule {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef) (pi0 pi1 : ℝ)
    (hpi0 : 0 < pi0) (hpi1 : 0 < pi1) (C00 C01 C10 C11 : ℝ) (hC0 : C00 < C10) (hC1 : C11 < C01)
    (tie : Bool) (y : EuclideanSpace ℝ ι) :
    binaryCostRule pi0 pi1 C00 C01 C10 C11 (MetaMathlibExt.multivariateGaussianPDFReal s0 R)
        (MetaMathlibExt.multivariateGaussianPDFReal s1 R) tie y =
      matchedFilterRule s1 s0 R pi0 pi1 C00 C01 C10 C11 tie y := by
  unfold binaryCostRule matchedFilterRule
  set A : ℝ := pi0 * (C10 - C00) with hA
  set B : ℝ := pi1 * (C01 - C11) with hB
  have hApos : 0 < A := mul_pos hpi0 (sub_pos.mpr hC0)
  have hBpos : 0 < B := mul_pos hpi1 (sub_pos.mpr hC1)
  have hp0 : 0 < MetaMathlibExt.multivariateGaussianPDFReal s0 R y := pdf_pos s0 R hR y
  have hp1 : 0 < MetaMathlibExt.multivariateGaussianPDFReal s1 R y := pdf_pos s1 R hR y
  have hratio :
      MetaMathlibExt.multivariateGaussianPDFReal s1 R y /
          MetaMathlibExt.multivariateGaussianPDFReal s0 R y =
        Real.exp (MathlibExt.Probability.Distributions.CommonCovarianceLikelihood.commonCovarianceLogLR
          s1 s0 R y) :=
    MathlibExt.Probability.Distributions.CommonCovarianceLikelihood.multivariateGaussianPDFReal_div_eq_exp
      s1 s0 R hR y
  have hp1eq : MetaMathlibExt.multivariateGaussianPDFReal s1 R y =
      Real.exp (MathlibExt.Probability.Distributions.CommonCovarianceLikelihood.commonCovarianceLogLR
        s1 s0 R y) * MetaMathlibExt.multivariateGaussianPDFReal s0 R y :=
    (div_eq_iff (ne_of_gt hp0)).mp hratio
  have hLR : MathlibExt.Probability.Distributions.CommonCovarianceLikelihood.commonCovarianceLogLR
        s1 s0 R y =
      matchedStatistic s1 s0 R y -
        (ofLp s1 ⬝ᵥ R⁻¹ *ᵥ ofLp s1 - ofLp s0 ⬝ᵥ R⁻¹ *ᵥ ofLp s0) / 2 := rfl
  have hthr : matchedThreshold s1 s0 R pi0 pi1 C00 C01 C10 C11 =
      Real.log (A / B) +
        (ofLp s1 ⬝ᵥ R⁻¹ *ᵥ ofLp s1 - ofLp s0 ⬝ᵥ R⁻¹ *ᵥ ofLp s0) / 2 := rfl
  have hABpos : 0 < A / B := div_pos hApos hBpos
  have hlt : (A * MetaMathlibExt.multivariateGaussianPDFReal s0 R y <
      B * MetaMathlibExt.multivariateGaussianPDFReal s1 R y) ↔
      matchedThreshold s1 s0 R pi0 pi1 C00 C01 C10 C11 <
        matchedStatistic s1 s0 R y := by
    rw [hp1eq, ← mul_assoc, mul_lt_mul_iff_of_pos_right hp0, mul_comm B, ← div_lt_iff₀ hBpos,
      ← Real.log_lt_iff_lt_exp hABpos, hthr, hLR]
    constructor <;> intro h <;> linarith [h]
  have heq : (B * MetaMathlibExt.multivariateGaussianPDFReal s1 R y =
      A * MetaMathlibExt.multivariateGaussianPDFReal s0 R y) ↔
      matchedStatistic s1 s0 R y =
        matchedThreshold s1 s0 R pi0 pi1 C00 C01 C10 C11 := by
    rw [hp1eq, ← mul_assoc, mul_eq_mul_right_iff, or_iff_left (ne_of_gt hp0)]
    have h1 : (B * Real.exp (MathlibExt.Probability.Distributions.CommonCovarianceLikelihood.commonCovarianceLogLR
          s1 s0 R y) = A) ↔
        Real.exp (MathlibExt.Probability.Distributions.CommonCovarianceLikelihood.commonCovarianceLogLR
          s1 s0 R y) = A / B := by
      rw [eq_div_iff (ne_of_gt hBpos), mul_comm]
    rw [h1]
    constructor
    · intro h
      have hlog : MathlibExt.Probability.Distributions.CommonCovarianceLikelihood.commonCovarianceLogLR
            s1 s0 R y = Real.log (A / B) := by
        rw [← h, Real.log_exp]
      linarith [hlog, hthr, hLR]
    · intro h
      have hlog : MathlibExt.Probability.Distributions.CommonCovarianceLikelihood.commonCovarianceLogLR
            s1 s0 R y = Real.log (A / B) := by
        linarith [h, hthr, hLR]
      rw [hlog, Real.exp_log hABpos]
  by_cases h1c : A * MetaMathlibExt.multivariateGaussianPDFReal s0 R y <
      B * MetaMathlibExt.multivariateGaussianPDFReal s1 R y
  · rw [ite_eq_left h1c, ite_eq_left (hlt.mp h1c)]
  · rw [ite_eq_right h1c, ite_eq_right (fun h => h1c (hlt.mpr h))]
    by_cases h2c : B * MetaMathlibExt.multivariateGaussianPDFReal s1 R y =
        A * MetaMathlibExt.multivariateGaussianPDFReal s0 R y
    · rw [ite_eq_left h2c, ite_eq_left (heq.mp h2c)]
    · rw [ite_eq_right h2c, ite_eq_right (fun h => h2c (heq.mpr h))]

/-! ## C. Bayes optimality -/

/-- **Finite-cost Gaussian matched-filter test is Bayes optimal (headline).** For laws
`N(s0, R)` (truth `0`) and `N(s1, R)` (truth `1`) with common positive definite covariance `R`,
positive priors summing to one and costs with `C00 < C10`, `C11 < C01`, the matched-filter
threshold rule is measurable and its deterministic decision kernel has original-cost Bayes risk
at most that of every Markov decision kernel. -/
theorem matchedFilterRule_minimizes_binaryCostAvgRisk {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef) (pi0 pi1 : ℝ)
    (hpi0 : 0 < pi0) (hpi1 : 0 < pi1) (hpi : pi0 + pi1 = 1) (C00 C01 C10 C11 : ℝ)
    (hC0 : C00 < C10) (hC1 : C11 < C01) (tie : Bool) :
    ∃ hf : Measurable (matchedFilterRule s1 s0 R pi0 pi1 C00 C01 C10 C11 tie),
      ∀ κ : Kernel (EuclideanSpace ℝ ι) Bool, IsMarkovKernel κ →
        binaryCostAvgRisk C00 C01 C10 C11
            (Kernel.boolKernel (multivariateGaussian s0 R) (multivariateGaussian s1 R))
            (Kernel.deterministic _ hf) pi0 pi1 ≤
          binaryCostAvgRisk C00 C01 C10 C11
            (Kernel.boolKernel (multivariateGaussian s0 R) (multivariateGaussian s1 R)) κ
            pi0 pi1 := by
  have hfun : matchedFilterRule s1 s0 R pi0 pi1 C00 C01 C10 C11 tie =
      binaryCostRule pi0 pi1 C00 C01 C10 C11
        (MetaMathlibExt.multivariateGaussianPDFReal s0 R)
        (MetaMathlibExt.multivariateGaussianPDFReal s1 R) tie := by
    funext y
    exact (binaryCostRule_gaussian_eq_matchedFilterRule s1 s0 R hR pi0 pi1 hpi0 hpi1
      C00 C01 C10 C11 hC0 hC1 tie y).symm
  obtain ⟨hf, hmin⟩ := binaryCostRule_minimizes_binaryCostAvgRisk volume
    (multivariateGaussian s0 R) (multivariateGaussian s1 R)
    (MetaMathlibExt.multivariateGaussianPDFReal s0 R)
    (MetaMathlibExt.multivariateGaussianPDFReal s1 R) (pdf_measurable s0 R)
    (pdf_measurable s1 R) (fun x => (pdf_pos s0 R hR x).le)
    (fun x => (pdf_pos s1 R hR x).le)
    (MetaMathlibExt.multivariateGaussian_eq_withDensity s0 hR)
    (MetaMathlibExt.multivariateGaussian_eq_withDensity s1 hR) pi0 pi1 hpi0 hpi1 hpi
    C00 C01 C10 C11 hC0 hC1 tie
  have hf2 : Measurable (matchedFilterRule s1 s0 R pi0 pi1 C00 C01 C10 C11 tie) := by
    rw [hfun]; exact hf
  refine ⟨hf2, fun κ hκ => ?_⟩
  have hker := Kernel.deterministic_congr hfun (hf := hf2)
  rw [hker]
  exact hmin κ hκ

/-! ## D. The statistic and the matched-SNR direction -/

/-- **The statistic is the whitened matched-filter output.** For positive definite `R`,
`(s1 - s0)ᵀ R⁻¹ y = wᵀ y` with the matched weight `w = R⁻¹ (s1 - s0)`. -/
lemma matchedStatistic_eq_dotProduct_matchedWeight {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef) (y : EuclideanSpace ℝ ι) :
    matchedStatistic s1 s0 R y = (R⁻¹ *ᵥ ofLp (s1 - s0)) ⬝ᵥ ofLp y := by
  have hT : (R⁻¹)ᵀ = R⁻¹ := hR.inv.isHermitian.isSymm
  have hsym : ∀ u v : ι → ℝ, u ⬝ᵥ R⁻¹ *ᵥ v = v ⬝ᵥ R⁻¹ *ᵥ u := fun u v => by
    conv_lhs => rw [← hT]
    exact Matrix.dotProduct_transpose_mulVec _ _ _
  unfold matchedStatistic
  rw [hsym, dotProduct_comm]

/-- **The matched weight attains the whitened energy.** For positive definite `R` and
`s1 ≠ s0`, the deterministic matched-filter SNR of the signal difference `d = s1 - s0` at the
weight `R⁻¹ d` is `dᵀ R⁻¹ d`. -/
lemma matchedSNR_matchedWeight {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef) (hs : s1 ≠ s0) :
    matchedSNR R (ofLp (s1 - s0)) (R⁻¹ *ᵥ ofLp (s1 - s0)) =
      ofLp (s1 - s0) ⬝ᵥ R⁻¹ *ᵥ ofLp (s1 - s0) := by
  have h := matchedSNR_inv_mulVec_smul R hR (ofLp (s1 - s0)) (ofLp_sub_ne_zero s1 s0 hs)
    (1 : ℝ) one_ne_zero
  simpa using h

/-- **The matched weight maximizes the SNR.** For positive definite `R` and `s1 ≠ s0`, every
nonzero weight has SNR for the difference `d = s1 - s0` at most that of `R⁻¹ d`. -/
lemma matchedSNR_le_matchedSNR_matchedWeight {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef) (hs : s1 ≠ s0)
    (w : ι → ℝ) (hw : w ≠ 0) :
    matchedSNR R (ofLp (s1 - s0)) w ≤
      matchedSNR R (ofLp (s1 - s0)) (R⁻¹ *ᵥ ofLp (s1 - s0)) := by
  rw [matchedSNR_matchedWeight s1 s0 R hR hs]
  exact matchedSNR_le_dotProduct_inv_mulVec R hR (ofLp (s1 - s0)) w
    (ofLp_sub_ne_zero s1 s0 hs) hw

/-- **The matched-SNR direction.** For positive definite `R` and `s1 ≠ s0`, a nonzero weight
attains the SNR of the statistic's weight `R⁻¹ (s1 - s0)` exactly when it is a nonzero multiple
of that weight. -/
lemma matchedSNR_eq_matchedSNR_matchedWeight_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef) (hs : s1 ≠ s0)
    (w : ι → ℝ) (hw : w ≠ 0) :
    matchedSNR R (ofLp (s1 - s0)) w =
        matchedSNR R (ofLp (s1 - s0)) (R⁻¹ *ᵥ ofLp (s1 - s0)) ↔
      ∃ c : ℝ, c ≠ 0 ∧ w = c • R⁻¹ *ᵥ ofLp (s1 - s0) := by
  rw [matchedSNR_matchedWeight s1 s0 R hR hs]
  exact matchedSNR_eq_dotProduct_inv_mulVec_iff R hR (ofLp (s1 - s0)) w
    (ofLp_sub_ne_zero s1 s0 hs) hw

/-! ## E. Equal means -/

/-- **Equal means give no SNR direction.** For positive definite `R`, the matched weight
`R⁻¹ (s1 - s0)` vanishes exactly when the means are equal. -/
lemma matchedWeight_eq_zero_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef) :
    R⁻¹ *ᵥ ofLp (s1 - s0) = 0 ↔ s1 = s0 := by
  constructor
  · intro h
    have hU : IsUnit R.det := isUnit_iff_ne_zero.mpr (ne_of_gt hR.det_pos)
    have hcancel : R *ᵥ (R⁻¹ *ᵥ ofLp (s1 - s0)) = ofLp (s1 - s0) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv R hU, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_zero] at hcancel
    have h0 : ofLp (s1 - s0) = ofLp (0 : EuclideanSpace ℝ ι) := by
      rw [← hcancel]; simp
    exact sub_eq_zero.mp (WithLp.ofLp_injective 2 h0)
  · intro h
    rw [h, sub_self, WithLp.ofLp_zero, Matrix.mulVec_zero]

/-- **Equal means: a prior/cost-only decision.** With `s1 = s0`, positive priors and costs with
`C00 < C10`, `C11 < C01`, the rule ignores the observation: it decides `true` iff
`pi0 (C10 - C00) < pi1 (C01 - C11)`, `tie` on equality, `false` otherwise. -/
lemma matchedFilterRule_of_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (pi0 pi1 : ℝ) (hpi0 : 0 < pi0) (hpi1 : 0 < pi1)
    (C00 C01 C10 C11 : ℝ) (hC0 : C00 < C10) (hC1 : C11 < C01) (tie : Bool)
    (y : EuclideanSpace ℝ ι) :
    matchedFilterRule s s R pi0 pi1 C00 C01 C10 C11 tie y =
      if pi0 * (C10 - C00) < pi1 * (C01 - C11) then true
      else if pi1 * (C01 - C11) = pi0 * (C10 - C00) then tie
      else false := by
  have hA : (0:ℝ) < pi0 * (C10 - C00) := mul_pos hpi0 (sub_pos.mpr hC0)
  have hB : (0:ℝ) < pi1 * (C01 - C11) := mul_pos hpi1 (sub_pos.mpr hC1)
  have hAB : (0:ℝ) < pi0 * (C10 - C00) / (pi1 * (C01 - C11)) := div_pos hA hB
  have hstat : matchedStatistic s s R y = 0 := by
    simp only [matchedStatistic, sub_self, WithLp.ofLp_zero, zero_dotProduct]
  have hthr : matchedThreshold s s R pi0 pi1 C00 C01 C10 C11 =
      Real.log (pi0 * (C10 - C00) / (pi1 * (C01 - C11))) := by
    simp only [matchedThreshold]
    rw [sub_self, zero_div, add_zero]
  have hlt : Real.log (pi0 * (C10 - C00) / (pi1 * (C01 - C11))) < 0 ↔
      pi0 * (C10 - C00) < pi1 * (C01 - C11) := by
    have hlog1 : Real.log (1:ℝ) = 0 := Real.log_one
    rw [← hlog1]
    constructor
    · intro h
      have h' := (Real.log_lt_log_iff hAB (by norm_num : (0:ℝ) < 1)).mp h
      have h'' := (div_lt_iff₀ hB).mp h'
      linarith
    · intro h
      apply (Real.log_lt_log_iff hAB (by norm_num : (0:ℝ) < 1)).mpr
      apply (div_lt_iff₀ hB).mpr
      linarith
  have heq : (0:ℝ) = Real.log (pi0 * (C10 - C00) / (pi1 * (C01 - C11))) ↔
      pi1 * (C01 - C11) = pi0 * (C10 - C00) := by
    constructor
    · intro h
      have hlog : Real.log (pi0 * (C10 - C00) / (pi1 * (C01 - C11))) = Real.log 1 := by
        rw [← h, Real.log_one]
      have hexp := congrArg Real.exp hlog
      rw [Real.exp_log hAB, Real.exp_log (by norm_num : (0:ℝ) < 1)] at hexp
      have hdiv := (div_eq_iff (ne_of_gt hB)).mp hexp
      linarith
    · intro h
      have h1 : pi0 * (C10 - C00) / (pi1 * (C01 - C11)) = 1 :=
        (div_eq_iff (ne_of_gt hB)).mpr (by linarith)
      have hlog : Real.log (pi0 * (C10 - C00) / (pi1 * (C01 - C11))) = 0 := by
        rw [h1, Real.log_one]
      exact hlog.symm
  simp only [matchedFilterRule]
  rw [hstat, hthr]
  by_cases h1c : Real.log (pi0 * (C10 - C00) / (pi1 * (C01 - C11))) < 0
  · rw [ite_eq_left h1c, ite_eq_left (hlt.mp h1c)]
  · rw [ite_eq_right h1c, ite_eq_right (fun h => h1c (hlt.mpr h))]
    by_cases h2c : (0:ℝ) = Real.log (pi0 * (C10 - C00) / (pi1 * (C01 - C11)))
    · rw [ite_eq_left h2c, ite_eq_left (heq.mp h2c)]
    · rw [ite_eq_right h2c, ite_eq_right (fun h => h2c (heq.mpr h))]

/-! ## F. Validation -/

/-- Upper bound for the `n = 1` threshold logarithm. -/
private lemma log_two_ninths_lt : Real.log (2 / 9 : ℝ) < -1 / 2 := by
  have hexp : (2 / 9 : ℝ) < Real.exp (-1 / 2) := by
    have h := Real.add_one_le_exp (-1 / 2 : ℝ)
    linarith
  have hpos1 : (0:ℝ) < 2 / 9 := by norm_num
  have hpos2 : (0:ℝ) < Real.exp (-1 / 2) := Real.exp_pos _
  have h := (Real.log_lt_log_iff hpos1 hpos2).mpr hexp
  rw [Real.log_exp] at h
  exact h

/-- Lower bound for the `n = 1` threshold logarithm. -/
private lemma log_two_ninths_gt : (-5 / 2 : ℝ) < Real.log (2 / 9 : ℝ) := by
  have e1 : (2:ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1:ℝ)
    linarith
  have e12 : (3/2:ℝ) ≤ Real.exp (1/2) := by
    have h := Real.add_one_le_exp (1/2:ℝ)
    linarith
  have h5 : Real.exp (5/2:ℝ) = Real.exp 1 * Real.exp 1 * Real.exp (1/2) := by
    have h : (5/2:ℝ) = 1 + 1 + 1/2 := by norm_num
    rw [h, Real.exp_add, Real.exp_add]
  have p1 : (0:ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have p12 : (0:ℝ) ≤ Real.exp (1/2) := (Real.exp_pos _).le
  have m1 : (2:ℝ) * 2 ≤ Real.exp 1 * Real.exp 1 :=
    (mul_le_mul_of_nonneg_left e1 (by norm_num)).trans
      (mul_le_mul_of_nonneg_right e1 p1)
  have m2 : (2:ℝ) * 2 * (3/2) ≤ Real.exp 1 * Real.exp 1 * Real.exp (1/2) :=
    (mul_le_mul_of_nonneg_right m1 (by norm_num)).trans
      (mul_le_mul_of_nonneg_left e12 (mul_nonneg p1 p1))
  have hexp : (9/2 : ℝ) < Real.exp (5/2) := by
    rw [h5]
    linarith [m2]
  have hexp_neg : Real.exp (-5/2) = 1 / Real.exp (5/2) := by
    have hneg : (-5/2 : ℝ) = -(5/2) := by norm_num
    rw [hneg, Real.exp_neg, one_div]
  have hlt : Real.exp (-5/2) < (2/9 : ℝ) := by
    rw [hexp_neg, div_lt_iff₀ (Real.exp_pos (5/2))]
    linarith [hexp]
  have hpos1 : (0:ℝ) < 2 / 9 := by norm_num
  have hpos2 : (0:ℝ) < Real.exp (-5/2) := Real.exp_pos _
  have h := (Real.log_lt_log_iff hpos2 hpos1).mpr hlt
  rw [Real.log_exp] at h
  exact h

/-- Lower bound for the flipped `n = 1` threshold logarithm. -/
private lemma log_four_thirds_gt : (-1/2 : ℝ) < Real.log (4/3 : ℝ) := by
  have hexp : Real.exp (-1/2) < (4/3 : ℝ) := by
    have h1 : Real.exp (-1/2) < Real.exp (0:ℝ) := Real.exp_lt_exp.mpr (by norm_num)
    rw [Real.exp_zero] at h1
    linarith
  have hpos1 : (0:ℝ) < 4/3 := by norm_num
  have hpos2 : (0:ℝ) < Real.exp (-1/2) := Real.exp_pos _
  have h := (Real.log_lt_log_iff hpos2 hpos1).mpr hexp
  rw [Real.log_exp] at h
  exact h

/-- Inverse of the `n = 1` fixture covariance. -/
private lemma fin_one_inv : !![(1:ℝ)]⁻¹ = !![(1:ℝ)] := by
  have hRS : !![(1:ℝ)] * !![(1:ℝ)] = 1 := by
    ext i j
    fin_cases i; fin_cases j;
      simp [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply]
  have hU : IsUnit !![(1:ℝ)].det := Matrix.isUnit_det_of_right_inverse hRS
  have hSR : !![(1:ℝ)]⁻¹ * !![(1:ℝ)] = 1 := by
    apply Matrix.nonsing_inv_mul
    exact hU
  exact left_inv_eq_right_inv hSR hRS

/-- Statistic of the `n = 1` fixture at `y = 0`. -/
private lemma fin_one_stat_zero :
    matchedStatistic (toLp 2 ![(1:ℝ)]) (toLp 2 ![0]) !![(1:ℝ)] (toLp 2 ![0]) = 0 := by
  simp only [matchedStatistic]
  rw [fin_one_inv]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_one, WithLp.ofLp_toLp, Pi.sub_apply]

/-- Statistic of the `n = 1` fixture at `y = -2`. -/
private lemma fin_one_stat_neg_two :
    matchedStatistic (toLp 2 ![(1:ℝ)]) (toLp 2 ![0]) !![(1:ℝ)] (toLp 2 ![-2]) = -2 := by
  simp only [matchedStatistic]
  rw [fin_one_inv]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_one, WithLp.ofLp_toLp, Pi.sub_apply]

/-- Signal energy of the `n = 1` fixture. -/
private lemma fin_one_energy_one :
    ofLp (toLp 2 ![(1:ℝ)]) ⬝ᵥ !![(1:ℝ)]⁻¹ *ᵥ ofLp (toLp 2 ![(1:ℝ)]) = 1 := by
  rw [fin_one_inv]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_one, WithLp.ofLp_toLp]

/-- Null energy of the `n = 1` fixture. -/
private lemma fin_one_energy_zero :
    ofLp (toLp 2 ![0]) ⬝ᵥ !![(1:ℝ)]⁻¹ *ᵥ ofLp (toLp 2 ![0]) = 0 := by
  rw [fin_one_inv]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_one, WithLp.ofLp_toLp]

/-- Threshold of the `n = 1` fixture. -/
private lemma fin_one_threshold :
    matchedThreshold (toLp 2 ![(1:ℝ)]) (toLp 2 ![0]) !![(1:ℝ)] (1 / 4) (3 / 4) 0 4 2 1 =
      Real.log (2 / 9) + 1 / 2 := by
  simp only [matchedThreshold]
  rw [fin_one_energy_one, fin_one_energy_zero]
  have harg : (1/4:ℝ) * (2 - 0) / ((3/4) * (4 - 1)) = 2 / 9 := by norm_num
  rw [harg]
  norm_num

/-- Threshold of the flipped `n = 1` fixture. -/
private lemma fin_one_threshold_flipped :
    matchedThreshold (toLp 2 ![(1:ℝ)]) (toLp 2 ![0]) !![(1:ℝ)] (1 / 4) (3 / 4) 0 2 4 1 =
      Real.log (4 / 3) + 1 / 2 := by
  simp only [matchedThreshold]
  rw [fin_one_energy_one, fin_one_energy_zero]
  have harg : (1/4:ℝ) * (4 - 0) / ((3/4) * (2 - 1)) = 4 / 3 := by norm_num
  rw [harg]
  norm_num

/-- **`n = 1`, unequal means, priors and costs.** `s0 = 0`, `s1 = 1`, `R = [1]`,
`pi0 = 1/4`, `pi1 = 3/4`, `C00 = 0`, `C01 = 4`, `C10 = 2`, `C11 = 1`: the statistic is `y` and the
threshold `log (2/9) + 1/2 ≈ -1.004`, so the rule decides `true` at `y = 0` and `false` at
`y = -2`. -/
lemma matchedFilterRule_fin_one_example (tie : Bool) :
    matchedFilterRule (toLp 2 ![(1 : ℝ)]) (toLp 2 ![0]) !![(1 : ℝ)] (1 / 4) (3 / 4) 0 4 2 1 tie
        (toLp 2 ![0]) = true ∧
      matchedFilterRule (toLp 2 ![(1 : ℝ)]) (toLp 2 ![0]) !![(1 : ℝ)] (1 / 4) (3 / 4) 0 4 2 1
        tie (toLp 2 ![-2]) = false := by
  constructor
  · simp only [matchedFilterRule]
    rw [fin_one_stat_zero, fin_one_threshold]
    have hlt : Real.log (2 / 9) + 1 / 2 < (0:ℝ) := by linarith [log_two_ninths_lt]
    rw [ite_eq_left hlt]
  · simp only [matchedFilterRule]
    rw [fin_one_stat_neg_two, fin_one_threshold]
    have hgt : (-2:ℝ) < Real.log (2 / 9) + 1 / 2 := by linarith [log_two_ninths_gt]
    rw [ite_eq_right (not_lt.mpr hgt.le), ite_eq_right (ne_of_lt hgt)]

/-- **Flipped cost index changes the threshold.** Transposing `C01` and `C10` in the `n = 1`
fixture (`C01 = 2`, `C10 = 4`, still `C00 < C10`, `C11 < C01`) moves the threshold from
`log (2/9) + 1/2` to `log (4/3) + 1/2`. -/
lemma matchedThreshold_fin_one_flipped_ne :
    matchedThreshold (toLp 2 ![(1 : ℝ)]) (toLp 2 ![0]) !![(1 : ℝ)] (1 / 4) (3 / 4) 0 2 4 1 ≠
      matchedThreshold (toLp 2 ![(1 : ℝ)]) (toLp 2 ![0]) !![(1 : ℝ)] (1 / 4) (3 / 4) 0 4 2 1 := by
  rw [fin_one_threshold_flipped, fin_one_threshold]
  intro hcon
  linarith [log_two_ninths_lt, log_four_thirds_gt]

/-- **Flipped cost index is rejected by the fixture.** At `y = 0` the transposed-cost rule
decides `false`, while the correct rule (`matchedFilterRule_fin_one_example`) decides `true`. -/
lemma matchedFilterRule_fin_one_flipped_example (tie : Bool) :
    matchedFilterRule (toLp 2 ![(1 : ℝ)]) (toLp 2 ![0]) !![(1 : ℝ)] (1 / 4) (3 / 4) 0 2 4 1 tie
      (toLp 2 ![0]) = false := by
  simp only [matchedFilterRule]
  rw [fin_one_stat_zero, fin_one_threshold_flipped]
  have hpos : (0:ℝ) < Real.log (4 / 3) + 1 / 2 := by linarith [log_four_thirds_gt]
  rw [ite_eq_right (not_lt.mpr hpos.le), ite_eq_right (ne_of_lt hpos)]

/-- Inverse of the `n = 2` fixture covariance. -/
private lemma fin_two_Rinv :
    !![(2:ℝ), 1; 1, 2]⁻¹ = !![(2/3:ℝ), -1/3; -1/3, 2/3] := by
  have hRS : !![(2:ℝ), 1; 1, 2] * !![(2/3:ℝ), -1/3; -1/3, 2/3] = 1 := by
    rw [Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hU : IsUnit !![(2:ℝ), 1; 1, 2].det := Matrix.isUnit_det_of_right_inverse hRS
  have hSR : !![(2:ℝ), 1; 1, 2]⁻¹ * !![(2:ℝ), 1; 1, 2] = 1 := by
    apply Matrix.nonsing_inv_mul
    exact hU
  exact left_inv_eq_right_inv hSR hRS

/-- Signal energy of the `n = 2` fixture. -/
private lemma fin_two_E1 :
    ofLp (toLp 2 ![(1:ℝ), 1]) ⬝ᵥ !![(2:ℝ), 1; 1, 2]⁻¹ *ᵥ ofLp (toLp 2 ![(1:ℝ), 1]) = 2/3 := by
  rw [fin_two_Rinv]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, WithLp.ofLp_toLp]
  norm_num

/-- Null energy of the `n = 2` fixture. -/
private lemma fin_two_E0 :
    ofLp (toLp 2 ![0, 0]) ⬝ᵥ !![(2:ℝ), 1; 1, 2]⁻¹ *ᵥ ofLp (toLp 2 ![0, 0]) = 0 := by
  rw [fin_two_Rinv]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, WithLp.ofLp_toLp]

/-- Threshold of the `n = 2` fixture. -/
private lemma fin_two_threshold :
    matchedThreshold (toLp 2 ![(1:ℝ), 1]) (toLp 2 ![0, 0]) !![(2:ℝ), 1; 1, 2] (1 / 2) (1 / 2)
      0 1 1 0 = 1/3 := by
  simp only [matchedThreshold]
  rw [fin_two_E1, fin_two_E0]
  have harg : (1/2:ℝ) * (1 - 0) / ((1/2) * (1 - 0)) = 1 := by norm_num
  rw [harg, Real.log_one]
  norm_num

/-- Statistic of the `n = 2` fixture at `(1, 1)`. -/
private lemma fin_two_stat_true :
    matchedStatistic (toLp 2 ![(1:ℝ), 1]) (toLp 2 ![0, 0]) !![(2:ℝ), 1; 1, 2]
      (toLp 2 ![1, 1]) = 2/3 := by
  simp only [matchedStatistic]
  rw [fin_two_Rinv]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, WithLp.ofLp_toLp, Pi.sub_apply]
  norm_num

/-- Statistic of the `n = 2` fixture at `(1, 0)`. -/
private lemma fin_two_stat_tie :
    matchedStatistic (toLp 2 ![(1:ℝ), 1]) (toLp 2 ![0, 0]) !![(2:ℝ), 1; 1, 2]
      (toLp 2 ![1, 0]) = 1/3 := by
  simp only [matchedStatistic]
  rw [fin_two_Rinv]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, WithLp.ofLp_toLp, Pi.sub_apply]
  norm_num

/-- Statistic of the `n = 2` fixture at `(0, 0)`. -/
private lemma fin_two_stat_false :
    matchedStatistic (toLp 2 ![(1:ℝ), 1]) (toLp 2 ![0, 0]) !![(2:ℝ), 1; 1, 2]
      (toLp 2 ![0, 0]) = 0 := by
  simp only [matchedStatistic]
  rw [fin_two_Rinv]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, WithLp.ofLp_toLp, Pi.sub_apply]

/-- **`n = 2`, non-diagonal covariance, all three branches.** `R = [[2, 1], [1, 2]]`,
`s0 = 0`, `s1 = (1, 1)`, equal priors, zero-one costs: `R⁻¹ s1 = (1/3, 1/3)`, the statistic is
`(y₁ + y₂) / 3` and the threshold `log 1 + (2/3) / 2 = 1/3`. The rule decides `true` at
`(1, 1)`, `tie` at `(1, 0)` and `false` at `(0, 0)`. -/
lemma matchedFilterRule_fin_two_example (tie : Bool) :
    matchedFilterRule (toLp 2 ![(1 : ℝ), 1]) (toLp 2 ![0, 0]) !![(2 : ℝ), 1; 1, 2] (1 / 2) (1 / 2)
        0 1 1 0 tie (toLp 2 ![1, 1]) = true ∧
      matchedFilterRule (toLp 2 ![(1 : ℝ), 1]) (toLp 2 ![0, 0]) !![(2 : ℝ), 1; 1, 2] (1 / 2)
        (1 / 2) 0 1 1 0 tie (toLp 2 ![1, 0]) = tie ∧
      matchedFilterRule (toLp 2 ![(1 : ℝ), 1]) (toLp 2 ![0, 0]) !![(2 : ℝ), 1; 1, 2] (1 / 2)
        (1 / 2) 0 1 1 0 tie (toLp 2 ![0, 0]) = false := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [matchedFilterRule]
    rw [fin_two_stat_true, fin_two_threshold]
    rw [ite_eq_left (by norm_num : (1/3:ℝ) < 2/3)]
  · simp only [matchedFilterRule]
    rw [fin_two_stat_tie, fin_two_threshold]
    rw [ite_eq_right (by norm_num : ¬(1/3:ℝ) < 1/3), ite_eq_left (rfl : (1/3:ℝ) = 1/3)]
  · simp only [matchedFilterRule]
    rw [fin_two_stat_false, fin_two_threshold]
    rw [ite_eq_right (by norm_num : ¬(1/3:ℝ) < 0), ite_eq_right (by norm_num : ¬(0:ℝ) = 1/3)]

/-- **`n = 2`, equal means.** `s0 = s1 = (1, 1)`, `R = [[2, 1], [1, 2]]`, `pi0 = 1/4`,
`pi1 = 3/4`, `C00 = 0`, `C01 = 4`, `C10 = 2`, `C11 = 1`: `pi0 (C10 - C00) = 1/2 < 9/4 =
pi1 (C01 - C11)`, so the rule decides `true` at every observation. -/
lemma matchedFilterRule_fin_two_equal_means_example (tie : Bool)
    (y : EuclideanSpace ℝ (Fin 2)) :
    matchedFilterRule (toLp 2 ![(1 : ℝ), 1]) (toLp 2 ![1, 1]) !![(2 : ℝ), 1; 1, 2] (1 / 4) (3 / 4)
      0 4 2 1 tie y = true := by
  have hrule := matchedFilterRule_of_eq (toLp 2 ![1, 1]) (!![(2:ℝ), 1; 1, 2]) (1 / 4) (3 / 4)
    (by norm_num) (by norm_num) 0 4 2 1 (by norm_num) (by norm_num) tie y
  rw [show toLp 2 ![(1:ℝ), 1] = toLp 2 ![1, 1] from rfl, hrule,
    ite_eq_left (by norm_num : (1/4:ℝ) * (2 - 0) < (3/4) * (4 - 1))]
end PhyslibExt.Instrumentation.GaussianMatchedDecision
