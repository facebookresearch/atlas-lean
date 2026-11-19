/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.PolygenicRiskScore

/-!
# Tests for polygenic risk scores under LD

Witness LD-score models on the uniform space `Fin n` built from signed indicators (`+1` and `-1`
on two dedicated points, `0` elsewhere): mean zero, pairwise orthogonal, rational second moments.
-/

@[expose] public section

open MeasureTheory Matrix
open MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.PolygenicRiskScore
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.PolygenicRiskScore

/-! ### Signed-indicator witnesses -/

/-- The uniform probability measure on `Fin n`. -/
noncomputable def μU (n : ℕ) : Measure (Fin n) := ((n : ℝ≥0∞)⁻¹) • Measure.count

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (μU n) := by
  constructor
  have hn : (n : ℝ≥0∞) ≠ 0 := by simp [NeZero.ne n]
  simpa [μU] using ENNReal.inv_mul_cancel hn (by simp)

/-- Integration against `μU n` is averaging over the `n` outcomes. -/
theorem integral_μU {n : ℕ} (f : Fin n → ℝ) : ∫ ω, f ω ∂μU n = (∑ ω, f ω) / n := by
  simp only [μU, integral_smul_measure, integral_count, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  ring

/-- The signed indicator of slot `a`: `+1` at `2a`, `-1` at `2a + 1`, `0` elsewhere. -/
noncomputable def sgnN (a t : ℕ) : ℝ := if t = 2 * a then 1 else if t = 2 * a + 1 then -1 else 0

theorem sum_sgnN {n a : ℕ} (ha : 2 * a + 1 < n) : ∑ ω : Fin n, sgnN a ω = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun t => sgnN a t) n]
  have h (t : ℕ) : sgnN a t = (if t = 2 * a then 1 else 0) - (if t = 2 * a + 1 then 1 else 0) := by
    unfold sgnN; split_ifs <;> first | (exfalso; omega) | norm_num
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_range]
  simp [show 2 * a < n by omega, ha]

theorem sum_sgnN_mul {n a b : ℕ} (ha : 2 * a + 1 < n) :
    ∑ ω : Fin n, sgnN a ω * sgnN b ω = if a = b then 2 else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun t => sgnN a t * sgnN b t) n]
  split_ifs with hab
  · subst hab
    have h (t : ℕ) : sgnN a t * sgnN a t =
        (if t = 2 * a then 1 else 0) + (if t = 2 * a + 1 then 1 else 0) := by
      unfold sgnN; split_ifs <;> first | (exfalso; omega) | norm_num
    simp_rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
    simp [show 2 * a < n by omega, ha]
    norm_num
  · refine Finset.sum_eq_zero fun t _ => ?_
    unfold sgnN; split_ifs <;> first | (exfalso; omega) | simp

/-- An LD-score model on `Fin n` with effects `cb · sgnN k` and noise `ce · sgnN (M + i)`. -/
noncomputable def sgnModel (n N M : ℕ) [NeZero n] (h2 cb ce : ℝ) (hn : 2 * (M + N) ≤ n)
    (hb : 2 * cb ^ 2 / n = h2 / M) (he : 2 * ce ^ 2 / n = 1 - h2) : Model (μU n) N M where
  h2 := h2
  beta k ω := cb * sgnN k ω
  eps i ω := ce * sgnN (M + i) ω
  memLp_beta := fun _ => MemLp.of_discrete
  memLp_eps := fun _ => MemLp.of_discrete
  integral_beta_mul k l := by
    rw [integral_μU]
    have h (ω : Fin n) : cb * sgnN k ω * (cb * sgnN l ω) = cb ^ 2 * (sgnN k ω * sgnN l ω) := by
      ring
    simp_rw [h, ← Finset.mul_sum]
    rw [sum_sgnN_mul (by have := k.isLt; omega)]
    simp only [Fin.val_inj]
    split_ifs
    · rw [← hb]; ring
    · simp
  integral_eps_mul i i' := by
    rw [integral_μU]
    have h (ω : Fin n) : ce * sgnN (M + i) ω * (ce * sgnN (M + i') ω) =
        ce ^ 2 * (sgnN (M + i) ω * sgnN (M + i') ω) := by ring
    simp_rw [h, ← Finset.mul_sum]
    rw [sum_sgnN_mul (by have := i.isLt; omega)]
    simp only [Nat.add_left_cancel_iff, Fin.val_inj]
    split_ifs
    · rw [← he]; ring
    · simp
  integral_beta_mul_eps k i := by
    rw [integral_μU]
    have h (ω : Fin n) : cb * sgnN k ω * (ce * sgnN (M + i) ω) =
        cb * ce * (sgnN k ω * sgnN (M + i) ω) := by ring
    simp_rw [h, ← Finset.mul_sum]
    have hki : (k : ℕ) ≠ M + i := by have := k.isLt; omega
    rw [sum_sgnN_mul (by have := k.isLt; omega)]
    simp [hki]

theorem sgnModel_mean_beta {n N M : ℕ} [NeZero n] {h2 cb ce : ℝ} {hn : 2 * (M + N) ≤ n}
    {hb : 2 * cb ^ 2 / n = h2 / M} {he : 2 * ce ^ 2 / n = 1 - h2} (k : Fin M) :
    ∫ ω, (sgnModel n N M h2 cb ce hn hb he).beta k ω ∂μU n = 0 := by
  rw [integral_μU]
  simp only [sgnModel, ← Finset.mul_sum]
  rw [sum_sgnN (by have := k.isLt; omega)]
  simp

theorem sgnModel_mean_eps {n N M : ℕ} [NeZero n] {h2 cb ce : ℝ} {hn : 2 * (M + N) ≤ n}
    {hb : 2 * cb ^ 2 / n = h2 / M} {he : 2 * ce ^ 2 / n = 1 - h2} (i : Fin N) :
    ∫ ω, (sgnModel n N M h2 cb ce hn hb he).eps i ω ∂μU n = 0 := by
  rw [integral_μU]
  simp only [sgnModel, ← Finset.mul_sum]
  rw [sum_sgnN (by have := i.isLt; omega)]
  simp

/-! ### Two SNPs with LD `r = 1/2`

`N = 8` individuals with standardized `±1` columns `(1,1,1,1,-1,-1,-1,-1)` and
`(1,1,1,-1,1,-1,-1,-1)` (sample correlation `4 / 8 = 1/2`), `h² = 2/11`, on `Fin 22`. -/

def X8 : Matrix (Fin 8) (Fin 2) ℝ :=
  !![1, 1; 1, 1; 1, 1; 1, -1; -1, 1; -1, -1; -1, -1; -1, -1]

noncomputable def D8 : Model (μU 22) 8 2 :=
  sgnModel 22 8 2 (2 / 11) 1 3 (by norm_num) (by norm_num) (by norm_num)

theorem isStandardized_X8 : IsStandardized X8 := by
  intro k
  fin_cases k <;> simp [X8, Fin.sum_univ_succ] <;> norm_num

/-- `C(β, β̂) = (h² / M) L = (1/11) (5/2)`, computed from the definitions. -/
theorem quadCov_beta_betaHat_D8 :
    quadCov (μU 22) (ldMatrix X8) D8.beta (D8.betaHat X8) = 5 / 22 := by
  simp [quadCov, integral_μU, ldCorr, Model.betaHat, Model.pheno, D8, sgnModel, X8, sgnN,
    Fin.sum_univ_succ]
  norm_num

/-- `C(β, β) = h² = 2/11`, computed from the definitions. -/
theorem quadCov_beta_beta_D8 : quadCov (μU 22) (ldMatrix X8) D8.beta D8.beta = 2 / 11 := by
  simp [quadCov, integral_μU, ldCorr, D8, sgnModel, X8, sgnN, Fin.sum_univ_succ]
  norm_num

/-- `C(β̂, β̂) = (h² / M) T + ((1 - h²) / N) L = (1/11)(7/2) + (9/88)(5/2)`, computed from the
definitions. -/
theorem quadCov_betaHat_betaHat_D8 :
    quadCov (μU 22) (ldMatrix X8) (D8.betaHat X8) (D8.betaHat X8) = 101 / 176 := by
  simp [quadCov, integral_μU, ldCorr, Model.betaHat, Model.pheno, D8, sgnModel, X8, sgnN,
    Fin.sum_univ_succ]
  norm_num

/-- The squared accuracy of the marginal PRS, from the definitions: `(5/22)² / ((2/11)(101/176))`.
-/
example : accuracySq (μU 22) (ldMatrix X8) D8.beta (D8.betaHat X8) = 50 / 101 := by
  rw [accuracySq, quadCov_beta_betaHat_D8, quadCov_beta_beta_D8, quadCov_betaHat_betaHat_D8]
  norm_num

/-- The calibration slope of the marginal PRS, from the definitions: `(5/22) / (101/176)`; the
raw score is over-dispersed (slope below `1`). -/
example : calibSlope (μU 22) (ldMatrix X8) D8.beta (D8.betaHat X8) = 40 / 101 := by
  rw [calibSlope, quadCov_beta_betaHat_D8, quadCov_betaHat_betaHat_D8]
  norm_num

/-- `L = ℓ₀ + ℓ₁ = 2 (1 + 1/4)`. -/
theorem ldScoreSum_X8 : ldScoreSum X8 = 5 / 2 := by
  simp [ldScoreSum, ldScore, ldCorr, X8, Fin.sum_univ_succ]
  norm_num

/-- `T = tr R³ = 2 (1 + 3/4)` for `R = [[1, 1/2], [1/2, 1]]`. -/
theorem ldCube_X8 : ldCube X8 = 7 / 2 := by
  simp [ldCube, ldCorr, X8, Fin.sum_univ_succ]
  norm_num

/-- The theorem gives the same values. -/
example : accuracySq (μU 22) (ldMatrix X8) D8.beta (D8.betaHat X8) = 50 / 101 := by
  rw [accuracySq_marginal D8 X8 isStandardized_X8 (by norm_num) (by norm_num), ldScoreSum_X8,
    ldCube_X8, accuracyFormula]
  norm_num [D8, sgnModel]

example : calibSlope (μU 22) (ldMatrix X8) D8.beta (D8.betaHat X8) = 40 / 101 := by
  rw [calibSlope_marginal, ldScoreSum_X8, ldCube_X8, slopeFormula]
  norm_num [D8, sgnModel]

/-- The covariance of the marginal scores is invertible here (`det V = 819 / 30976`), so
`calibSlope_blup` applies to this design. -/
example : IsUnit (scoreCov 8 2 D8.h2 X8).det := by
  rw [isUnit_iff_ne_zero, det_fin_two]
  simp [scoreCov, ldCorr, X8, D8, sgnModel, Fin.sum_univ_succ, mul_apply]
  norm_num

/-! ### No LD: independent SNPs

`N = 4` individuals with orthogonal standardized columns `(1, 1, -1, -1)` and `(1, -1, 1, -1)`,
`h² = 1/3`, on `Fin 12`. -/

def X4 : Matrix (Fin 4) (Fin 2) ℝ := !![1, 1; 1, -1; -1, 1; -1, -1]

theorem hasOrthogonalColumns_X4 :
    MathlibExt.Biology.StatisticalGenetics.GenomicPrediction.HasOrthogonalColumns X4 := by
  intro k l
  fin_cases k <;> fin_cases l <;> simp [X4, Fin.sum_univ_succ] <;> norm_num

noncomputable def D4 : Model (μU 12) 4 2 :=
  sgnModel 12 4 2 (1 / 3) 1 2 (by norm_num) (by norm_num) (by norm_num)

theorem quadCov_beta_betaHat_D4 :
    quadCov (μU 12) (ldMatrix X4) D4.beta (D4.betaHat X4) = 1 / 3 := by
  simp [quadCov, integral_μU, ldCorr, Model.betaHat, Model.pheno, D4, sgnModel, X4, sgnN,
    Fin.sum_univ_succ]
  norm_num

theorem quadCov_beta_beta_D4 : quadCov (μU 12) (ldMatrix X4) D4.beta D4.beta = 1 / 3 := by
  simp [quadCov, integral_μU, ldCorr, D4, sgnModel, X4, sgnN, Fin.sum_univ_succ]
  norm_num

theorem quadCov_betaHat_betaHat_D4 :
    quadCov (μU 12) (ldMatrix X4) (D4.betaHat X4) (D4.betaHat X4) = 2 / 3 := by
  simp [quadCov, integral_μU, ldCorr, Model.betaHat, Model.pheno, D4, sgnModel, X4, sgnN,
    Fin.sum_univ_succ]
  norm_num

/-- From the definitions: `r² = (1/3)² / ((1/3)(2/3)) = 1/2`. -/
example : accuracySq (μU 12) (ldMatrix X4) D4.beta (D4.betaHat X4) = 1 / 2 := by
  rw [accuracySq, quadCov_beta_betaHat_D4, quadCov_beta_beta_D4, quadCov_betaHat_betaHat_D4]
  norm_num

/-- From the definitions: slope `(1/3) / (2/3) = 1/2`. -/
example : calibSlope (μU 12) (ldMatrix X4) D4.beta (D4.betaHat X4) = 1 / 2 := by
  rw [calibSlope, quadCov_beta_betaHat_D4, quadCov_betaHat_betaHat_D4]
  norm_num

/-- The no-LD theorem: `N h² / (N h² + M (1 - h²)) = (4/3) / (4/3 + 4/3)`. -/
example : accuracySq (μU 12) (ldMatrix X4) D4.beta (D4.betaHat X4) = 1 / 2 := by
  rw [accuracySq_marginal_of_orthogonal D4 X4 hasOrthogonalColumns_X4 (by norm_num)
    (by norm_num)]
  norm_num [D4, sgnModel]

/-- With no LD, `V = (1/3) I`, so the shrinkage is `K = (1/6) I (3 I) = (1/2) I`. -/
theorem shrinkMatrix_D4 :
    shrinkMatrix 4 2 D4.h2 X4 = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hR : ldMatrix X4 = 1 := by
    ext j k
    fin_cases j <;> fin_cases k <;> simp [ldCorr, X4, Fin.sum_univ_succ] <;> norm_num
  have hV : scoreCov 4 2 D4.h2 X4 = (1 / 3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [scoreCov, hR]
    simp only [D4, sgnModel, Matrix.mul_one, ← add_smul]
    norm_num
  have hVi : (scoreCov 4 2 D4.h2 X4)⁻¹ = (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hV]
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, Matrix.mul_one]
    norm_num
  rw [shrinkMatrix, hVi, hR, smul_mul_smul_comm, Matrix.mul_one]
  norm_num [D4, sgnModel]

theorem blupScore_D4 : blupScore D4 X4 = fun k ω => D4.betaHat X4 k ω / 2 := by
  funext k ω
  rw [blupScore, shrinkMatrix_D4]
  fin_cases k <;> simp [Fin.sum_univ_two] <;> ring

/-- The shrunk score is calibrated, checked from the definitions: `C(β, β̃) = C(β̃, β̃) = 1/6`. -/
example : calibSlope (μU 12) (ldMatrix X4) D4.beta (blupScore D4 X4) = 1 := by
  have h1 : quadCov (μU 12) (ldMatrix X4) D4.beta (blupScore D4 X4) = 1 / 6 := by
    rw [blupScore_D4]
    simp [quadCov, integral_μU, ldCorr, Model.betaHat, Model.pheno, D4, sgnModel, X4, sgnN,
      Fin.sum_univ_succ]
    norm_num
  have h2 : quadCov (μU 12) (ldMatrix X4) (blupScore D4 X4) (blupScore D4 X4) = 1 / 6 := by
    rw [blupScore_D4]
    simp [quadCov, integral_μU, ldCorr, Model.betaHat, Model.pheno, D4, sgnModel, X4, sgnN,
      Fin.sum_univ_succ]
    norm_num
  rw [calibSlope, h1, h2]
  norm_num

/-- The hypotheses of `calibSlope_blup` hold on this design. -/
example : calibSlope (μU 12) (ldMatrix X4) D4.beta (blupScore D4 X4) = 1 := by
  refine calibSlope_blup D4 X4 _ ?_ ?_
  · rw [isUnit_iff_ne_zero, det_fin_two]
    simp [scoreCov, ldCorr, X4, D4, sgnModel, Fin.sum_univ_succ, mul_apply]
    norm_num
  · rw [blupScore_D4]
    simp [quadCov, integral_μU, ldCorr, Model.betaHat, Model.pheno, D4, sgnModel, X4, sgnN,
      Fin.sum_univ_succ]
    norm_num

/-! ### Perfect LD: the calibration claim degenerates

Two identical standardized columns `(1, -1)` (`r = 1`). -/

def X2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; -1, -1]

example : IsStandardized X2 := by
  intro k
  fin_cases k <;> simp [X2, Fin.sum_univ_two] <;> norm_num

/-- The marginal formula stays defined: `L = 4`, `T = tr R³ = 8` for `R` the all-ones matrix. -/
example : ldScoreSum X2 = 4 ∧ ldCube X2 = 8 := by
  constructor
  · simp [ldScoreSum, ldScore, ldCorr, X2, Fin.sum_univ_two]
    norm_num
  · simp [ldCube, ldCorr, X2, Fin.sum_univ_two]
    norm_num

/-- `V = (h² / M) R² + ((1 - h²) / N) R` is singular for every `h²`. -/
theorem det_scoreCov_X2 (h2 : ℝ) : (scoreCov 2 2 h2 X2).det = 0 := by
  rw [det_fin_two]
  simp [scoreCov, ldCorr, X2, Fin.sum_univ_two, mul_apply]

/-- So the invertibility hypothesis of `calibSlope_blup` fails. -/
example (h2 : ℝ) : ¬ IsUnit (scoreCov 2 2 h2 X2).det := by
  rw [det_scoreCov_X2]
  exact not_isUnit_zero

/-- The shrunk score collapses to `0` (Mathlib's inverse of a singular matrix is `0`), and its
"calibration slope" is the junk value `0 / 0 = 0`, not `1`, for every model and target LD. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (D : Model μ 2 2)
    (S : Matrix (Fin 2) (Fin 2) ℝ) : calibSlope μ S D.beta (blupScore D X2) = 0 := by
  have hK : shrinkMatrix 2 2 D.h2 X2 = 0 := by
    rw [shrinkMatrix, nonsing_inv_apply_not_isUnit _ (by rw [det_scoreCov_X2]; exact
      not_isUnit_zero), Matrix.mul_zero]
  have hb : blupScore D X2 = fun _ _ => 0 := by
    funext k ω
    simp [blupScore, hK]
  simp [calibSlope, quadCov, hb]

/-- The LD scores are all equal (`ℓ = 2`), so the LD-score regression slope is not identified
and the hypothesis `sxy ℓ ℓ ≠ 0` of `accuracySq_marginal_eq_olsH2Hat` fails. -/
example : MathlibExt.Probability.FiniteProbability.sxy (ldScore X2) (ldScore X2) = 0 := by
  have h : ldScore X2 = fun _ => 2 := by
    funext j
    fin_cases j <;> simp [ldScore, ldCorr, X2, Fin.sum_univ_two] <;> norm_num
  simp [MathlibExt.Probability.FiniteProbability.sxy, h,
    MathlibExt.Probability.FiniteProbability.sampleMean,
    MathlibExt.Probability.Causality.popMean]

/-! ### LD-score regression identifies the accuracy: a non-vacuous instance

`N = 8`, `M = 3`: the two markers of `X8` and a third marker uncorrelated with both, so the LD
scores `(5/4, 5/4, 1)` are not all equal; `h² = 1/4`, mean-zero effects and noise on `Fin 24`. -/

def X83 : Matrix (Fin 8) (Fin 3) ℝ :=
  !![1, 1, 1; 1, 1, -1; 1, 1, -1; 1, -1, 1; -1, 1, 1; -1, -1, -1; -1, -1, -1; -1, -1, 1]

theorem isStandardized_X83 : IsStandardized X83 := by
  intro k
  fin_cases k <;> simp [X83, Fin.sum_univ_succ] <;> norm_num

theorem sxy_ldScore_X83 :
    MathlibExt.Probability.FiniteProbability.sxy (ldScore X83) (ldScore X83) ≠ 0 := by
  simp [MathlibExt.Probability.FiniteProbability.sxy,
    MathlibExt.Probability.FiniteProbability.sampleMean,
    MathlibExt.Probability.Causality.popMean, ldScore, ldCorr, X83, Fin.sum_univ_succ]
  norm_num

noncomputable def D83 : Model (μU 24) 8 3 :=
  sgnModel 24 8 3 (1 / 4) 1 3 (by norm_num) (by norm_num) (by norm_num)

example : accuracySq (μU 24) (ldMatrix X83) D83.beta (D83.betaHat X83) =
    accuracyFormula 8 3
      (MathlibExt.Biology.StatisticalGenetics.LDScoreRegression.olsH2Hat 8 3 (ldScore X83)
        fun j => ∫ ω, D83.chiSq X83 j ω ∂μU 24)
      (ldScoreSum X83) (ldCube X83) :=
  accuracySq_marginal_eq_olsH2Hat D83 X83 isStandardized_X83 (by norm_num) (by norm_num)
    sxy_ldScore_X83 sgnModel_mean_beta sgnModel_mean_eps

end MathlibExtTest.Biology.StatisticalGenetics.PolygenicRiskScore
