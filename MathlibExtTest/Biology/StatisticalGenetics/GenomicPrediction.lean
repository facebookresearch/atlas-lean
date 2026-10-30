/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.GenomicPrediction
public import MathlibExtTest.Biology.StatisticalGenetics.LDScore

/-!
# Tests for genomic prediction from summary statistics

Non-vacuity witnesses for `PRSModel`, `StratifiedModel` and `CrossTraitModel` on the uniform
four-point space `μ4` with the scaled Hadamard sign vectors `had` (second moment `1/4` each,
pairwise orthogonal), and for `PRSModel.ofLDScore` from an `LDScore.Model`; concrete COJO and
Cochran–Armitage computations, including boundary cases.
-/

@[expose] public section

open MeasureTheory Matrix MathlibExt.Biology.StatisticalGenetics.GenomicPrediction
open MathlibExt.Biology.StatisticalGenetics.LDScore
open MathlibExtTest.Biology.StatisticalGenetics.LDScore
  (μ4 had integral_μ4 X2 isStandardized_X2)

namespace MathlibExtTest.Biology.StatisticalGenetics.GenomicPrediction

/-! ### Polygenic-score accuracy -/

/-- A witness `PRSModel` with one marker: effect `had 1` (`h² = 1/4`) and estimation error
`had 2` (`s² = 1/4`). -/
noncomputable def P1 : PRSModel μ4 1 where
  h2 := 1 / 4
  s2 := 1 / 4
  beta := fun _ => had 1
  err := fun _ => had 2
  memLp_beta := fun _ => MemLp.of_discrete
  memLp_err := fun _ => MemLp.of_discrete
  integral_beta_mul := by
    intro k l
    simp [Subsingleton.elim k l, integral_μ4, had]
    norm_num
  integral_err_mul := by
    intro k l
    simp [Subsingleton.elim k l, integral_μ4, had]
    norm_num
  integral_beta_mul_err := by
    intro k l
    simp [integral_μ4, had]
    norm_num

/-- `r²_g = h² / (h² + M s²) = (1/4) / (1/4 + 1/4) = 1/2`. -/
example : P1.accuracySq = 1 / 2 := by
  rw [P1.accuracySq_eq one_ne_zero]
  norm_num [P1]

/-- The Daetwyler–Dudbridge form with `s² = 1 / N`, `N = 4`: `4 · (1/4) / (4 · (1/4) + 1)`. -/
example : P1.accuracySq = 4 * (1 / 4) / (4 * (1 / 4) + 1) := by
  rw [P1.accuracySq_eq_of_s2 (N := 4) one_ne_zero four_ne_zero (by norm_num [P1])]
  norm_num [P1]

/-- The same value by direct computation of the three expectations. -/
example : P1.accuracySq = 1 / 2 := by
  simp [PRSModel.accuracySq, PRSModel.betaHat, P1, integral_μ4, had]
  norm_num

/-- The model forces `h² ≥ 0` and `s² ≥ 0`. -/
example : 0 ≤ P1.h2 ∧ 0 ≤ P1.s2 := ⟨P1.h2_nonneg one_pos, P1.s2_nonneg one_pos⟩

/-- Boundary: zero heritability gives zero accuracy (`0 / (0 + M s²)`). -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (D : PRSModel μ 3) (h : D.h2 = 0) :
    D.accuracySq = 0 := by
  rw [D.accuracySq_eq three_ne_zero, h, zero_div]

/-- A witness LD-score model with `N = 2` individuals and one marker: `h² = 9/25`, effect
`(6/5) · 2 had 1`, noise `(8/5) · 2 had 2`, `(8/5) · 2 had 3` (a 3-4-5 triangle keeps the moments
rational). -/
noncomputable def L : MathlibExt.Biology.StatisticalGenetics.LDScore.Model μ4 2 1 where
  h2 := 9 / 25
  beta := fun _ => fun ω => 6 / 5 * had 1 ω
  eps := ![fun ω => 8 / 5 * had 2 ω, fun ω => 8 / 5 * had 3 ω]
  memLp_beta := fun _ => MemLp.of_discrete
  memLp_eps := fun _ => MemLp.of_discrete
  integral_beta_mul := by
    intro k l
    simp [Subsingleton.elim k l, integral_μ4, had]
    norm_num
  integral_eps_mul := by
    intro i i'
    fin_cases i <;> fin_cases i' <;> simp [integral_μ4, had] <;> norm_num
  integral_beta_mul_eps := by
    intro k i
    fin_cases i <;> simp [integral_μ4, had] <;> norm_num

/-- The training column `(1, -1)` is orthogonal with sum of squares `2`. -/
def X21 : Matrix (Fin 2) (Fin 1) ℝ := !![1; -1]

theorem hasOrthogonalColumns_X21 : HasOrthogonalColumns X21 := by
  intro k l
  simp [Subsingleton.elim k l, X21, Fin.sum_univ_two]
  norm_num

/-- In the LD-score model the accuracy is `N h² / (N h² + M (1 - h²)) = 18 / 34 = 9 / 17`, not
the `N h² / (N h² + M) = 18 / 43` of the cited formula. -/
example : (PRSModel.ofLDScore L X21 hasOrthogonalColumns_X21).accuracySq = 9 / 17 := by
  rw [PRSModel.accuracySq_ofLDScore L X21 hasOrthogonalColumns_X21 two_ne_zero one_ne_zero]
  norm_num [L]

/-! ### COJO -/

/-- Three individuals, two markers; the second column is zero. -/
def Xz : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; -1, 0; 2, 0]

/-- The marginal estimate of the first marker is `x₀ᵀ y / x₀ᵀ x₀ = (1 - 2 + 6) / 6`. -/
example : marginalEstimate Xz ![1, 2, 3] 0 = 5 / 6 := by
  simp [marginalEstimate, Xz, mulVec, dotProduct, mul_apply, Fin.sum_univ_three]
  norm_num

/-- Boundary: for the zero column the marginal estimate is the junk value `0 / 0 = 0`, and
`Xᵀ y = D β̂` still holds there (both sides are `0`). -/
example : marginalEstimate Xz ![1, 2, 3] 1 = 0 ∧
    (Xzᵀ *ᵥ ![1, 2, 3]) 1 = (gramDiag Xz *ᵥ marginalEstimate Xz ![1, 2, 3]) 1 := by
  refine ⟨by simp [marginalEstimate, Xz, mulVec, dotProduct, mul_apply, Fin.sum_univ_three],
    by rw [transpose_mulVec_eq_gramDiag_mulVec]⟩

/-- Two uncorrelated markers (orthogonal columns): the joint estimate is the vector of marginal
estimates. -/
def Xo : Matrix (Fin 4) (Fin 2) ℝ := !![1, 1; 1, -1; -1, 1; -1, -1]

theorem gram_Xo : Xoᵀ * Xo = gramDiag Xo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramDiag, Xo, mul_apply, Fin.sum_univ_four, diagonal]

example (y : Fin 4 → ℝ) : (Xoᵀ * Xo)⁻¹ *ᵥ (Xoᵀ *ᵥ y) = marginalEstimate Xo y :=
  cojo_joint_of_diagonal Xo y gram_Xo fun j => by
    fin_cases j <;> simp [Xo, mul_apply, Fin.sum_univ_four] <;> norm_num

/-! ### Stratified LD-score regression -/

/-- A witness stratified model on `N = 2` individuals and `M = 2` markers with two overlapping
categories `{0}` and `{0, 1}`: `τ = (3/4, 1/4)`, so `Var β₀ = 1` and `Var β₁ = 1/4`; noise
variance `1/4`. -/
noncomputable def S2 : StratifiedModel μ4 2 2 (Fin 2) where
  cat := ![{0}, {0, 1}]
  tau := ![3 / 4, 1 / 4]
  sigma2e := 1 / 4
  beta := ![fun ω => 2 * had 1 ω, had 2]
  eps := ![had 3, had 0]
  memLp_beta := fun k => by fin_cases k <;> exact MemLp.of_discrete
  memLp_eps := fun i => by fin_cases i <;> exact MemLp.of_discrete
  integral_beta_mul := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [integral_μ4, had, Fin.sum_univ_two] <;> norm_num
  integral_eps_mul := by
    intro i i'
    fin_cases i <;> fin_cases i' <;> simp [integral_μ4, had] <;> norm_num
  integral_beta_mul_eps := by
    intro k i
    fin_cases k <;> fin_cases i <;> simp [integral_μ4, had] <;> norm_num

/-- `𝔼[χ²₀] = N (τ₀ ℓ(0, {0}) + τ₁ ℓ(0, {0, 1})) + σ²_e = 2 (3/4 · 1 + 1/4 · 2) + 1/4` for the
standardized perfect-LD matrix `X2 = [[1, 1], [-1, -1]]`. -/
example : ∫ ω, S2.chiSq X2 0 ω ∂μ4 = 11 / 4 := by
  rw [S2.integral_chiSq_of_standardized X2 two_ne_zero 0 isStandardized_X2]
  simp [S2, stratLDScore, ldCorr, X2, Fin.sum_univ_two]
  norm_num

/-- The same value by direct computation of the expectation. -/
example : ∫ ω, S2.chiSq X2 0 ω ∂μ4 = 11 / 4 := by
  simp [integral_μ4, StratifiedModel.chiSq, StratifiedModel.betaHat, StratifiedModel.pheno, S2,
    X2, had, Fin.sum_univ_two]
  norm_num

/-- One causal variant (LD proxy): the category `{1}` alone with `τ = 1/4`, noise variance
`1/4`, on `N = 2` individuals. -/
noncomputable def C1 : StratifiedModel μ4 2 2 Unit where
  cat := fun _ => {1}
  tau := fun _ => 1 / 4
  sigma2e := 1 / 4
  beta := ![fun _ => 0, had 1]
  eps := ![had 2, had 3]
  memLp_beta := fun k => by fin_cases k <;> exact MemLp.of_discrete
  memLp_eps := fun i => by fin_cases i <;> exact MemLp.of_discrete
  integral_beta_mul := by
    intro k l
    fin_cases k <;> fin_cases l <;> norm_num [integral_μ4, had]
  integral_eps_mul := by
    intro i i'
    fin_cases i <;> fin_cases i' <;> simp [integral_μ4, had] <;> norm_num
  integral_beta_mul_eps := by
    intro k i
    fin_cases k <;> fin_cases i <;> simp [integral_μ4, had] <;> norm_num

/-- Marker `0` has no effect but is in perfect LD with the causal marker `1` (`X2`):
`𝔼[χ²₀] = N τ r₀₁² + σ²_e = 2 · (1/4) · 1 + 1/4 = 3/4`. -/
example : ∫ ω, C1.chiSq X2 0 ω ∂μ4 = 3 / 4 := by
  rw [C1.integral_chiSq_single_causal X2 1 rfl two_ne_zero 0 isStandardized_X2]
  simp [C1, ldCorr, X2, Fin.sum_univ_two]
  norm_num

/-! ### Cross-trait scaled-score identity -/

/-- A witness bivariate model: a pool of two individuals, sample `S₁ = {0}` for trait 1 and
`S₂ = {0, 1}` for trait 2 (overlap `{0}`), one marker with shared effect `had 1`
(`ρ_g = 1/4`), and noise shared within each individual (`ρ_e = 1/4`). -/
noncomputable def T2 : CrossTraitModel μ4 2 1 where
  S1 := {0}
  S2 := Finset.univ
  rhoG := 1 / 4
  rhoE := 1 / 4
  beta1 := fun _ => had 1
  beta2 := fun _ => had 1
  eps1 := ![had 2, had 3]
  eps2 := ![had 2, had 3]
  memLp_beta1 := fun _ => MemLp.of_discrete
  memLp_beta2 := fun _ => MemLp.of_discrete
  memLp_eps1 := fun i => by fin_cases i <;> exact MemLp.of_discrete
  memLp_eps2 := fun i => by fin_cases i <;> exact MemLp.of_discrete
  integral_beta1_mul_beta2 := by
    intro k l
    simp [Subsingleton.elim k l, integral_μ4, had]
    norm_num
  integral_eps1_mul_eps2 := by
    intro i i'
    fin_cases i <;> fin_cases i' <;> simp [integral_μ4, had] <;> norm_num
  integral_beta1_mul_eps2 := by
    intro k i
    fin_cases i <;> simp [integral_μ4, had] <;> norm_num
  integral_eps1_mul_beta2 := by
    intro i k
    fin_cases i <;> simp [integral_μ4, had] <;> norm_num

/-- With the column `(1, -1)`: `r¹ = r² = 1` and the overlap contributes `x₀₀² = 1`, so
`𝔼[z₁ z₂] = √2 · (1/4) · 1 + (1/4) · 1 / √2`. -/
example : ∫ ω, T2.z1 X21 0 ω * T2.z2 X21 0 ω ∂μ4 = √2 / 4 + 1 / (4 * √2) := by
  rw [T2.integral_z_mul_z X21 0]
  simp [T2, sampleCorr, X21, Fin.sum_univ_two]
  ring

/-! ### The Cochran–Armitage trend test -/

open ArmitageTrend

/-- Cases `(1, 2, 3)` and controls `(3, 2, 1)` by allele count: the pooled sample `(4, 4, 4)`
is not in Hardy–Weinberg proportions (`4² ≠ 4 · 4 · 4`). -/
noncomputable def rA : Fin 3 → ℝ := ![1, 2, 3]
/-- Controls of the first table. -/
noncomputable def sA : Fin 3 → ℝ := ![3, 2, 1]

example : trendStat rA sA = 2 := by
  simp [trendStat, total, numer, rA, sA, Fin.sum_univ_three]
  norm_num

example : allelicStat rA sA = 8 / 3 := by
  simp [allelicStat, pearson2x2, rA, sA, Fin.sum_univ_three]
  norm_num

/-- The trend statistic is `N r²` with `N = 12`. -/
example : total rA sA * corrSq rA sA = 2 := by
  rw [← trendStat_eq_total_mul_corrSq]
  simp [trendStat, total, numer, rA, sA, Fin.sum_univ_three]
  norm_num

/-- Cases `(0, 1, 1)` and controls `(1, 1, 0)`: the pooled sample `(1, 2, 1)` is in
Hardy–Weinberg proportions, so the allelic and trend statistics agree (both `2`). -/
noncomputable def rB : Fin 3 → ℝ := ![0, 1, 1]
/-- Controls of the second table. -/
noncomputable def sB : Fin 3 → ℝ := ![1, 1, 0]

example : allelicStat rB sB = trendStat rB sB := by
  have hp : alleleFreq rB sB = 1 / 2 := by
    simp [alleleFreq, total, rB, sB, Fin.sum_univ_three]
    norm_num
  have hV : scoreVar rB sB = 1 / 2 := by
    simp [scoreVar, total, rB, sB, Fin.sum_univ_three]
    norm_num
  refine (allelicStat_eq_trendStat_iff rB sB (by simp [rB, Fin.sum_univ_three])
    (by simp [sB, Fin.sum_univ_three]) (by rw [hp]; norm_num) (by rw [hp]; norm_num)
    (by rw [hV]; norm_num) (by simp [numer, rB, sB, Fin.sum_univ_three])).2 ?_
  simp [rB, sB]
  norm_num

/-- Boundary (junk value outside the domain): with no controls the trend statistic is `0` by
the convention `x / 0 = 0`. -/
example : trendStat ![1, 2, 3] 0 = 0 := by
  simp [trendStat]

/-! ### Interpretation boundary checks -/

/-- Two full-rank one-column blocks selecting separate observations. -/
def X1full : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
/-- The second full-rank block. -/
def X2full : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]
/-- Response used for the full-rank conditional example. -/
def yfull : Fin 2 → ℝ := ![2, 3]

/-- Both Gram determinants are units, so the conditional formula has its least-squares
interpretation and recovers the second response coordinate. -/
example : IsUnit (X1fullᵀ * X1full).det ∧ IsUnit (X2fullᵀ * X2full).det ∧
    conditionalEstimate X1full X2full yfull 0 = 3 := by
  norm_num [conditionalEstimate, X1full, X2full, yfull, mulVec, dotProduct, mul_apply,
    Matrix.det_fin_one, Matrix.nonsing_inv_apply, Fin.sum_univ_two]

/-- A singular nonzero design with two identical columns. -/
def Xsing : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]
/-- Response lying in the column space of `Xsing`. -/
def ysing : Fin 2 → ℝ := ![1, 0]

/-- The singular Gram matrix makes the nonsingular inverse, hence the unconditional conditional
formula with an empty first block, zero. -/
example : (Xsingᵀ * Xsing).det = 0 ∧
    conditionalEstimate (0 : Matrix (Fin 2) (Fin 0) ℝ) Xsing ysing = 0 := by
  have hdet : (Xsingᵀ * Xsing).det = 0 := by
    norm_num [Xsing, mul_apply, Matrix.det_fin_two, Fin.sum_univ_two]
  refine ⟨hdet, ?_⟩
  have hinv : (Xsingᵀ * Xsing)⁻¹ = 0 :=
    Matrix.nonsing_inv_apply_not_isUnit _ (by simp [hdet])
  unfold conditionalEstimate
  rw [hinv]
  simp

/-- The zero junk value is not a least-squares fit: `[1, 0]` fits `ysing` exactly, while the
unconditional singular formula does not even reproduce `ysing`. -/
example : Xsing *ᵥ ![1, 0] = ysing ∧
    Xsing *ᵥ conditionalEstimate (0 : Matrix (Fin 2) (Fin 0) ℝ) Xsing ysing ≠ ysing := by
  have hdet : (Xsingᵀ * Xsing).det = 0 := by
    norm_num [Xsing, mul_apply, Matrix.det_fin_two, Fin.sum_univ_two]
  have hinv : (Xsingᵀ * Xsing)⁻¹ = 0 :=
    Matrix.nonsing_inv_apply_not_isUnit _ (by simp [hdet])
  have hz : conditionalEstimate (0 : Matrix (Fin 2) (Fin 0) ℝ) Xsing ysing = 0 := by
    unfold conditionalEstimate
    rw [hinv]
    simp
  rw [hz]
  constructor
  · funext i
    fin_cases i <;> simp [Xsing, ysing, mulVec, dotProduct, Fin.sum_univ_two]
  · intro h
    have := congrFun h 0
    norm_num [ysing] at this

/-- Trait-1 phenotype of overlapping individual `0` in the concrete bivariate model. -/
noncomputable def phenotype1At0 (ω : Fin 4) : ℝ :=
  (∑ k, X21 0 k * T2.beta1 k ω) + T2.eps1 0 ω

/-- Trait-2 phenotype of overlapping individual `0` in the concrete bivariate model. -/
noncomputable def phenotype2At0 (ω : Fin 4) : ℝ :=
  (∑ k, X21 0 k * T2.beta2 k ω) + T2.eps2 0 ω

/-- The overlap parameter is a residual cross-moment, not the phenotypic cross-moment: the
nonzero genetic contribution raises the latter from `1/4` to `1/2`. -/
example : T2.rhoE = 1 / 4 ∧
    (∫ ω, phenotype1At0 ω * phenotype2At0 ω ∂μ4) = 1 / 2 ∧
      (∫ ω, phenotype1At0 ω * phenotype2At0 ω ∂μ4) ≠ T2.rhoE := by
  simp [phenotype1At0, phenotype2At0, T2, X21, integral_μ4, had]
  norm_num

/-! ### Stratified normalization boundary checks -/

/-- The tested column is standardized but the second column has scale two. -/
def Xnonstd : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; -1, -2]

/-- The tested column has sum of squares `N`, but the full matrix is not standardized. -/
example : (∑ i, Xnonstd i 0 ^ 2) = 2 ∧ ¬IsStandardized Xnonstd := by
  constructor
  · norm_num [Xnonstd, Fin.sum_univ_two]
  · intro h
    have hk := (h 1).2
    norm_num [Xnonstd, Fin.sum_univ_two] at hk

/-- The raw normalized cross product is `2` and its square is `4`, while normalization by both
column norms gives squared correlation `1`. -/
example : ldCorr Xnonstd 0 1 = 2 ∧ ldCorr Xnonstd 0 1 ^ 2 = 4 ∧
    (∑ i, Xnonstd i 0 * Xnonstd i 1) ^ 2 /
      ((∑ i, Xnonstd i 0 ^ 2) * ∑ i, Xnonstd i 1 ^ 2) = 1 := by
  norm_num [ldCorr, Xnonstd, Fin.sum_univ_two]

/-- The generic normalized-cross-product identity remains valid without standardization. -/
example : ∫ ω, S2.chiSq Xnonstd 0 ω ∂μ4 =
    2 * ∑ c, S2.tau c * stratLDScore Xnonstd (S2.cat c) 0 +
      S2.sigma2e * (∑ i, Xnonstd i 0 ^ 2) / 2 := by
  exact S2.integral_chiSq Xnonstd 0

/-- For this unstandardized matrix the generic identity evaluates to `17/4`; no cited
LD-correlation specialization is used. -/
example : ∫ ω, S2.chiSq Xnonstd 0 ω ∂μ4 = 17 / 4 := by
  rw [S2.integral_chiSq Xnonstd 0]
  norm_num [S2, stratLDScore, ldCorr, Xnonstd, Fin.sum_univ_two]

end MathlibExtTest.Biology.StatisticalGenetics.GenomicPrediction
