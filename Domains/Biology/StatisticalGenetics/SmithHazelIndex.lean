/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.SmithHazel
public import MathlibExt.Probability.Statistics.GaussianSelection
import Mathlib.Algebra.Order.Star.Real

/-!
# The Smith–Hazel selection index

For a Smith–Hazel model `M` (`Domains.Biology.StatisticalGenetics.SmithHazel`) with phenotypic
covariance `P`, additive genetic covariance `G`, economic weights `a`, aggregate breeding value
`H = a ⬝ᵥ A` and phenotype–objective covariance vector `c = (cov[X_i, H])ᵢ`, the index
`I_b = b ⬝ᵥ X` with coefficient vector `b` has `Var[I_b] = b ⬝ᵥ P b` and `cov[I_b, H] = b ⬝ᵥ c`.
The coefficients `w = P⁻¹ c` solve Hazel's normal equations, minimize `Var[H - I_b]`, and maximize
the correlation of `I_b` with `H`; every maximizer is a positive multiple of `w`. With jointly
Gaussian breeding values and residuals, truncation selection on `I_b` at `z` index standard
deviations gives the genetic gain `λ(z) ρ(I_b, H) σ_H`, where `λ(z) = φ(z) / Φ(-z)` is the
intensity of selection, so the same coefficients maximize the gain.

The generic Gaussian truncation results used here are in
`MathlibExt.Probability.Statistics.GaussianSelection`.

## References

* L. N. Hazel, *The genetic basis for constructing selection indexes*, Genetics 28 (1943)
  476–490, equations (1)–(8) and pp. 486–487.
* H. F. Smith, *A discriminant function for plant selection*, Ann. Eugenics 7 (1936) 240–250.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Probability.Causality.MissingData (inverseMillsRatio)
open scoped BigOperators Matrix

namespace SmithHazel

private lemma Model.memLp_phenotype {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (i : Fin n) : MemLp (fun ω => M.phenotype ω i) 2 μ :=
  (M.memLp_additive i).add (M.memLp_residual i)

private lemma Model.memLp_index {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b : Fin n → ℝ) : MemLp (M.index b) 2 μ :=
  memLp_dotProduct M.memLp_phenotype b

private lemma Model.memLp_aggregate {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : MemLp M.aggregate 2 μ :=
  memLp_dotProduct M.memLp_additive M.economic

private lemma Model.phenotypicCov_posDef {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (M : Model n Ω μ) : M.phenotypicCov.PosDef := by
  change Matrix.PosDef (fun i j => cov[fun ω => M.additive ω i + M.residual ω i,
    fun ω => M.additive ω j + M.residual ω j; μ])
  exact M.posDef

/-- **Covariance of two indices** (Hazel 1943). Let `μ` be a probability measure on `Ω` and `M` a
Smith–Hazel model on `n` traits under `μ`. For all coefficient vectors `b, d ∈ ℝⁿ`,
`cov[M.index b, M.index d; μ] = b ⬝ᵥ (M.phenotypicCov *ᵥ d)`. -/
theorem covariance_index_index {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b d : Fin n → ℝ) :
    cov[M.index b, M.index d; μ] = b ⬝ᵥ (M.phenotypicCov *ᵥ d) := by
  exact covariance_dotProduct_dotProduct M.memLp_phenotype M.memLp_phenotype b d

/-- **Variance of an index** (Hazel 1943). Let `μ` be a probability measure on `Ω` and `M` a
Smith–Hazel model on `n` traits under `μ`. For every coefficient vector `b ∈ ℝⁿ`,
`Var[M.index b; μ] = b ⬝ᵥ (M.phenotypicCov *ᵥ b)`. -/
theorem variance_index {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    Var[M.index b; μ] = b ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
  rw [← covariance_self (M.memLp_index b).aemeasurable]
  exact covariance_index_index M b b

/-- **Covariance of an index with the aggregate breeding value** (Hazel 1943). Let `μ` be a
probability measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ`. For every
coefficient vector `b ∈ ℝⁿ`, `cov[M.index b, M.aggregate; μ] = b ⬝ᵥ M.objectiveCov`. -/
theorem covariance_index_aggregate {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    cov[M.index b, M.aggregate; μ] = b ⬝ᵥ M.objectiveCov := by
  exact covariance_dotProduct_left M.memLp_phenotype M.memLp_aggregate b

/-- **Variance of the aggregate breeding value** (Hazel 1943). Let `μ` be a probability measure on
`Ω` and `M` a Smith–Hazel model on `n` traits under `μ`. Then
`Var[M.aggregate; μ] = M.economic ⬝ᵥ (M.geneticCov *ᵥ M.economic)`. -/
theorem variance_aggregate {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) :
    Var[M.aggregate; μ] = M.economic ⬝ᵥ (M.geneticCov *ᵥ M.economic) := by
  rw [← covariance_self M.memLp_aggregate.aemeasurable]
  exact covariance_dotProduct_dotProduct M.memLp_additive M.memLp_additive M.economic M.economic

/-- **Correlation of an index with the aggregate in matrix form** (Hazel 1943). Let `μ` be a
probability measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ`, with
`Var[M.aggregate; μ] > 0`. For every nonzero coefficient vector `b`,
`pearsonRatio μ (M.index b) M.aggregate = (b ⬝ᵥ c) / (√(b ⬝ᵥ (P *ᵥ b)) * √(a ⬝ᵥ (G *ᵥ a)))`, where
`P = M.phenotypicCov`, `G = M.geneticCov`, `c = M.objectiveCov` and `a = M.economic`. -/
theorem pearsonRatio_index_eq {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) :
    pearsonRatio μ (M.index b) M.aggregate =
      (b ⬝ᵥ M.objectiveCov) /
        (√(b ⬝ᵥ (M.phenotypicCov *ᵥ b)) *
          √(M.economic ⬝ᵥ (M.geneticCov *ᵥ M.economic))) := by
  simp only [pearsonRatio, populationSD, covariance_index_aggregate,
    variance_index, variance_aggregate]

/-- **Phenotypic covariance decomposes** (multivariate extension whose diagonal recovers Hazel
1943, equation (8)). Let `μ` be a probability measure on `Ω` and `M` a Smith–Hazel model on `n`
traits under `μ`, where `M.orthogonal` assumes `cov[A_i, E_j; μ] = 0` for all trait pairs `i, j`.
Then `M.phenotypicCov = M.geneticCov + M.residualCov` entry by entry; on the diagonal this gives
the single-trait variance decomposition `σ_{X_i}² = σ_{G_i}² + σ_{E_i}²` of Hazel (1943,
equation (8)). -/
theorem phenotypicCov_eq_add {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) :
    M.phenotypicCov = M.geneticCov + M.residualCov := by
  ext i j
  change cov[(fun ω => M.additive ω i) + (fun ω => M.residual ω i),
    (fun ω => M.additive ω j) + (fun ω => M.residual ω j); μ] = _
  rw [covariance_add_left (M.memLp_additive i) (M.memLp_residual i)
    ((M.memLp_additive j).add (M.memLp_residual j)),
    covariance_add_right (M.memLp_additive i) (M.memLp_additive j) (M.memLp_residual j),
    covariance_add_right (M.memLp_residual i) (M.memLp_additive j) (M.memLp_residual j),
    M.orthogonal i j, covariance_comm (fun ω => M.residual ω i), M.orthogonal j i]
  simp [Model.geneticCov, Model.residualCov]

/-- **Hazel's path-coefficient formula in covariance form** (Hazel 1943). Let `μ` be a probability
measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ`. Then the phenotype–objective
covariance vector is `M.objectiveCov = M.geneticCov *ᵥ M.economic`. -/
theorem objectiveCov_eq_geneticCov_mulVec {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ) :
    M.objectiveCov = M.geneticCov *ᵥ M.economic := by
  funext i
  change cov[fun ω => M.phenotype ω i, fun ω => ∑ j, M.economic j * M.additive ω j; μ] = _
  rw [covariance_fun_sum_right (fun j => (M.memLp_additive j).const_mul (M.economic j))
    (M.memLp_phenotype i)]
  simp only [covariance_const_mul_right, mulVec, dotProduct, Model.geneticCov]
  apply Finset.sum_congr rfl
  intro j _
  change M.economic j * cov[(fun ω => M.additive ω i) + (fun ω => M.residual ω i),
    fun ω => M.additive ω j; μ] = _
  rw [covariance_add_left (M.memLp_additive i) (M.memLp_residual i) (M.memLp_additive j),
    covariance_comm (fun ω => M.residual ω i), M.orthogonal j i]
  simp [mul_comm]

/-- **The index coefficients in genetic form** (Hazel 1943). Let `μ` be a probability measure on `Ω`
and `M` a Smith–Hazel model on `n` traits under `μ`. Then
`M.regressionWeights = M.phenotypicCov⁻¹ *ᵥ (M.geneticCov *ᵥ M.economic)`. -/
theorem regressionWeights_eq_geneticCov {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ) :
    M.regressionWeights = M.phenotypicCov⁻¹ *ᵥ (M.geneticCov *ᵥ M.economic) := by
  rw [Model.regressionWeights, objectiveCov_eq_geneticCov_mulVec]

/-- **Positive index variance** (Hazel 1943). Let `μ` be a probability measure on `Ω` and `M` a
Smith–Hazel model on `n` traits under `μ`. For every coefficient vector `b`, `0 < Var[M.index b; μ]`
if and only if `b ≠ 0`. -/
theorem variance_index_pos_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    0 < Var[M.index b; μ] ↔ b ≠ 0 := by
  rw [variance_index]
  constructor
  · intro h hz
    simp [hz] at h
  · intro hb
    simpa using M.phenotypicCov_posDef.dotProduct_mulVec_pos hb

/-- **Zero index variance** (Hazel 1943). Let `μ` be a probability measure on `Ω` and `M` a
Smith–Hazel model on `n` traits under `μ`. For every coefficient vector `b`, `Var[M.index b; μ] = 0`
if and only if `b = 0`. -/
theorem variance_index_eq_zero_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    Var[M.index b; μ] = 0 ↔ b = 0 := by
  constructor
  · intro h
    by_contra hb
    have := (variance_index_pos_iff M b).mpr hb
    linarith
  · intro h
    simp [variance_index, h]

/-- **Economic weights against the objective covariances** (Hazel 1943). Let `μ` be a probability
measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ`. Then
`M.economic ⬝ᵥ M.objectiveCov = Var[M.aggregate; μ]`. -/
theorem economic_dot_objectiveCov {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) :
    M.economic ⬝ᵥ M.objectiveCov = Var[M.aggregate; μ] := by
  rw [objectiveCov_eq_geneticCov_mulVec, variance_aggregate]

/-- **A constant aggregate** (Hazel 1943). Let `μ` be a probability measure on `Ω` and `M` a
Smith–Hazel model on `n` traits under `μ`. Then `Var[M.aggregate; μ] = 0` if and only if the
phenotype–objective covariance vector vanishes, `M.objectiveCov = 0`. -/
theorem variance_aggregate_eq_zero_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) :
    Var[M.aggregate; μ] = 0 ↔ M.objectiveCov = 0 := by
  have hG : M.geneticCov.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      simpa [Model.geneticCov] using
        covariance_comm (fun ω => M.additive ω j) (fun ω => M.additive ω i) (μ := μ)
    · intro x
      have hx := covariance_dotProduct_dotProduct M.memLp_additive M.memLp_additive x x
      rw [covariance_self (memLp_dotProduct M.memLp_additive x).aemeasurable] at hx
      change Var[fun ω => x ⬝ᵥ M.additive ω; μ] = x ⬝ᵥ (M.geneticCov *ᵥ x) at hx
      simpa only [star_trivial, ← hx] using
        variance_nonneg (fun ω => x ⬝ᵥ M.additive ω) μ
  rw [variance_aggregate, objectiveCov_eq_geneticCov_mulVec]
  simpa using hG.dotProduct_mulVec_zero_iff (x := M.economic)

/-- **Hazel's normal equations** (Hazel 1943). Let `μ` be any measure on `Ω` and `M` a Smith–Hazel
model on `n` traits under `μ`. For every coefficient vector `b`,
`M.phenotypicCov *ᵥ b = M.objectiveCov` if and only if `b = M.regressionWeights`. -/
theorem normalEquations_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b : Fin n → ℝ) :
    M.phenotypicCov *ᵥ b = M.objectiveCov ↔ b = M.regressionWeights := by
  classical
  let : Invertible M.phenotypicCov := M.phenotypicCov_posDef.isUnit.invertible
  constructor
  · intro h
    exact (Matrix.inv_mulVec_eq_vec h.symm).symm
  · rintro rfl
    rw [Model.regressionWeights, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
      Matrix.one_mulVec]

private lemma Model.normal_weights {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : M.phenotypicCov *ᵥ M.regressionWeights = M.objectiveCov :=
  (normalEquations_iff M M.regressionWeights).mpr rfl

private lemma Model.pair_comm {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b d : Fin n → ℝ) :
    b ⬝ᵥ (M.phenotypicCov *ᵥ d) = d ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
  simpa using M.phenotypicCov_posDef.isHermitian.star_dotProduct_mulVec_comm b d

private lemma Model.weights_ne_zero {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (hc : M.objectiveCov ≠ 0) : M.regressionWeights ≠ 0 := by
  intro h
  have := M.normal_weights
  simp only [h, mulVec_zero] at this
  exact hc this.symm

private lemma Model.objective_pair_pos {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (hc : M.objectiveCov ≠ 0) :
    0 < M.objectiveCov ⬝ᵥ M.regressionWeights := by
  have h := M.phenotypicCov_posDef.dotProduct_mulVec_pos (M.weights_ne_zero hc)
  simpa only [star_trivial, M.normal_weights, dotProduct_comm] using h

private lemma Model.quadratic_sub_weights {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (M : Model n Ω μ) (b : Fin n → ℝ) (k : ℝ) :
    (b - k • M.regressionWeights) ⬝ᵥ
        (M.phenotypicCov *ᵥ (b - k • M.regressionWeights)) =
      b ⬝ᵥ (M.phenotypicCov *ᵥ b) - 2 * k * (b ⬝ᵥ M.objectiveCov) +
        k ^ 2 * (M.objectiveCov ⬝ᵥ M.regressionWeights) := by
  have hcross : M.regressionWeights ⬝ᵥ (M.phenotypicCov *ᵥ b) =
      b ⬝ᵥ M.objectiveCov := by rw [← M.pair_comm b, M.normal_weights]
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, M.normal_weights, hcross]
  rw [dotProduct_comm M.regressionWeights M.objectiveCov]
  ring

private lemma Model.error_variance {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    Var[fun ω => M.aggregate ω - M.index b ω; μ] =
      Var[M.aggregate; μ] - 2 * (b ⬝ᵥ M.objectiveCov) +
        b ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
  rw [variance_fun_sub M.memLp_aggregate (M.memLp_index b),
    covariance_comm, covariance_index_aggregate, variance_index]

private lemma Model.error_variance_decomposition {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    Var[fun ω => M.aggregate ω - M.index b ω; μ] =
      Var[fun ω => M.aggregate ω - M.index M.regressionWeights ω; μ] +
        (b - M.regressionWeights) ⬝ᵥ (M.phenotypicCov *ᵥ (b - M.regressionWeights)) := by
  have hq := M.quadratic_sub_weights b 1
  simp only [one_smul, one_pow, mul_one, one_mul] at hq
  rw [M.error_variance b, M.error_variance M.regressionWeights, hq, M.normal_weights,
    dotProduct_comm M.regressionWeights M.objectiveCov]
  ring

private lemma Model.sd_phenotype_pos {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (i : Fin n) :
    0 < populationSD μ (fun ω => M.phenotype ω i) :=
  Real.sqrt_pos.mpr (M.variance_phenotype_pos i)

/-- **Hazel's normal equations in correlation form** (Hazel 1943, equations (5)–(7)). Let `μ` be a
probability measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ`, with
`Var[M.aggregate; μ] > 0`. For every trait `i`,
`∑_j pearsonRatio μ X_i X_j * M.beta j = pearsonRatio μ X_i M.aggregate`, where `X_i` is the
phenotype of trait `i` and `M.beta j = w_j σ_{X_j} / σ_H` is the standardized coefficient. -/
theorem standardized_normalEquations {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (_hH : 0 < Var[M.aggregate; μ]) (i : Fin n) :
    (∑ j, pearsonRatio μ (fun ω => M.phenotype ω i) (fun ω => M.phenotype ω j) *
      M.beta j) = pearsonRatio μ (fun ω => M.phenotype ω i) M.aggregate := by
  have h : (∑ j, M.phenotypicCov i j * M.regressionWeights j) = M.objectiveCov i :=
    congrFun M.normal_weights i
  unfold pearsonRatio Model.beta
  have heach : ∀ j, M.phenotypicCov i j /
      (populationSD μ (fun ω => M.phenotype ω i) *
        populationSD μ (fun ω => M.phenotype ω j)) *
      (M.regressionWeights j * populationSD μ (fun ω => M.phenotype ω j) /
        populationSD μ M.aggregate) =
      (M.phenotypicCov i j * M.regressionWeights j) /
        (populationSD μ (fun ω => M.phenotype ω i) * populationSD μ M.aggregate) := by
    intro j
    field_simp [(M.sd_phenotype_pos i).ne', (M.sd_phenotype_pos j).ne',
      (Real.sqrt_pos.mpr _hH).ne']
  change (∑ j, M.phenotypicCov i j / _ * _) = M.objectiveCov i / _
  simp_rw [heach]
  rw [← Finset.sum_div, h]

/-- **The index coefficients minimize the prediction error** (Hazel 1943). Let `μ` be a probability
measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ`. For every coefficient vector
`b`, `Var[M.aggregate - M.index b; μ] ≤ Var[M.aggregate - M.index d; μ]` for all `d` if and only if
`b = M.regressionWeights`. -/
theorem regressionWeights_iff_min_variance {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    (∀ d, Var[fun ω => M.aggregate ω - M.index b ω; μ] ≤
      Var[fun ω => M.aggregate ω - M.index d ω; μ]) ↔ b = M.regressionWeights := by
  constructor
  · intro h
    have hmin := h M.regressionWeights
    rw [M.error_variance_decomposition b] at hmin
    have hq : (b - M.regressionWeights) ⬝ᵥ
        (M.phenotypicCov *ᵥ (b - M.regressionWeights)) = 0 := by
      have hn := M.phenotypicCov_posDef.posSemidef.dotProduct_mulVec_nonneg
        (b - M.regressionWeights)
      simp only [star_trivial] at hn
      linarith
    have hz := M.phenotypicCov_posDef.posSemidef.dotProduct_mulVec_zero_iff.mp
      (show star (b - M.regressionWeights) ⬝ᵥ
        (M.phenotypicCov *ᵥ (b - M.regressionWeights)) = 0 by simpa using hq)
    have hb := M.phenotypicCov_posDef.mulVec_injective
      (show M.phenotypicCov *ᵥ (b - M.regressionWeights) = M.phenotypicCov *ᵥ 0 by
        simpa using hz)
    exact sub_eq_zero.mp hb
  · rintro rfl d
    rw [M.error_variance_decomposition d]
    have h := M.phenotypicCov_posDef.posSemidef.dotProduct_mulVec_nonneg
      (d - M.regressionWeights)
    simp only [star_trivial] at h
    linarith

private lemma Model.pearson_form {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    pearsonRatio μ (M.index b) M.aggregate =
      ((b ⬝ᵥ M.objectiveCov) / √(b ⬝ᵥ (M.phenotypicCov *ᵥ b))) /
        populationSD μ M.aggregate := by
  rw [pearsonRatio, covariance_index_aggregate]
  simp only [populationSD, variance_index, div_div]

private lemma Model.pearson_regression {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index M.regressionWeights) M.aggregate =
      √(M.objectiveCov ⬝ᵥ M.regressionWeights) / populationSD μ M.aggregate := by
  rw [M.pearson_form, M.normal_weights, dotProduct_comm M.regressionWeights M.objectiveCov]
  have h := M.objective_pair_pos hc
  congr 1
  apply (div_eq_iff (Real.sqrt_pos.mpr h).ne').mpr
  exact (Real.mul_self_sqrt h.le).symm

private lemma Model.pearson_smul_pos {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) {k : ℝ} (hk : 0 < k) :
    pearsonRatio μ (M.index (k • b)) M.aggregate =
      pearsonRatio μ (M.index b) M.aggregate := by
  have hi : M.index (k • b) = fun ω => k * M.index b ω := by
    funext ω
    exact smul_dotProduct k b (M.phenotype ω)
  rw [hi, pearsonRatio, pearsonRatio, covariance_const_mul_left]
  have hs : populationSD μ (fun ω => k * M.index b ω) =
      k * populationSD μ (M.index b) := by
    rw [populationSD, variance_const_mul, Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk.le]
    rfl
  rw [hs]
  field_simp

private lemma Model.pearson_neg {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    pearsonRatio μ (M.index (-b)) M.aggregate = -pearsonRatio μ (M.index b) M.aggregate := by
  have hi : M.index (-b) = fun ω => -M.index b ω := by
    funext ω
    exact neg_dotProduct b (M.phenotype ω)
  rw [hi, pearsonRatio, pearsonRatio, covariance_fun_neg_left]
  simp only [populationSD, variance_fun_neg, neg_div]

/-- **Upper bound on the correlation** (Hazel 1943). Let `μ` be a probability measure on `Ω` and `M`
a Smith–Hazel model on `n` traits under `μ`, with `Var[M.aggregate; μ] > 0` and
`M.objectiveCov ≠ 0`. For every nonzero coefficient vector `b`,
`pearsonRatio μ (M.index b) M.aggregate ≤ √(c ⬝ᵥ w) / σ_H`, where `c = M.objectiveCov`,
`w = M.regressionWeights` and `σ_H = populationSD μ M.aggregate`. -/
theorem pearsonRatio_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index b) M.aggregate ≤
      √(M.objectiveCov ⬝ᵥ M.regressionWeights) / populationSD μ M.aggregate := by
  have hq : 0 < b ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
    simpa using M.phenotypicCov_posDef.dotProduct_mulVec_pos _hb
  have hQ := M.objective_pair_pos _hc
  have hcs := M.phenotypicCov_posDef.star_dotProduct_mulVec_mul_le b M.regressionWeights
  simp only [star_trivial, M.normal_weights,
    dotProduct_comm M.regressionWeights M.objectiveCov, ← pow_two] at hcs
  have hn : b ⬝ᵥ M.objectiveCov ≤
      √(b ⬝ᵥ (M.phenotypicCov *ᵥ b)) * √(M.objectiveCov ⬝ᵥ M.regressionWeights) := by
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    simpa only [mul_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hQ.le] using hcs
  rw [M.pearson_form]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hq)).mpr (by simpa only [mul_comm] using hn)

/-- **The upper bound is attained exactly on the positive ray of `w`** (Hazel 1943). Let `μ` be a
probability measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ`, with
`Var[M.aggregate; μ] > 0` and `M.objectiveCov ≠ 0`. For every nonzero coefficient vector `b`,
`pearsonRatio μ (M.index b) M.aggregate = √(c ⬝ᵥ w) / σ_H` if and only if `b = k • w` for some
`k > 0`, where `c = M.objectiveCov`, `w = M.regressionWeights` and
`σ_H = populationSD μ M.aggregate`. -/
theorem pearsonRatio_eq_upper_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index b) M.aggregate =
      √(M.objectiveCov ⬝ᵥ M.regressionWeights) / populationSD μ M.aggregate ↔
      ∃ k : ℝ, 0 < k ∧ b = k • M.regressionWeights := by
  have hq : 0 < b ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
    simpa using M.phenotypicCov_posDef.dotProduct_mulVec_pos _hb
  have hQ := M.objective_pair_pos _hc
  have hsQ := Real.sqrt_pos.mpr hQ
  have hsq := Real.sqrt_pos.mpr hq
  constructor
  · intro h
    rw [M.pearson_form] at h
    have ht : b ⬝ᵥ M.objectiveCov =
        √(b ⬝ᵥ (M.phenotypicCov *ᵥ b)) * √(M.objectiveCov ⬝ᵥ M.regressionWeights) := by
      have hn := (div_left_inj₀ (Real.sqrt_pos.mpr _hH).ne').mp h
      have := (div_eq_iff hsq.ne').mp hn
      simpa only [mul_comm] using this
    let k := √(b ⬝ᵥ (M.phenotypicCov *ᵥ b)) / √(M.objectiveCov ⬝ᵥ M.regressionWeights)
    have hk : 0 < k := div_pos hsq hsQ
    have hkQ : k ^ 2 * (M.objectiveCov ⬝ᵥ M.regressionWeights) =
        b ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
      dsimp [k]
      rw [div_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hQ.le,
        div_mul_cancel₀ _ hQ.ne']
    have hkt : k * (b ⬝ᵥ M.objectiveCov) = b ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
      dsimp [k]
      rw [ht]
      field_simp
      nlinarith [Real.sq_sqrt hq.le]
    have hz : (b - k • M.regressionWeights) ⬝ᵥ
        (M.phenotypicCov *ᵥ (b - k • M.regressionWeights)) = 0 := by
      rw [M.quadratic_sub_weights, hkQ]
      nlinarith [hkt]
    have heq : b - k • M.regressionWeights = 0 := by
      apply M.phenotypicCov_posDef.mulVec_injective
      have hz' := M.phenotypicCov_posDef.posSemidef.dotProduct_mulVec_zero_iff.mp
        (show star (b - k • M.regressionWeights) ⬝ᵥ
          (M.phenotypicCov *ᵥ (b - k • M.regressionWeights)) = 0 by simpa using hz)
      simpa using hz'
    exact ⟨k, hk, sub_eq_zero.mp heq⟩
  · rintro ⟨k, hk, rfl⟩
    rw [M.pearson_smul_pos _ hk, M.pearson_regression _hc]

/-- **Lower bound on the correlation** (Hazel 1943). Let `μ` be a probability measure on `Ω` and `M`
a Smith–Hazel model on `n` traits under `μ`, with `Var[M.aggregate; μ] > 0` and
`M.objectiveCov ≠ 0`. For every nonzero coefficient vector `b`,
`-(√(c ⬝ᵥ w) / σ_H) ≤ pearsonRatio μ (M.index b) M.aggregate`, where `c = M.objectiveCov`,
`w = M.regressionWeights` and `σ_H = populationSD μ M.aggregate`. -/
theorem lower_le_pearsonRatio {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    -(√(M.objectiveCov ⬝ᵥ M.regressionWeights) / populationSD μ M.aggregate) ≤
      pearsonRatio μ (M.index b) M.aggregate := by
  have h := pearsonRatio_le M (neg_ne_zero.mpr _hb) _hH _hc
  rw [M.pearson_neg] at h
  linarith

/-- **The lower bound is attained exactly on the negative ray of `w`** (Hazel 1943). Let `μ` be a
probability measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ`, with
`Var[M.aggregate; μ] > 0` and `M.objectiveCov ≠ 0`. For every nonzero coefficient vector `b`,
`pearsonRatio μ (M.index b) M.aggregate = -(√(c ⬝ᵥ w) / σ_H)` if and only if `b = k • w` for some
`k < 0`, where `c = M.objectiveCov`, `w = M.regressionWeights` and
`σ_H = populationSD μ M.aggregate`. -/
theorem pearsonRatio_eq_lower_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index b) M.aggregate =
      -(√(M.objectiveCov ⬝ᵥ M.regressionWeights) / populationSD μ M.aggregate) ↔
      ∃ k : ℝ, k < 0 ∧ b = k • M.regressionWeights := by
  have h := pearsonRatio_eq_upper_iff M (neg_ne_zero.mpr _hb) _hH _hc
  rw [M.pearson_neg] at h
  constructor
  · intro heq
    obtain ⟨k, hk, hb⟩ := h.mp (by linarith)
    refine ⟨-k, by linarith, ?_⟩
    simpa using congrArg Neg.neg hb
  · rintro ⟨k, hk, hb⟩
    have hn : -b = (-k) • M.regressionWeights := by simp [hb]
    have heq := h.mpr ⟨-k, by linarith, hn⟩
    linarith

/-- **Upper bound on the squared correlation** (Hazel 1943). Let `μ` be a probability measure on `Ω`
and `M` a Smith–Hazel model on `n` traits under `μ`, with `Var[M.aggregate; μ] > 0` and
`M.objectiveCov ≠ 0`. For every nonzero coefficient vector `b`,
`pearsonRatio μ (M.index b) M.aggregate ^ 2 ≤ (c ⬝ᵥ w) / Var[M.aggregate; μ]`, where
`c = M.objectiveCov` and `w = M.regressionWeights`. -/
theorem pearsonRatio_sq_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index b) M.aggregate ^ 2 ≤
      (M.objectiveCov ⬝ᵥ M.regressionWeights) / Var[M.aggregate; μ] := by
  have hu := pearsonRatio_le M _hb _hH _hc
  have hl := lower_le_pearsonRatio M _hb _hH _hc
  have hQ := M.objective_pair_pos _hc
  have hbound : (√(M.objectiveCov ⬝ᵥ M.regressionWeights) /
      populationSD μ M.aggregate) ^ 2 =
      (M.objectiveCov ⬝ᵥ M.regressionWeights) / Var[M.aggregate; μ] := by
    rw [div_pow, Real.sq_sqrt hQ.le, populationSD, Real.sq_sqrt _hH.le]
  rw [← hbound]
  nlinarith

/-- **The squared bound is attained exactly on the line of `w`** (Hazel 1943). Let `μ` be a
probability measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ`, with
`Var[M.aggregate; μ] > 0` and `M.objectiveCov ≠ 0`. For every nonzero coefficient vector `b`,
`pearsonRatio μ (M.index b) M.aggregate ^ 2 = (c ⬝ᵥ w) / Var[M.aggregate; μ]` if and only if
`b = k • w` for some `k ≠ 0`, where `c = M.objectiveCov` and `w = M.regressionWeights`. -/
theorem pearsonRatio_sq_eq_upper_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index b) M.aggregate ^ 2 =
      (M.objectiveCov ⬝ᵥ M.regressionWeights) / Var[M.aggregate; μ] ↔
      ∃ k : ℝ, k ≠ 0 ∧ b = k • M.regressionWeights := by
  have hQ := M.objective_pair_pos _hc
  have hbound : (√(M.objectiveCov ⬝ᵥ M.regressionWeights) /
      populationSD μ M.aggregate) ^ 2 =
      (M.objectiveCov ⬝ᵥ M.regressionWeights) / Var[M.aggregate; μ] := by
    rw [div_pow, Real.sq_sqrt hQ.le, populationSD, Real.sq_sqrt _hH.le]
  rw [← hbound, sq_eq_sq_iff_eq_or_eq_neg,
    pearsonRatio_eq_upper_iff M _hb _hH _hc, pearsonRatio_eq_lower_iff M _hb _hH _hc]
  constructor
  · rintro (⟨k, hk, hb⟩ | ⟨k, hk, hb⟩)
    · exact ⟨k, hk.ne', hb⟩
    · exact ⟨k, hk.ne, hb⟩
  · rintro ⟨k, hk, hb⟩
    rcases lt_or_gt_of_ne hk with h | h
    · exact Or.inr ⟨k, h, hb⟩
    · exact Or.inl ⟨k, h, hb⟩

private lemma Model.canonical_sum {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (hH : 0 < Var[M.aggregate; μ]) :
    (∑ i, M.beta i * pearsonRatio μ (fun ω => M.phenotype ω i) M.aggregate) =
      (M.objectiveCov ⬝ᵥ M.regressionWeights) / Var[M.aggregate; μ] := by
  calc
    _ = ∑ i, (M.objectiveCov i * M.regressionWeights i) /
        populationSD μ M.aggregate ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      unfold Model.beta pearsonRatio
      change M.regressionWeights i * populationSD μ (fun ω => M.phenotype ω i) /
          populationSD μ M.aggregate *
        (M.objectiveCov i / (populationSD μ (fun ω => M.phenotype ω i) *
          populationSD μ M.aggregate)) = _
      field_simp [(M.sd_phenotype_pos i).ne', (Real.sqrt_pos.mpr hH).ne']
    _ = (M.objectiveCov ⬝ᵥ M.regressionWeights) / populationSD μ M.aggregate ^ 2 := by
      rw [← Finset.sum_div]
      rfl
    _ = _ := by rw [populationSD, Real.sq_sqrt hH.le]

/-- **Squared correlation of the optimal index** (Hazel 1943, p. 486). Let `μ` be a probability
measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ`, with `Var[M.aggregate; μ] > 0`
and `M.objectiveCov ≠ 0`. Then the squared correlation of the index `I_w`,
`w = M.regressionWeights`, with the aggregate is `∑_i M.beta i * pearsonRatio μ X_i M.aggregate`,
where `X_i` is the phenotype of trait `i`. -/
theorem pearsonRatio_sq_regressionWeights_eq_sum {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index M.regressionWeights) M.aggregate ^ 2 =
      ∑ i, M.beta i * pearsonRatio μ (fun ω => M.phenotype ω i) M.aggregate := by
  rw [M.pearson_regression _hc, M.canonical_sum _hH, div_pow,
    Real.sq_sqrt (M.objective_pair_pos _hc).le, populationSD, Real.sq_sqrt _hH.le]

/-- **Correlation of the optimal index** (Hazel 1943, p. 486). Let `μ` be a probability measure on
`Ω` and `M` a Smith–Hazel model on `n` traits under `μ`, with `Var[M.aggregate; μ] > 0` and
`M.objectiveCov ≠ 0`. Then the correlation of the index `I_w`, `w = M.regressionWeights`, with the
aggregate is the nonnegative square root `√(∑_i M.beta i * pearsonRatio μ X_i M.aggregate)`, where
`X_i` is the phenotype of trait `i`. -/
theorem pearsonRatio_regressionWeights_eq_sqrt_sum {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index M.regressionWeights) M.aggregate =
      √(∑ i, M.beta i * pearsonRatio μ (fun ω => M.phenotype ω i) M.aggregate) := by
  rw [← pearsonRatio_sq_regressionWeights_eq_sum M _hH _hc]
  symm
  apply Real.sqrt_sq
  rw [M.pearson_regression _hc]
  exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **Hazel's sum in matrix form** (Hazel 1943, p. 486). Let `μ` be a probability measure on `Ω` and
`M` a Smith–Hazel model on `n` traits under `μ`, with `Var[M.aggregate; μ] > 0`. Then
`∑_i M.beta i * pearsonRatio μ X_i M.aggregate = (c ⬝ᵥ w) / Var[M.aggregate; μ]`, where `X_i` is the
phenotype of trait `i`, `c = M.objectiveCov` and `w = M.regressionWeights`. -/
theorem sum_beta_mul_pearsonRatio {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (_hH : 0 < Var[M.aggregate; μ]) :
    (∑ i, M.beta i * pearsonRatio μ (fun ω => M.phenotype ω i) M.aggregate) =
      (M.objectiveCov ⬝ᵥ M.regressionWeights) / Var[M.aggregate; μ] := by
  exact M.canonical_sum _hH

/-- **Uncorrelated traits** (Hazel 1943, p. 487). Let `μ` be a probability measure on `Ω` and `M` a
Smith–Hazel model on `n` traits under `μ`, and suppose the phenotypic and additive genetic
covariance matrices are diagonal (`M.phenotypicCov i j = 0` and `M.geneticCov i j = 0` for `i ≠ j`).
Then for every trait `i`, `M.regressionWeights i = M.economic i * M.heritability i`, the economic
weight times the heritability `G_ii / P_ii`. -/
theorem regressionWeights_eq_economic_mul_heritability {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hP : ∀ i j, i ≠ j → M.phenotypicCov i j = 0)
    (_hG : ∀ i j, i ≠ j → M.geneticCov i j = 0) (i : Fin n) :
    M.regressionWeights i = M.economic i * M.heritability i := by
  classical
  have hPsum : (∑ j, M.phenotypicCov i j * M.regressionWeights j) =
      M.phenotypicCov i i * M.regressionWeights i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [_hP i j hji.symm, zero_mul]
    · simp
  have hGsum : (∑ j, M.geneticCov i j * M.economic j) =
      M.geneticCov i i * M.economic i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [_hG i j hji.symm, zero_mul]
    · simp
  have h := congrFun M.normal_weights i
  rw [objectiveCov_eq_geneticCov_mulVec M] at h
  change (∑ j, M.phenotypicCov i j * M.regressionWeights j) =
    ∑ j, M.geneticCov i j * M.economic j at h
  rw [hPsum, hGsum] at h
  unfold Model.heritability
  field_simp [M.phenotypicCov_posDef.diag_pos.ne']
  nlinarith [h]

/-- **Optimal indices for uncorrelated traits** (Hazel 1943, p. 487). Let `μ` be a probability
measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ`, with diagonal phenotypic and
additive genetic covariance matrices (`M.phenotypicCov i j = 0` and `M.geneticCov i j = 0` for
`i ≠ j`), `Var[M.aggregate; μ] > 0` and `M.objectiveCov ≠ 0`. For every nonzero coefficient vector
`b`, `b` maximizes `pearsonRatio μ (M.index d) M.aggregate` over all nonzero `d` if and only if
`b = k • (i ↦ M.economic i * M.heritability i)` for some `k > 0`. -/
theorem diagonal_pearsonRatio_max_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hP : ∀ i j, i ≠ j → M.phenotypicCov i j = 0)
    (_hG : ∀ i j, i ≠ j → M.geneticCov i j = 0) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    (∀ d : Fin n → ℝ, d ≠ 0 →
      pearsonRatio μ (M.index d) M.aggregate ≤ pearsonRatio μ (M.index b) M.aggregate) ↔
      ∃ k : ℝ, 0 < k ∧ b = k • (fun i => M.economic i * M.heritability i) := by
  have hw : M.regressionWeights = (fun i => M.economic i * M.heritability i) := by
    funext i
    exact regressionWeights_eq_economic_mul_heritability M _hP _hG i
  rw [← hw, ← pearsonRatio_eq_upper_iff M _hb _hH _hc]
  constructor
  · intro h
    have hmax := h M.regressionWeights (M.weights_ne_zero _hc)
    rw [M.pearson_regression _hc] at hmax
    exact le_antisymm (pearsonRatio_le M _hb _hH _hc) hmax
  · intro h d hd
    rw [h]
    exact pearsonRatio_le M hd _hH _hc

/-- **The aggregate and an index are jointly Gaussian.** Let `μ` be a measure on `Ω` and `M` a
Smith–Hazel model on `n` traits under `μ` whose additive values and residuals `(A, E)` are
jointly Gaussian under `μ` (`HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ`). Then for
every coefficient vector `b`, the pair `(M.aggregate, M.index b)` is jointly Gaussian under `μ`. -/
theorem hasGaussianLaw_aggregate_index {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (M : Model n Ω μ)
    (_hAE : HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ) (b : Fin n → ℝ) :
    HasGaussianLaw (fun ω => (M.aggregate ω, M.index b ω)) μ := by
  let a : (Fin n → ℝ) →L[ℝ] ℝ :=
    ∑ i, M.economic i • ContinuousLinearMap.proj i
  let c : (Fin n → ℝ) →L[ℝ] ℝ :=
    ∑ i, b i • ContinuousLinearMap.proj i
  let p := ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)
  let q := ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)
  simpa [a, c, p, q, Model.aggregate, Model.index, Model.phenotype,
    dotProduct, _root_.sum_apply, mul_add, Finset.sum_add_distrib] using
    _hAE.map_fun ((a.comp p).prod (c.comp (p + q)))

/-- **Genetic gain in covariance form** (Hazel 1943, equation (3)). Let `μ` be a probability measure
on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ` whose additive values and residuals
`(A, E)` are jointly Gaussian under `μ`. For every nonzero coefficient vector `b` and every
threshold `z`, the genetic gain from selecting the standardized upper event of `M.index b` at `z` is
`M.gain b z = inverseMillsRatio (-z) * (cov[M.index b, M.aggregate; μ] / σ_b)`, where
`σ_b = populationSD μ (M.index b)` and `inverseMillsRatio (-z) = φ(z) / Φ(-z)` is the intensity of
selection. -/
theorem gain_eq_covariance {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hAE : HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ)
    {b : Fin n → ℝ} (_hb : b ≠ 0) (z : ℝ) :
    M.gain b z = inverseMillsRatio (-z) * (cov[M.index b, M.aggregate; μ] /
      populationSD μ (M.index b)) := by
  apply conditionalMeanShift_standardizedUpperEvent_gaussian
  · change Measurable (fun ω => ∑ i, b i * (M.additive ω i + M.residual ω i))
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul
      (((measurable_pi_apply i).comp M.measurable_additive).add
        ((measurable_pi_apply i).comp M.measurable_residual))
  · exact hasGaussianLaw_aggregate_index M _hAE b
  · exact (variance_index_pos_iff M b).mpr _hb

/-- **Genetic gain** (Hazel 1943, equation (3)). Let `μ` be a probability measure on `Ω` and `M` a
Smith–Hazel model on `n` traits under `μ` whose additive values and residuals `(A, E)` are jointly
Gaussian under `μ`, with `Var[M.aggregate; μ] > 0`. For every nonzero coefficient vector `b` and
every threshold `z`,
`M.gain b z = inverseMillsRatio (-z) * pearsonRatio μ (M.index b) M.aggregate * σ_H`, where
`σ_H = populationSD μ M.aggregate`. -/
theorem gain_eq_pearsonRatio {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hAE : HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ)
    {b : Fin n → ℝ} (_hb : b ≠ 0) (_hH : 0 < Var[M.aggregate; μ]) (z : ℝ) :
    M.gain b z = inverseMillsRatio (-z) * pearsonRatio μ (M.index b) M.aggregate *
      populationSD μ M.aggregate := by
  rw [gain_eq_covariance M _hAE _hb]
  unfold pearsonRatio
  have hsd : populationSD μ M.aggregate ≠ 0 := (Real.sqrt_pos.mpr _hH).ne'
  field_simp

/-- **No gain for a constant aggregate.** Let `μ` be a probability measure on `Ω` and `M` a
Smith–Hazel model on `n` traits under `μ` whose additive values and residuals `(A, E)` are jointly
Gaussian under `μ`, with `Var[M.aggregate; μ] = 0`. For every nonzero coefficient vector `b` and
every threshold `z`, `M.gain b z = 0`. -/
theorem gain_eq_zero_of_variance_aggregate_eq_zero {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hAE : HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ)
    {b : Fin n → ℝ} (_hb : b ≠ 0) (_hH : Var[M.aggregate; μ] = 0) (z : ℝ) :
    M.gain b z = 0 := by
  rw [gain_eq_covariance M _hAE _hb, covariance_index_aggregate,
    (variance_aggregate_eq_zero_iff M).mp _hH]
  simp

/-- **The optimal index maximizes the genetic gain** (Smith 1936; Hazel 1943). Let `μ` be a
probability measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ` whose additive values
and residuals `(A, E)` are jointly Gaussian under `μ`, with `Var[M.aggregate; μ] > 0` and
`M.objectiveCov ≠ 0`. Fix a threshold `z`. For every nonzero coefficient vector `b`, the gain
satisfies `M.gain d z ≤ M.gain b z` for every nonzero `d` if and only if
`b = k • M.regressionWeights` for some `k > 0`. -/
theorem gain_max_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hAE : HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ)
    {b : Fin n → ℝ} (_hb : b ≠ 0) (_hH : 0 < Var[M.aggregate; μ])
    (_hc : M.objectiveCov ≠ 0) (z : ℝ) :
    (∀ d : Fin n → ℝ, d ≠ 0 → M.gain d z ≤ M.gain b z) ↔
      ∃ k : ℝ, 0 < k ∧ b = k • M.regressionWeights := by
  have hi := MathlibExt.Probability.Causality.MissingData.inverseMillsRatio_pos (-z)
  have hs : 0 < populationSD μ M.aggregate := Real.sqrt_pos.mpr _hH
  have horder : ∀ d, d ≠ 0 → (M.gain d z ≤ M.gain b z ↔
      pearsonRatio μ (M.index d) M.aggregate ≤ pearsonRatio μ (M.index b) M.aggregate) := by
    intro d hd
    rw [gain_eq_pearsonRatio M _hAE hd _hH, gain_eq_pearsonRatio M _hAE _hb _hH,
      mul_le_mul_iff_left₀ hs, mul_le_mul_iff_right₀ hi]
  rw [← pearsonRatio_eq_upper_iff M _hb _hH _hc]
  constructor
  · intro h
    have hmax := (horder M.regressionWeights (M.weights_ne_zero _hc)).mp
      (h M.regressionWeights (M.weights_ne_zero _hc))
    rw [M.pearson_regression _hc] at hmax
    exact le_antisymm (pearsonRatio_le M _hb _hH _hc) hmax
  · intro h d hd
    apply (horder d hd).mpr
    rw [h]
    exact pearsonRatio_le M hd _hH _hc

/-- **The reversed optimal index minimizes the genetic gain** (Smith 1936; Hazel 1943). Let `μ` be a
probability measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ` whose additive values
and residuals `(A, E)` are jointly Gaussian under `μ`, with `Var[M.aggregate; μ] > 0` and
`M.objectiveCov ≠ 0`. Fix a threshold `z`. For every nonzero coefficient vector `b`, the gain
satisfies `M.gain b z ≤ M.gain d z` for every nonzero `d` if and only if
`b = k • M.regressionWeights` for some `k < 0`. -/
theorem gain_min_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hAE : HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ)
    {b : Fin n → ℝ} (_hb : b ≠ 0) (_hH : 0 < Var[M.aggregate; μ])
    (_hc : M.objectiveCov ≠ 0) (z : ℝ) :
    (∀ d : Fin n → ℝ, d ≠ 0 → M.gain b z ≤ M.gain d z) ↔
      ∃ k : ℝ, k < 0 ∧ b = k • M.regressionWeights := by
  have hi := MathlibExt.Probability.Causality.MissingData.inverseMillsRatio_pos (-z)
  have hs : 0 < populationSD μ M.aggregate := Real.sqrt_pos.mpr _hH
  have horder : ∀ d, d ≠ 0 → (M.gain b z ≤ M.gain d z ↔
      pearsonRatio μ (M.index b) M.aggregate ≤ pearsonRatio μ (M.index d) M.aggregate) := by
    intro d hd
    rw [gain_eq_pearsonRatio M _hAE _hb _hH, gain_eq_pearsonRatio M _hAE hd _hH,
      mul_le_mul_iff_left₀ hs, mul_le_mul_iff_right₀ hi]
  rw [← pearsonRatio_eq_lower_iff M _hb _hH _hc]
  constructor
  · intro h
    have hn : -M.regressionWeights ≠ 0 := neg_ne_zero.mpr (M.weights_ne_zero _hc)
    have hmin := (horder (-M.regressionWeights) hn).mp (h (-M.regressionWeights) hn)
    rw [M.pearson_neg, M.pearson_regression _hc] at hmin
    exact le_antisymm hmin (lower_le_pearsonRatio M _hb _hH _hc)
  · intro h d hd
    apply (horder d hd).mpr
    rw [h]
    exact lower_le_pearsonRatio M hd _hH _hc

end SmithHazel
