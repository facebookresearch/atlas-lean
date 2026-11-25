/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import MathlibExt.Probability.Statistics.StandardizedSelection
import Mathlib.Probability.Moments.Covariance

/-!
# The Smith–Hazel model

A Smith–Hazel model on `n` traits consists of random vectors of additive breeding values `A` and
residuals `E` with square-integrable coordinates, every `A_i` uncorrelated with every `E_j`, and
a positive definite phenotypic covariance matrix, together with economic weights `a`. The
phenotype is `X = A + E`, the aggregate breeding value (the breeding objective) is
`H = a ⬝ᵥ A`, and an index with coefficient vector `b` is the linear score `I_b = b ⬝ᵥ X`. This
file defines the model, its covariance matrices, the index coefficients `w = P⁻¹ c`, and the
genetic gain from truncation selection on an index. The theorems are in
`Domains.Biology.StatisticalGenetics.SmithHazelIndex`.

## References

* L. N. Hazel, *The genetic basis for constructing selection indexes*, Genetics 28 (1943)
  476–490, equations (1)–(8) and pp. 486–487.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix

namespace SmithHazel

/-- A Smith–Hazel model on `n` traits under the measure `μ`: measurable random vectors of
additive breeding values and residuals whose coordinates are in `L²(μ)`, with every additive
coordinate uncorrelated with every residual coordinate and a positive definite phenotypic
covariance matrix `(cov[A_i + E_i, A_j + E_j; μ])`, together with economic weights. -/
structure Model (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- Additive breeding values by trait. -/
  additive : Ω → Fin n → ℝ
  /-- Residuals by trait. -/
  residual : Ω → Fin n → ℝ
  /-- Relative economic weights. -/
  economic : Fin n → ℝ
  /-- The additive breeding values are measurable. -/
  measurable_additive : Measurable additive
  /-- The residuals are measurable. -/
  measurable_residual : Measurable residual
  /-- Every additive coordinate is square integrable. -/
  memLp_additive : ∀ i, MemLp (fun ω => additive ω i) 2 μ
  /-- Every residual coordinate is square integrable. -/
  memLp_residual : ∀ i, MemLp (fun ω => residual ω i) 2 μ
  /-- Every additive coordinate is uncorrelated with every residual coordinate. -/
  orthogonal : ∀ i j, cov[fun ω => additive ω i, fun ω => residual ω j; μ] = 0
  /-- The phenotypic covariance matrix is positive definite. -/
  posDef : Matrix.PosDef (fun i j => cov[fun ω => additive ω i + residual ω i,
    fun ω => additive ω j + residual ω j; μ] : Matrix (Fin n) (Fin n) ℝ)

/-- The phenotype vector `X = A + E`, the sum of additive breeding values and residuals. -/
def Model.phenotype {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (ω : Ω) : Fin n → ℝ := M.additive ω + M.residual ω

/-- The aggregate breeding value `H = a ⬝ᵥ A`, the economic objective of Hazel's equation (2). -/
noncomputable def Model.aggregate {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (ω : Ω) : ℝ := M.economic ⬝ᵥ M.additive ω

/-- The index `I_b = b ⬝ᵥ X` with coefficient vector `b`, Hazel's equation (4). -/
noncomputable def Model.index {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b : Fin n → ℝ) (ω : Ω) : ℝ := b ⬝ᵥ M.phenotype ω

/-- The phenotypic covariance matrix `P`, with entries `cov[X_i, X_j; μ]`. -/
noncomputable def Model.phenotypicCov {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => cov[fun ω => M.phenotype ω i, fun ω => M.phenotype ω j; μ]

/-- The additive genetic covariance matrix `G`, with entries `cov[A_i, A_j; μ]`. -/
noncomputable def Model.geneticCov {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => cov[fun ω => M.additive ω i, fun ω => M.additive ω j; μ]

/-- The residual covariance matrix, with entries `cov[E_i, E_j; μ]`. -/
noncomputable def Model.residualCov {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => cov[fun ω => M.residual ω i, fun ω => M.residual ω j; μ]

/-- The phenotype–objective covariance vector `c`, with entries `cov[X_i, H; μ]`. -/
noncomputable def Model.objectiveCov {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : Fin n → ℝ :=
  fun i => cov[fun ω => M.phenotype ω i, M.aggregate; μ]

/-- The index coefficients `w = P⁻¹ c`, the regression coefficients of `H` on `X`. -/
noncomputable def Model.regressionWeights {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : Fin n → ℝ := M.phenotypicCov⁻¹ *ᵥ M.objectiveCov

/-- Hazel's standardized coefficient `β_i = w_i σ_{X_i} / σ_H` of trait `i` (meaningful when
`Var[H; μ] > 0`). -/
noncomputable def Model.beta {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (i : Fin n) : ℝ :=
  M.regressionWeights i * populationSD μ (fun ω => M.phenotype ω i) / populationSD μ M.aggregate

/-- The narrow-sense heritability `G_ii / P_ii` of trait `i`. -/
noncomputable def Model.heritability {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (i : Fin n) : ℝ := M.geneticCov i i / M.phenotypicCov i i

/-- The totalized truncation-selection shift
`conditionalMeanShift μ M.aggregate (standardizedUpperEvent μ (M.index b) z)`, i.e., the integral
of `H` under the scaled restriction `μ[|s]` on `s = {ω | μ[I_b] + z * σ_{I_b} ≤ I_b ω}`
(normalized when `0 < μ s < ∞`, and zero when `μ s = 0` or `μ s = ∞`) minus the unnormalized
integral `∫ H dμ`. When `μ` is a probability measure, `H` is integrable, and `s` is measurable
with positive mass, this equals the genetic gain: the mean of `H` among selected outcomes minus
the population mean of `H`. -/
noncomputable def Model.gain {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b : Fin n → ℝ) (z : ℝ) : ℝ :=
  conditionalMeanShift μ M.aggregate (standardizedUpperEvent μ (M.index b) z)

/-- **Rescaling the index coefficients.** For any measure `μ`, any Smith–Hazel model `M` under
`μ`, any coefficient vector `b`, any threshold `z` and any `k > 0`, the standardized upper event
of `M.index (k • b)` at `z` equals that of `M.index b`. -/
theorem Model.upperEvent_smul {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b : Fin n → ℝ) (z : ℝ) {k : ℝ} (hk : 0 < k) :
    standardizedUpperEvent μ (M.index (k • b)) z =
      standardizedUpperEvent μ (M.index b) z := by
  have h : M.index (k • b) = fun ω => k * M.index b ω := by
    funext ω
    exact smul_dotProduct k b (M.phenotype ω)
  rw [h]
  exact standardizedUpperEvent_const_mul (μ := μ) (M.index b) z hk

/-- **Reversing the index coefficients.** For any measure `μ`, any Smith–Hazel model `M` under
`μ`, any coefficient vector `b` and any threshold `z`, the standardized upper event of
`M.index (-b)` at `z` is the lower event
`{ω | M.index b ω ≤ μ[M.index b] - z * populationSD μ (M.index b)}`. -/
theorem Model.upperEvent_neg {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b : Fin n → ℝ) (z : ℝ) :
    standardizedUpperEvent μ (M.index (-b)) z =
      {ω | M.index b ω ≤ μ[M.index b] - z * populationSD μ (M.index b)} := by
  have h : M.index (-b) = fun ω => -M.index b ω := by
    funext ω
    exact neg_dotProduct b (M.phenotype ω)
  rw [h]
  exact standardizedUpperEvent_neg μ (M.index b) z

/-- **Positive phenotypic variances.** For any measure `μ`, any Smith–Hazel model `M` under `μ`
and any trait `i`, the phenotype `X_i` has positive variance `Var[X_i; μ] > 0`. -/
theorem Model.variance_phenotype_pos {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (i : Fin n) : 0 < Var[fun ω => M.phenotype ω i; μ] := by
  have hm : Measurable (fun ω => M.phenotype ω i) :=
    ((measurable_pi_apply i).comp M.measurable_additive).add
      ((measurable_pi_apply i).comp M.measurable_residual)
  rw [← covariance_self hm.aemeasurable]
  exact M.posDef.diag_pos (i := i)

end SmithHazel
