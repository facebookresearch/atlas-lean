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
# Smith–Hazel selection index

The additive breeding values and residuals define the phenotype, the economic
objective, and all the population covariances of the index.

L. N. Hazel, *The genetic basis for constructing selection indexes*,
Genetics 28 (1943), 476–490, equations (1)–(8) and pp. 486–487.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix

namespace SmithHazel

/-- The additive and residual random vectors, with finite coordinate second
moments, orthogonality across the two vectors, and nonsingular phenotype variation. -/
structure Model (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- Additive breeding values by trait. -/
  additive : Ω → Fin n → ℝ
  /-- Residuals by trait. -/
  residual : Ω → Fin n → ℝ
  /-- Relative economic weights. -/
  economic : Fin n → ℝ
  measurable_additive : Measurable additive
  measurable_residual : Measurable residual
  memLp_additive : ∀ i, MemLp (fun ω => additive ω i) 2 μ
  memLp_residual : ∀ i, MemLp (fun ω => residual ω i) 2 μ
  orthogonal : ∀ i j, cov[fun ω => additive ω i, fun ω => residual ω j; μ] = 0
  posDef : Matrix.PosDef (fun i j => cov[fun ω => additive ω i + residual ω i,
    fun ω => additive ω j + residual ω j; μ] : Matrix (Fin n) (Fin n) ℝ)

/-- Phenotype is the sum of additive value and residual. -/
def Model.phenotype {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (ω : Ω) : Fin n → ℝ := M.additive ω + M.residual ω

/-- Aggregate breeding value `H`, the economic objective in Hazel's equation (2). -/
noncomputable def Model.aggregate {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (ω : Ω) : ℝ := M.economic ⬝ᵥ M.additive ω

/-- Linear phenotype score `I_b`, Hazel's equation (4). -/
noncomputable def Model.index {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b : Fin n → ℝ) (ω : Ω) : ℝ := b ⬝ᵥ M.phenotype ω

/-- The actual phenotypic covariance matrix `P`. -/
noncomputable def Model.phenotypicCov {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => cov[fun ω => M.phenotype ω i, fun ω => M.phenotype ω j; μ]

/-- The actual additive genetic covariance matrix `G`. -/
noncomputable def Model.geneticCov {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => cov[fun ω => M.additive ω i, fun ω => M.additive ω j; μ]

/-- The actual residual covariance matrix. -/
noncomputable def Model.residualCov {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => cov[fun ω => M.residual ω i, fun ω => M.residual ω j; μ]

/-- The covariance vector `c` of each phenotype coordinate with aggregate breeding value. -/
noncomputable def Model.objectiveCov {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : Fin n → ℝ :=
  fun i => cov[fun ω => M.phenotype ω i, M.aggregate; μ]

/-- Canonical regression coefficients, defined by the inverse phenotype covariance. -/
noncomputable def Model.regressionWeights {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : Fin n → ℝ := M.phenotypicCov⁻¹ *ᵥ M.objectiveCov

/-- Hazel's standardized coefficient, using the canonical regression coefficients.
Used where the aggregate variance is positive. -/
noncomputable def Model.beta {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (i : Fin n) : ℝ :=
  M.regressionWeights i * populationSD μ (fun ω => M.phenotype ω i) / populationSD μ M.aggregate

/-- Narrow-sense heritability of one trait, the additive variance over the phenotype variance. -/
noncomputable def Model.heritability {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (i : Fin n) : ℝ := M.geneticCov i i / M.phenotypicCov i i

/-- Genetic gain is the selected mean of the aggregate breeding value minus
its population mean. The event fixes the threshold in index standard deviations. -/
noncomputable def Model.gain {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b : Fin n → ℝ) (z : ℝ) : ℝ :=
  conditionalMeanShift μ M.aggregate (standardizedUpperEvent μ (M.index b) z)

/-- Standardized upper-tail membership is invariant under positive rescaling of the weights. -/
theorem Model.upperEvent_smul {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b : Fin n → ℝ) (z : ℝ) {k : ℝ} (hk : 0 < k) :
    standardizedUpperEvent μ (M.index (k • b)) z =
      standardizedUpperEvent μ (M.index b) z := by
  have h : M.index (k • b) = fun ω => k * M.index b ω := by
    funext ω
    exact smul_dotProduct k b (M.phenotype ω)
  rw [h]
  exact standardizedUpperEvent_const_mul (μ := μ) (M.index b) z hk

/-- Reversing the coefficient vector selects the reflected lower tail. -/
theorem Model.upperEvent_neg {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b : Fin n → ℝ) (z : ℝ) :
    standardizedUpperEvent μ (M.index (-b)) z =
      {ω | M.index b ω ≤ μ[M.index b] - z * populationSD μ (M.index b)} := by
  have h : M.index (-b) = fun ω => -M.index b ω := by
    funext ω
    exact neg_dotProduct b (M.phenotype ω)
  rw [h]
  exact standardizedUpperEvent_neg μ (M.index b) z

/-- The actual variance of each phenotype coordinate is positive. -/
theorem Model.variance_phenotype_pos {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (i : Fin n) : 0 < Var[fun ω => M.phenotype ω i; μ] := by
  have hm : Measurable (fun ω => M.phenotype ω i) :=
    ((measurable_pi_apply i).comp M.measurable_additive).add
      ((measurable_pi_apply i).comp M.measurable_residual)
  rw [← covariance_self hm.aemeasurable]
  exact M.posDef.diag_pos (i := i)

end SmithHazel
