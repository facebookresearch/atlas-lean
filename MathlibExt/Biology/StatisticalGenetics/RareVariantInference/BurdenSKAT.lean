/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.BOLTLMM
public import MathlibExt.Biology.StatisticalGenetics.KinshipIBD
public import MathlibExt.Probability.Statistics.GeneralizedLeastSquares
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# SKAT: the variance-component score test for rare variants, with relatedness

**Method.** This file treats the **SKAT variance-component score test** (Wu et al. 2011), not
the burden test. A burden test collapses a region into the single score `∑ⱼ wⱼ Sⱼ`; SKAT
instead sums the squared single-variant scores, `Q = ∑ⱼ wⱼ Sⱼ²`.

**Model.** `n` individuals, `q` covariates, `m` variants in a region. The phenotype is
`y = X α + G β + g + ε`, where `X` holds the covariates, `G` the minor-allele counts, `g` a
polygenic effect with covariance `σ_g² Φ`, and `ε` noise with covariance `σ_e² I`. For a pedigree
`Φ = 2 φ`, where `φ` is the tabular kinship `Kinship.Pedigree.kinship` of the merged `Kinship`
and `KinshipIBD` files (`pedigreeRelationship`). The variant effects are random with mean `0`
and covariance `τ W`, `W = diag w`, so `Cov y = Σ₀ + τ K` with `Σ₀ = σ_g² Φ + σ_e² I`
(`nullCov`) and `K = G W Gᵀ` (`skatKernel`). The null hypothesis is `H₀ : τ = 0`. Gaussian
phenotypes are encoded by Mathlib's `multivariateGaussian (X α) V'`, with `V' = Σ₀` under `H₀`
and `V' = Σ₀ + τ K` (`altCov`) under the alternative.

**Statistic.** With the null GLS fit `α̂ = (Xᵀ Σ₀⁻¹ X)⁻¹ Xᵀ Σ₀⁻¹ y`, the statistic is
`Q = (y - X α̂)ᵀ Σ₀⁻¹ K Σ₀⁻¹ (y - X α̂) = (P y)ᵀ K (P y)`, where
`P = Σ₀⁻¹ - Σ₀⁻¹ X (Xᵀ Σ₀⁻¹ X)⁻¹ Xᵀ Σ₀⁻¹` (`skatQ`, `projP`).

## Main results

* `map_skatQ_multivariateGaussian`: **the law of `Q` is a weighted chi-square mixture.** If
  `y ~ N(X α, V')`, then `Q ~ ∑ₖ λₖ χ²₁`, where `λ` are the eigenvalues of
  `A = (P V'^{1/2})ᵀ K (P V'^{1/2})` (`skatMixtureMatrix`). The proof diagonalises `A`
  in an orthonormal eigenbasis (`stdGaussian_map_inner_eq_weightedChiSq`). `V' = Σ₀` gives the
  null law, and `V' = Σ₀ + τ K` the law under the alternative.
* `eigenvalues_skatMixtureMatrix_nonneg`: the weights are nonnegative when `w ≥ 0`.
* `skatQ_add_covariates`: the covariate effects `X α` drop out of `Q` (`P X = 0`).
* `skatQ_eq_sum_variantScore`: `Q = ∑ⱼ wⱼ Sⱼ²`, with `Sⱼ = gⱼᵀ P y`.
* `integral_skatQ_null`: `𝔼₀ Q = tr(K P) = ∑ₖ λₖ`, so the centred score `Q - tr(K P)` has
  null mean `0`.

## Boundary cases

* **Variance component on the boundary, `τ = 0`.** `H₀` sits on the boundary of
  `τ ∈ [0, ∞)`. The statistic needs only the null fit, satisfies `Q ≥ 0`
  (`skatQ_nonneg`, `map_skatQ_null_Iio`), and is used one-sided, rejecting for large `Q`.
  `integral_skatQ_altCov` gives `𝔼_τ Q = tr(K P) + τ tr(K P K Pᵀ)` with a nonnegative slope
  (`trace_skatKernel_mul_projP_nonneg`), so `integral_skatQ_null_le_altCov` says the mean is
  smallest at the boundary.
* **Rare alleles.** `betaWeight` is the default weight `wⱼ = Beta(MAFⱼ; 1, 25)²`. It decreases
  in the MAF (`betaWeight_antitoneOn`) and attains its maximum `625` at `MAF = 0`
  (`betaWeight_zero`, `betaWeight_le`). The calibration splits over variants
  (`integral_skatQ_null_eq_sum`): `𝔼₀ Q = ∑ⱼ wⱼ gⱼᵀ P gⱼ`. Informally, a rare variant has a
  sparse column, so its quadratic form `gⱼᵀ P gⱼ` is small, and the large weight compensates.
* **Zero minor-allele count.** A variant with no carriers has score `0`
  (`variantScore_eq_zero_of_col`) and is invisible to `Q`, whatever its weight
  (`skatQ_update_of_col`). With no carriers at any variant, `Q ≡ 0`, every weight vanishes
  (`eigenvalues_skatMixtureMatrix_zero_genotype`), and the law degenerates to the point mass at
  `0` (`map_skatQ_zero_genotype`).
* **Singular kinship.** With noise (`σ_e² > 0`), a singular positive semidefinite `Φ` still
  gives a positive definite `Σ₀` (`posDef_nullCov`), and every result above applies. The pedigree
  relationship matrix is positive semidefinite (`posSemidef_pedigreeRelationship`, from
  `posSemidef_two_kinship`). Without noise, a null vector of `Φ` makes `Σ₀` singular
  (`det_nullCov_zero`), so the phenotype lies on a hyperplane almost surely
  (`ae_dotProduct_sub_eq_zero`). The GLS formula then has no inverse to use: Mathlib's
  convention `Σ₀⁻¹ = 0` makes `P = 0` and `Q ≡ 0` (`projP_of_det_eq_zero`,
  `skatQ_of_det_eq_zero`).

## Source contract

M. C. Wu, S. Lee, T. Cai, Y. Li, M. Boehnke, X. Lin, *Rare-variant association testing for
sequencing data with the sequence kernel association test*, Am. J. Hum. Genet. 89 (2011),
82–93. From this paper we formalize, for the linear (continuous-trait) SKAT:
1. the statistic `Q = (y - μ̂)ᵀ K (y - μ̂)` with `K = G W Gᵀ`. With `Σ₀ = σ² I` our `skatQ` is
   their `Q` multiplied by the known constant `σ⁻⁴`;
2. the null law `Q ~ ∑ λⱼ χ²₁` (their eq. (6), with `P₀` defined in Appendix A), with weights
   from the eigenvalues of the projected kernel and the variance components treated as known;
3. the default weights `√wⱼ = Beta(MAFⱼ; 1, 25)`.

Wu et al. state the weights as the eigenvalues of `P₀^{1/2} K P₀^{1/2}`, where
`P₀ = V - V X (Xᵀ V X)⁻¹ Xᵀ V` is the residual covariance; under `Σ₀ = σ² I` it is `σ⁴ P`. We use
`(P Σ₀^{1/2})ᵀ K (P Σ₀^{1/2})` instead. The two spectra agree up to the factor `σ⁴`, through the
`AB`/`BA` exchange and `P Σ₀ P = P` (`projP_mul_mul_projP`), matching the factor `σ⁻⁴` on `Q`
in item 1, but this identification is not formalized. Nor are: plug-in estimation of `σ²` or
of the variance components, p-value computation (Davies' method), the logistic model for binary
traits, SKAT-O, and the burden test. The kinship covariance `Σ₀ = σ_g² · 2φ + σ_e² I` is the
family-sample extension of H. Chen, J. B. Meigs, J. Dupuis, *Sequence kernel association test
for quantitative traits in family samples*, Genet. Epidemiol. 37 (2013), 196–204; it is used
here only as the model, not as a second source contract.

## API-00 receipt (base `origin/main` 53666a3c1)

Reuse search of `MathlibExt`, `WantedExt`, `CSLibExt` and the pinned Mathlib for SKAT, burden
tests, variance-component score tests and weighted chi-square mixtures found nothing. Reused:
Mathlib's `multivariateGaussian`, `stdGaussian_eq_map_pi_orthonormalBasis`,
`Matrix.IsHermitian.eigenvectorBasis` / `eigenvalues` / `trace_eq_sum_eigenvalues`, and
`CFC.sqrt`; the repository's `GeneralizedLeastSquares.glsMatrix`, `Kinship.Pedigree.kinship`,
`Relatedness.IBDModel` and `Kinship.Pedigree.ibdModel`. The repository's Cochran theorem covers
only projections (`χ²_r`), not general weights, so it is not reused. `BOLTLMM.Model.V` and
`BOLTLMM.Model.proj` are the same `Σ₀` and `P` as `nullCov` and `projP` (bridges `nullCov_eq_V`,
`projP_eq_proj`), and `Model.posDef_V`, `Model.proj_mul_X` and `Model.proj_mul_V_mul_proj` match
`posDef_nullCov`, `projP_mul_self` and `projP_mul_mul_projP`. They are not used as the base API
because `Model` requires `σ_e² > 0` and index type `Fin n`, which excludes the noise-free
singular-kinship case treated here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder
open MathlibExt.Probability.Statistics.GeneralizedLeastSquares

namespace MathlibExt.Biology.StatisticalGenetics.BurdenSKAT

section WeightedChiSq

variable {k : Type*} [Fintype k]

/-- The weighted chi-square law `∑ⱼ λⱼ ξⱼ²` with `ξ₁, …, ξₖ` independent standard normal. -/
noncomputable def weightedChiSq (lam : k → ℝ) : Measure ℝ :=
  (Measure.pi fun _ : k => gaussianReal 0 1).map fun ξ => ∑ j, lam j * ξ j ^ 2

instance (lam : k → ℝ) : IsProbabilityMeasure (weightedChiSq lam) :=
  by unfold weightedChiSq; infer_instance

/-- With all weights zero the weighted chi-square law is the point mass at `0`. -/
theorem weightedChiSq_zero : weightedChiSq (0 : k → ℝ) = Measure.dirac 0 := by
  simp [weightedChiSq]

/-- **Quadratic forms of a standard Gaussian vector** (spectral form): if `b` is an orthonormal
eigenbasis of `A` with eigenvalues `lam`, then `⟪Z, A Z⟫` has the weighted chi-square law with
weights `lam`. -/
theorem stdGaussian_map_inner_eq_weightedChiSq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) (lam : n → ℝ)
    (hb : ∀ j, A *ᵥ ⇑(b j) = lam j • ⇑(b j)) :
    (stdGaussian (EuclideanSpace ℝ n)).map (fun z => ⟪z, toEuclideanCLM (𝕜 := ℝ) A z⟫) =
      weightedChiSq lam := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, Measure.map_map (by fun_prop) (by fun_prop)]
  unfold weightedChiSq
  congr 1
  funext x
  have hAb : ∀ j, toEuclideanCLM (𝕜 := ℝ) A (b j) = lam j • b j := by
    intro j
    apply (WithLp.equiv 2 _).injective
    simp [hb j]
  simp only [Function.comp_apply, map_sum, map_smul, hAb, smul_smul]
  rw [b.orthonormal.inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [conj_trivial]
  ring

/-- The mean of the weighted chi-square law is the sum of the weights. -/
theorem integral_weightedChiSq (lam : k → ℝ) : ∫ x, x ∂weightedChiSq lam = ∑ j, lam j := by
  have hsq : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    rw [← variance_of_integral_eq_zero (X := fun x : ℝ => x) aemeasurable_id'
      integral_id_gaussianReal]
    exact variance_fun_id_gaussianReal
  have hmap : ∀ j, (Measure.pi fun _ : k => gaussianReal 0 1).map (Function.eval j) =
      gaussianReal 0 1 := fun j =>
    (measurePreserving_eval (fun _ : k => gaussianReal 0 1) j).map_eq
  have hint : ∀ j, Integrable (fun ξ : k → ℝ => ξ j ^ 2)
      (Measure.pi fun _ => gaussianReal 0 1) := by
    intro j
    have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal 2).integrable_sq
    rw [← hmap j] at h2
    exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
      (measurable_pi_apply j).aemeasurable).1 h2
  have hcoord : ∀ j, ∫ ξ : k → ℝ, ξ j ^ 2 ∂(Measure.pi fun _ => gaussianReal 0 1) = 1 := by
    intro j
    have h := integral_map (μ := Measure.pi fun _ : k => gaussianReal 0 1) (φ := Function.eval j)
      (f := fun x : ℝ => x ^ 2) (measurable_pi_apply j).aemeasurable
      (continuous_pow 2).aestronglyMeasurable
    rw [hmap j, hsq] at h
    exact h.symm
  rw [weightedChiSq, integral_map (f := fun x : ℝ => x)
    (by fun_prop : Measurable fun ξ : k → ℝ => ∑ j, lam j * ξ j ^ 2).aemeasurable (by fun_prop),
    integral_finsetSum _ fun j _ => (hint j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, hcoord j, mul_one]

/-- With nonnegative weights the weighted chi-square law is carried by `[0, ∞)`. -/
theorem weightedChiSq_Iio_eq_zero {lam : k → ℝ} (hlam : 0 ≤ lam) :
    weightedChiSq lam (Set.Iio 0) = 0 := by
  rw [weightedChiSq, Measure.map_apply (by fun_prop) measurableSet_Iio]
  convert measure_empty (μ := Measure.pi fun _ : k => gaussianReal 0 1)
  ext ξ
  simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hlam j) (sq_nonneg _)

end WeightedChiSq

section Model

variable {n q m : Type*} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q] [Fintype m]
  [DecidableEq m]

/-- The null phenotypic covariance of the polygenic mixed model with relatedness:
`Σ₀ = σ_g² Φ + σ_e² I`, for a relationship matrix `Φ` (for a pedigree, twice the kinship). -/
def nullCov (Φ : Matrix n n ℝ) (σg2 σe2 : ℝ) : Matrix n n ℝ := σg2 • Φ + σe2 • 1

/-- The weighted linear SKAT kernel `K = G W Gᵀ`, `W = diag w`, for the genotype matrix `G`
(individuals × variants, minor-allele counts) and variant weights `w`. -/
def skatKernel (G : Matrix n m ℝ) (w : m → ℝ) : Matrix n n ℝ := G * diagonal w * Gᵀ

/-- The phenotypic covariance under the variance-component alternative: the random variant
effects `β ~ (0, τ W)` add `τ K` to the null covariance `V`. -/
def altCov (V : Matrix n n ℝ) (G : Matrix n m ℝ) (w : m → ℝ) (τ : ℝ) : Matrix n n ℝ :=
  V + τ • skatKernel G w

/-- The null-model GLS residual `y - X α̂`, with `α̂ = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y`. -/
noncomputable def glsResidual (X : Matrix n q ℝ) (V : Matrix n n ℝ) (y : n → ℝ) : n → ℝ :=
  y - X *ᵥ (glsMatrix X V *ᵥ y)

/-- The SKAT variance-component score statistic
`Q = (y - X α̂)ᵀ V⁻¹ K V⁻¹ (y - X α̂)` (Wu et al. 2011, eq. (3), with the null covariance `V`
in place of `σ² I`). -/
noncomputable def skatQ (X : Matrix n q ℝ) (V : Matrix n n ℝ) (G : Matrix n m ℝ) (w : m → ℝ)
    (y : n → ℝ) : ℝ :=
  (V⁻¹ *ᵥ glsResidual X V y) ⬝ᵥ skatKernel G w *ᵥ (V⁻¹ *ᵥ glsResidual X V y)

/-- The null projection `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`. -/
noncomputable def projP (X : Matrix n q ℝ) (V : Matrix n n ℝ) : Matrix n n ℝ :=
  V⁻¹ - V⁻¹ * X * glsMatrix X V

/-- The single-variant score statistics `Sⱼ = gⱼᵀ P y`, `gⱼ` the genotype column of variant
`j`. -/
noncomputable def variantScore (X : Matrix n q ℝ) (V : Matrix n n ℝ) (G : Matrix n m ℝ)
    (y : n → ℝ) : m → ℝ :=
  Gᵀ *ᵥ (projP X V *ᵥ y)

/-- The matrix whose eigenvalues are the mixture weights of `Q` when the phenotype has
covariance `V'`: `A = (P V'^{1/2})ᵀ K (P V'^{1/2})`, with `P` built from the null covariance
`V`. Under the null hypothesis `V' = V`. -/
noncomputable def skatMixtureMatrix (X : Matrix n q ℝ) (V : Matrix n n ℝ) (G : Matrix n m ℝ)
    (w : m → ℝ) (V' : Matrix n n ℝ) : Matrix n n ℝ :=
  (projP X V * CFC.sqrt V')ᵀ * skatKernel G w * (projP X V * CFC.sqrt V')

variable {X : Matrix n q ℝ} {V : Matrix n n ℝ} {G : Matrix n m ℝ} {w : m → ℝ}

/-- `V⁻¹ (y - X α̂) = P y`. -/
theorem inv_mulVec_glsResidual (y : n → ℝ) :
    V⁻¹ *ᵥ glsResidual X V y = projP X V *ᵥ y := by
  simp [glsResidual, projP, mulVec_sub, sub_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- `Q = (P y)ᵀ K (P y)`. -/
theorem skatQ_eq (y : n → ℝ) :
    skatQ X V G w y = (projP X V *ᵥ y) ⬝ᵥ skatKernel G w *ᵥ (projP X V *ᵥ y) := by
  rw [skatQ, inv_mulVec_glsResidual]

omit [DecidableEq n] in
/-- `uᵀ K u = ∑ⱼ wⱼ (gⱼᵀ u)²`. -/
theorem dotProduct_skatKernel_mulVec (u : n → ℝ) :
    u ⬝ᵥ skatKernel G w *ᵥ u = ∑ j, w j * (Gᵀ *ᵥ u) j ^ 2 := by
  rw [skatKernel, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
    dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_diagonal]
  ring

/-- **SKAT as a weighted sum of squared single-variant scores**: `Q = ∑ⱼ wⱼ Sⱼ²`. -/
theorem skatQ_eq_sum_variantScore (y : n → ℝ) :
    skatQ X V G w y = ∑ j, w j * variantScore X V G y j ^ 2 := by
  rw [skatQ_eq, dotProduct_skatKernel_mulVec, variantScore]

/-- The null projection annihilates the covariates: `P X = 0`. -/
theorem projP_mul_self (hX : IsUnit (Xᵀ * V⁻¹ * X)) : projP X V * X = 0 := by
  rw [projP, Matrix.sub_mul, Matrix.mul_assoc (V⁻¹ * X), glsMatrix_mul_self hX, Matrix.mul_one,
    sub_self]

/-- **Covariate effects drop out of `Q`**: `Q(X α + y) = Q(y)`. -/
theorem skatQ_add_covariates (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ) (y : n → ℝ) :
    skatQ X V G w (X *ᵥ α + y) = skatQ X V G w y := by
  simp only [skatQ_eq, mulVec_add, mulVec_mulVec, projP_mul_self hX, zero_mulVec, zero_add]

omit [Fintype n] [DecidableEq n] in
/-- The SKAT kernel is symmetric. -/
theorem isHermitian_skatKernel : (skatKernel G w).IsHermitian := by
  simp [IsHermitian, skatKernel, conjTranspose_eq_transpose_of_trivial, transpose_mul,
    Matrix.mul_assoc]

omit [Fintype n] [DecidableEq n] in
/-- With nonnegative weights the SKAT kernel is positive semidefinite. -/
theorem posSemidef_skatKernel [Finite n] (hw : 0 ≤ w) : (skatKernel G w).PosSemidef := by
  have := Fintype.ofFinite n
  simpa [skatKernel, conjTranspose_eq_transpose_of_trivial] using
    (PosSemidef.diagonal hw).mul_mul_conjTranspose_same G

/-- The mixture matrix is symmetric. -/
theorem isHermitian_skatMixtureMatrix (V' : Matrix n n ℝ) :
    (skatMixtureMatrix X V G w V').IsHermitian := by
  simpa [skatMixtureMatrix, conjTranspose_eq_transpose_of_trivial] using
    isHermitian_conjTranspose_mul_mul (projP X V * CFC.sqrt V') isHermitian_skatKernel

/-- With nonnegative variant weights the mixture weights are nonnegative. -/
theorem eigenvalues_skatMixtureMatrix_nonneg (hw : 0 ≤ w) (V' : Matrix n n ℝ) (j : n) :
    0 ≤ (isHermitian_skatMixtureMatrix (X := X) (V := V) (G := G) (w := w) V').eigenvalues j := by
  have h : (skatMixtureMatrix X V G w V').PosSemidef := by
    simpa [skatMixtureMatrix, conjTranspose_eq_transpose_of_trivial] using
      (posSemidef_skatKernel hw).conjTranspose_mul_mul_same (projP X V * CFC.sqrt V')
  exact h.eigenvalues_nonneg j

/-- `Q(X α + S z) = zᵀ (P S)ᵀ K (P S) z`. -/
private theorem skatQ_add_mulVec (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ) (S : Matrix n n ℝ)
    (z : n → ℝ) :
    skatQ X V G w (X *ᵥ α + S *ᵥ z) =
      z ⬝ᵥ ((projP X V * S)ᵀ * skatKernel G w * (projP X V * S)) *ᵥ z := by
  rw [skatQ_add_covariates hX, skatQ_eq, mulVec_mulVec]
  conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- `Q` is continuous in the phenotype. -/
theorem continuous_skatQ : Continuous (skatQ X V G w) := by
  unfold skatQ glsResidual
  fun_prop

/-- **The law of the SKAT statistic is a weighted chi-square mixture.** If the phenotype is
Gaussian, `y ~ N(X α, V')`, then `Q ~ ∑ⱼ λⱼ χ²₁` with `λ` the eigenvalues of
`A = (P V'^{1/2})ᵀ K (P V'^{1/2})`, `P` the null projection built from `V`. Taking `V' = V`
gives the null law; `V' = V + τ K` gives the law under the variance-component alternative. -/
theorem map_skatQ_multivariateGaussian (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ)
    (V' : Matrix n n ℝ) :
    (multivariateGaussian (toLp 2 (X *ᵥ α)) V').map (fun y => skatQ X V G w (ofLp y)) =
      weightedChiSq (isHermitian_skatMixtureMatrix (X := X) (V := V) (G := G) (w := w)
        V').eigenvalues := by
  set hA := isHermitian_skatMixtureMatrix (X := X) (V := V) (G := G) (w := w) V'
  rw [← stdGaussian_map_inner_eq_weightedChiSq _ hA.eigenvectorBasis _
    hA.mulVec_eigenvectorBasis, multivariateGaussian,
    Measure.map_map (by exact (continuous_skatQ.comp (PiLp.continuous_ofLp 2 _)).measurable)
      (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply, inner_toEuclideanCLM, ofLp_add,
    ofLp_toEuclideanCLM]
  exact skatQ_add_mulVec hX α _ _

/-! ### Weights and means -/

omit [DecidableEq n] in
/-- The kernel trace splits over variants: `tr(K N) = ∑ⱼ wⱼ gⱼᵀ N gⱼ`. -/
theorem trace_skatKernel_mul (N : Matrix n n ℝ) :
    trace (skatKernel G w * N) = ∑ j, w j * (Gᵀ * N * G) j j := by
  rw [skatKernel, Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  simp [trace, diagonal_mul, Matrix.mul_assoc]

/-- The total mixture weight is `∑ⱼ λⱼ = tr(K P V' Pᵀ)`. -/
theorem sum_eigenvalues_skatMixtureMatrix {V' : Matrix n n ℝ} (hV' : V'.PosSemidef) :
    ∑ j, (isHermitian_skatMixtureMatrix (X := X) (V := V) (G := G) (w := w) V').eigenvalues j =
      trace (skatKernel G w * (projP X V * V' * (projP X V)ᵀ)) := by
  have hS : (CFC.sqrt V')ᵀ = CFC.sqrt V' := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg V').posSemidef.isHermitian.eq
  have hSS : CFC.sqrt V' * CFC.sqrt V' = V' := CFC.sqrt_mul_sqrt_self V' hV'.nonneg
  have h := (isHermitian_skatMixtureMatrix (X := X) (V := V) (G := G) (w := w)
    V').trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [← h, skatMixtureMatrix, trace_mul_comm, ← Matrix.mul_assoc, trace_mul_comm]
  congr 2
  rw [transpose_mul, hS, Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt V'), hSS,
    Matrix.mul_assoc]

/-- The mean of `Q` under `y ~ N(X α, V')`: `𝔼 Q = tr(K P V' Pᵀ)`. -/
theorem integral_skatQ_multivariateGaussian (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ)
    {V' : Matrix n n ℝ} (hV' : V'.PosSemidef) :
    ∫ y, skatQ X V G w (ofLp y) ∂multivariateGaussian (toLp 2 (X *ᵥ α)) V' =
      trace (skatKernel G w * (projP X V * V' * (projP X V)ᵀ)) := by
  have h1 : ∫ y, skatQ X V G w (ofLp y) ∂multivariateGaussian (toLp 2 (X *ᵥ α)) V' =
      ∫ x, x ∂((multivariateGaussian (toLp 2 (X *ᵥ α)) V').map
        (fun y => skatQ X V G w (ofLp y))) :=
    (integral_map (f := fun x : ℝ => x)
      (continuous_skatQ.comp (PiLp.continuous_ofLp 2 _)).aemeasurable (by fun_prop)).symm
  rw [h1, map_skatQ_multivariateGaussian hX, integral_weightedChiSq,
    sum_eigenvalues_skatMixtureMatrix hV']

/-- The null projection is symmetric. -/
theorem transpose_projP (hV : V.PosDef) : (projP X V)ᵀ = projP X V := by
  have hVt : Vᵀ = V := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hV.isHermitian.eq
  have hVi : (V⁻¹)ᵀ = V⁻¹ := by rw [transpose_nonsing_inv, hVt]
  have hC : ((Xᵀ * V⁻¹ * X)⁻¹)ᵀ = (Xᵀ * V⁻¹ * X)⁻¹ := by
    rw [transpose_nonsing_inv, transpose_mul, transpose_mul, hVi, transpose_transpose,
      Matrix.mul_assoc]
  simp only [projP, glsMatrix, transpose_sub, transpose_mul, hVi, hC, transpose_transpose]
  simp only [Matrix.mul_assoc]

/-- The null projection is a `V`-generalized inverse: `P V P = P`. -/
theorem projP_mul_mul_projP (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X)) :
    projP X V * V * projP X V = projP X V := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hV.isUnit
  have h1 : ∀ Z : Matrix n n ℝ, V * (V⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]
  have h2 : ∀ Z : Matrix n n ℝ, V⁻¹ * (V * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.one_mul]
  have h3 : ∀ Z : Matrix q n ℝ, glsMatrix X V * (X * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, glsMatrix_mul_self hX, Matrix.one_mul]
  simp only [projP, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h1, h3,
    mul_nonsing_inv _ hd, nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.one_mul]
  abel

/-- **The null mean of `Q` is `tr(P K)`**: under `H₀` (`y ~ N(X α, V)`) the mixture weights sum
to `tr(K P)`, so the centred score `Q - tr(K P)` has mean zero. -/
theorem integral_skatQ_null (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ) :
    ∫ y, skatQ X V G w (ofLp y) ∂multivariateGaussian (toLp 2 (X *ᵥ α)) V =
      trace (skatKernel G w * projP X V) := by
  rw [integral_skatQ_multivariateGaussian hX α hV.posSemidef, transpose_projP hV,
    projP_mul_mul_projP hV hX]

/-! ### Boundary case: the variance component at `τ = 0` -/

/-- `Q ≥ 0`: the score test of `τ = 0` against `τ > 0` is one-sided. -/
theorem skatQ_nonneg (hw : 0 ≤ w) (y : n → ℝ) : 0 ≤ skatQ X V G w y := by
  rw [skatQ_eq_sum_variantScore]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)

omit [Fintype n] [DecidableEq n] in
/-- At `τ = 0` the alternative covariance is the null covariance. -/
@[simp] theorem altCov_zero (V : Matrix n n ℝ) : altCov V G w 0 = V := by simp [altCov]

/-- The mean excess `tr(K P K Pᵀ) ≥ 0` that a variance component adds to `𝔼 Q`. -/
theorem trace_skatKernel_mul_projP_nonneg (hw : 0 ≤ w) :
    0 ≤ trace (skatKernel G w * (projP X V * skatKernel G w * (projP X V)ᵀ)) := by
  rw [trace_skatKernel_mul]
  have hN : (projP X V * skatKernel G w * (projP X V)ᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      (posSemidef_skatKernel hw).mul_mul_conjTranspose_same (projP X V)
  have hM : (Gᵀ * (projP X V * skatKernel G w * (projP X V)ᵀ) * G).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hN.conjTranspose_mul_mul_same G
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hw j) hM.diag_nonneg

/-- **The mean of `Q` along the variance-component alternative**: for `τ ≥ 0`,
`𝔼_τ Q = tr(K P) + τ tr(K P K Pᵀ)`, an affine function of `τ` with nonnegative slope. -/
theorem integral_skatQ_altCov (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X)) (hw : 0 ≤ w)
    {τ : ℝ} (hτ : 0 ≤ τ) (α : q → ℝ) :
    ∫ y, skatQ X V G w (ofLp y) ∂multivariateGaussian (toLp 2 (X *ᵥ α)) (altCov V G w τ) =
      trace (skatKernel G w * projP X V) +
        τ * trace (skatKernel G w * (projP X V * skatKernel G w * (projP X V)ᵀ)) := by
  have hV' : (altCov V G w τ).PosSemidef :=
    hV.posSemidef.add ((posSemidef_skatKernel hw).smul hτ)
  rw [integral_skatQ_multivariateGaussian hX α hV', altCov, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_add, trace_add, ← integral_skatQ_multivariateGaussian hX α hV.posSemidef,
    integral_skatQ_null hV hX α, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul,
    smul_eq_mul]

/-- **Boundary behaviour at `τ = 0`**: the null mean is the smallest mean on `τ ≥ 0`, so
departures from the boundary `τ = 0` only push `Q` up and the test rejects for large `Q`. -/
theorem integral_skatQ_null_le_altCov (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X))
    (hw : 0 ≤ w) {τ : ℝ} (hτ : 0 ≤ τ) (α : q → ℝ) :
    ∫ y, skatQ X V G w (ofLp y) ∂multivariateGaussian (toLp 2 (X *ᵥ α)) V ≤
      ∫ y, skatQ X V G w (ofLp y) ∂multivariateGaussian (toLp 2 (X *ᵥ α)) (altCov V G w τ) := by
  rw [integral_skatQ_altCov hV hX hw hτ, integral_skatQ_null hV hX]
  exact le_add_of_nonneg_right (mul_nonneg hτ (trace_skatKernel_mul_projP_nonneg hw))

/-- Under `H₀` the law of `Q` puts no mass below `0`. -/
theorem map_skatQ_null_Iio (hX : IsUnit (Xᵀ * V⁻¹ * X)) (hw : 0 ≤ w) (α : q → ℝ) :
    (multivariateGaussian (toLp 2 (X *ᵥ α)) V).map (fun y => skatQ X V G w (ofLp y))
      (Set.Iio 0) = 0 := by
  rw [map_skatQ_multivariateGaussian hX]
  exact weightedChiSq_Iio_eq_zero fun j => eigenvalues_skatMixtureMatrix_nonneg hw V j

/-! ### Boundary case: rare alleles -/

/-- The default SKAT variant weight of Wu et al. (2011): `√wⱼ = Beta(MAFⱼ; 1, 25)`, the
`Beta(1, 25)` density `25 (1 - MAF)²⁴`, so `wⱼ = (25 (1 - MAFⱼ)²⁴)²`. -/
noncomputable def betaWeight (maf : ℝ) : ℝ := (25 * (1 - maf) ^ 24) ^ 2

/-- The weight of a variant of vanishing frequency is `25² = 625`. -/
theorem betaWeight_zero : betaWeight 0 = 625 := by norm_num [betaWeight]

/-- A fixed variant (`MAF = 1`) has weight `0`. -/
theorem betaWeight_one : betaWeight 1 = 0 := by norm_num [betaWeight]

theorem betaWeight_nonneg (maf : ℝ) : 0 ≤ betaWeight maf := sq_nonneg _

/-- **Rarer variants get larger weights**: `betaWeight` is antitone on `[0, 1]`. -/
theorem betaWeight_antitoneOn : AntitoneOn betaWeight (Set.Icc 0 1) := by
  intro a ha b hb hab
  have h1 : 0 ≤ 1 - b := by linarith [hb.2]
  have h2 : (1 - b) ^ 24 ≤ (1 - a) ^ 24 := pow_le_pow_left₀ h1 (by linarith) 24
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- The weights are bounded by their rare-variant limit `625`. -/
theorem betaWeight_le {maf : ℝ} (h0 : 0 ≤ maf) (h1 : maf ≤ 1) : betaWeight maf ≤ 625 :=
  betaWeight_zero ▸ betaWeight_antitoneOn ⟨le_rfl, zero_le_one⟩ ⟨h0, h1⟩ h0

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- The variant contribution to the mean: `gⱼᵀ N gⱼ`. -/
theorem transpose_mul_mul_apply_self (N : Matrix n n ℝ) (j : m) :
    (Gᵀ * N * G) j j = (fun i => G i j) ⬝ᵥ N *ᵥ (fun i => G i j) := by
  simp only [mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The null mean splits over variants**: `𝔼₀ Q = ∑ⱼ wⱼ gⱼᵀ P gⱼ`. A variant enters the
calibration only through `wⱼ` times the quadratic form of its genotype column. -/
theorem integral_skatQ_null_eq_sum (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ) :
    ∫ y, skatQ X V G w (ofLp y) ∂multivariateGaussian (toLp 2 (X *ᵥ α)) V =
      ∑ j, w j * ((fun i => G i j) ⬝ᵥ projP X V *ᵥ (fun i => G i j)) := by
  rw [integral_skatQ_null hV hX, trace_skatKernel_mul]
  simp only [transpose_mul_mul_apply_self]

/-! ### Boundary case: zero minor-allele count -/

omit [Fintype m] [DecidableEq m] in
/-- A variant with no carriers has score `0`. -/
theorem variantScore_eq_zero_of_col {j : m} (hj : ∀ i, G i j = 0) (y : n → ℝ) :
    variantScore X V G y j = 0 := by
  simp [variantScore, mulVec, dotProduct, hj]

/-- **A variant with no carriers is invisible to `Q`**: changing its weight does not change the
statistic. -/
theorem skatQ_update_of_col {j : m} (hj : ∀ i, G i j = 0) (c : ℝ) (y : n → ℝ) :
    skatQ X V G (Function.update w j c) y = skatQ X V G w y := by
  simp only [skatQ_eq_sum_variantScore]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l = j
  · subst hl; simp [variantScore_eq_zero_of_col hj]
  · simp [Function.update_of_ne hl]

/-- With no carriers at any variant (`G = 0`) the statistic vanishes identically. -/
@[simp] theorem skatQ_zero_genotype (y : n → ℝ) : skatQ X V (0 : Matrix n m ℝ) w y = 0 := by
  simp [skatQ, skatKernel]

/-- With `G = 0` every mixture weight is `0`. -/
theorem eigenvalues_skatMixtureMatrix_zero_genotype (V' : Matrix n n ℝ) :
    (isHermitian_skatMixtureMatrix (X := X) (V := V) (G := (0 : Matrix n m ℝ)) (w := w)
      V').eigenvalues = 0 := by
  rw [IsHermitian.eigenvalues_eq_zero_iff]
  simp [skatMixtureMatrix, skatKernel]

/-- **Degenerate law with no carriers**: if no individual carries a minor allele at any variant
the law of `Q` is the point mass at `0`, whatever the phenotype covariance; the test has no
power and no non-trivial calibration. -/
theorem map_skatQ_zero_genotype (μ : EuclideanSpace ℝ n) (V' : Matrix n n ℝ) :
    (multivariateGaussian μ V').map (fun y => skatQ X V (0 : Matrix n m ℝ) w (ofLp y)) =
      Measure.dirac 0 := by
  simp

/-! ### Boundary case: singular kinship -/

variable {Φ : Matrix n n ℝ} {σg2 σe2 : ℝ}

omit [Fintype n] in
/-- **A singular relationship matrix is harmless when there is residual noise**: for `Φ`
positive semidefinite (possibly singular) and `σ_e² > 0` the null covariance is positive
definite. -/
theorem posDef_nullCov (hΦ : Φ.PosSemidef) (hg : 0 ≤ σg2) (he : 0 < σe2) :
    (nullCov Φ σg2 σe2).PosDef :=
  PosDef.posSemidef_add (hΦ.smul hg) (PosDef.one.smul he)

/-- Without residual noise a null vector of `Φ` is a null vector of `Σ₀`. -/
theorem nullCov_zero_mulVec {v : n → ℝ} (hv : Φ *ᵥ v = 0) : nullCov Φ σg2 0 *ᵥ v = 0 := by
  simp [nullCov, smul_mulVec, hv]

/-- **Singular kinship without noise makes `Σ₀` singular.** -/
theorem det_nullCov_zero {v : n → ℝ} (hv0 : v ≠ 0) (hv : Φ *ᵥ v = 0) :
    (nullCov Φ σg2 0).det = 0 :=
  exists_mulVec_eq_zero_iff.1 ⟨v, hv0, nullCov_zero_mulVec hv⟩

/-- With a singular covariance `V`, Mathlib's inverse is `V⁻¹ = 0`, so the null projection, and
with it `Q`, collapses to `0`: the GLS formula defining the test is not available. -/
theorem projP_of_det_eq_zero (h : V.det = 0) : projP X V = 0 := by
  have hV : V⁻¹ = 0 := nonsing_inv_apply_not_isUnit V (by simp [h])
  simp [projP, glsMatrix, hV]

/-- `Q ≡ 0` for a singular null covariance (Mathlib's inverse convention). -/
theorem skatQ_of_det_eq_zero (h : V.det = 0) (y : n → ℝ) : skatQ X V G w y = 0 := by
  simp [skatQ_eq, projP_of_det_eq_zero h]

/-- **A singular covariance confines the phenotype to a hyperplane**: if `S v = 0` for a
positive semidefinite `S`, then under `y ~ N(μ, S)` almost surely `vᵀ (y - μ) = 0`. -/
theorem ae_dotProduct_sub_eq_zero {S : Matrix n n ℝ} (hS : S.PosSemidef) {v : n → ℝ}
    (hv : S *ᵥ v = 0) (μ : EuclideanSpace ℝ n) :
    ∀ᵐ y ∂multivariateGaussian μ S, v ⬝ᵥ (ofLp y - ofLp μ) = 0 := by
  set R := CFC.sqrt S
  have hR : Rᵀ = R := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg S).posSemidef.isHermitian.eq
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hRv : R *ᵥ v = 0 := by
    have h0 : (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = 0 := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hR, mulVec_mulVec, hRR, hv, zero_dotProduct]
    exact dotProduct_self_eq_zero.1 h0
  rw [multivariateGaussian, ae_map_iff (by fun_prop)
    (measurableSet_eq_fun (by fun_prop) measurable_const)]
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [ofLp_add, ofLp_toEuclideanCLM, add_sub_cancel_left]
  rw [dotProduct_mulVec, ← mulVec_transpose, hR, hRv, zero_dotProduct]

/-! ### Bridge to `BOLTLMM` -/

/-- `nullCov` is the marginal covariance `BOLTLMM.Model.V` of the BOLT-LMM model. -/
theorem nullCov_eq_V {N : ℕ} (M : BOLTLMM.Model N) : nullCov M.K M.σg2 M.σe2 = M.V := rfl

/-- `projP` is the residual-forming matrix `BOLTLMM.Model.proj` of the BOLT-LMM model. -/
theorem projP_eq_proj {N p : ℕ} (M : BOLTLMM.Model N) (X : Matrix (Fin N) (Fin p) ℝ) :
    projP X M.V = M.proj X := by
  simp only [projP, glsMatrix, BOLTLMM.Model.proj, Matrix.mul_assoc]

end Model

/-! ### The pedigree relationship matrix -/

section Kinship

open Relatedness Kinship

/-- **Twice the kinship matrix of an IBD model is positive semidefinite**: it is the genotype
covariance `Cov(xᵢ, xⱼ) = 2p(1 - p) · 2 φᵢⱼ` divided by `2p(1 - p) > 0`. -/
theorem posSemidef_two_kinship {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Finite ι] (D : IBDModel μ ι) :
    (Matrix.of fun i j => 2 * D.kinship i j).PosSemidef := by
  have := Fintype.ofFinite ι
  have hc : 0 < 2 * D.p * (1 - D.p) := by
    have := D.p_pos; have := D.p_lt_one
    have : 0 < 1 - D.p := by linarith
    positivity
  set h : ι → Ω → ℝ := fun i ω => D.genotype i ω - 2 * D.p
  have hint : ∀ i j, Integrable (fun ω => h i ω * h j ω) μ := by
    intro i j
    refine ((((D.integrable_genotype_mul i j).sub ((D.integrable_genotype i).const_mul
      (2 * D.p))).sub ((D.integrable_genotype j).const_mul (2 * D.p))).add
      (integrable_const (4 * D.p ^ 2))).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [h, Pi.add_apply, Pi.sub_apply]
    ring
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp [D.kinship_comm]
  · have key : star x ⬝ᵥ (Matrix.of fun i j => 2 * D.kinship i j) *ᵥ x =
        (∫ ω, (∑ i, x i * h i ω) ^ 2 ∂μ) / (2 * D.p * (1 - D.p)) := by
      have hsq : (fun ω => (∑ i, x i * h i ω) ^ 2) =
          fun ω => ∑ i, ∑ j, x i * x j * (h i ω * h j ω) := by
        funext ω
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hsq, integral_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => (hint i j).const_mul _, Finset.sum_div]
      simp only [star_trivial, dotProduct, mulVec, of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hp0 : D.p ≠ 0 := D.p_pos.ne'
      have hp1 : 1 - D.p ≠ 0 := sub_ne_zero.2 D.p_lt_one.ne'
      rw [integral_const_mul, D.integral_centered_mul]
      field_simp
    rw [key]
    exact div_nonneg (integral_nonneg fun ω => sq_nonneg _) hc.le

/-- The additive relationship matrix `2 Φ` of a pedigree, from the tabular kinship
`Pedigree.kinship` of `MathlibExt.Biology.StatisticalGenetics.Kinship`. -/
noncomputable def pedigreeRelationship {N : ℕ} (P : Pedigree N) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => 2 * P.kinship i j

/-- The pedigree relationship matrix is positive semidefinite (it may be singular). -/
theorem posSemidef_pedigreeRelationship {N : ℕ} (P : Pedigree N) :
    (pedigreeRelationship P).PosSemidef := by
  have h := posSemidef_two_kinship (P.ibdModel (1 / 2) (by norm_num) (by norm_num))
  simpa [pedigreeRelationship, Pedigree.ibdModel_kinship_eq_kinship] using h

/-- **The famSKAT null covariance of a pedigree** `Σ₀ = σ_g² · 2Φ + σ_e² I` is positive definite
whenever `σ_e² > 0`. -/
theorem posDef_nullCov_pedigreeRelationship {N : ℕ} (P : Pedigree N) {σg2 σe2 : ℝ}
    (hg : 0 ≤ σg2) (he : 0 < σe2) : (nullCov (pedigreeRelationship P) σg2 σe2).PosDef :=
  posDef_nullCov (posSemidef_pedigreeRelationship P) hg he

end Kinship

end MathlibExt.Biology.StatisticalGenetics.BurdenSKAT
