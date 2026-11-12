/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.RareVariantInference.BurdenSKAT
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
import MathlibExt.Biology.StatisticalGenetics.RareVariantInference.MultipleTesting
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Burden test, SKAT-O and the Davies p-value formula

**Setting.** The linear mixed model of `BurdenSKAT` (T37): `n` individuals, covariates `X`,
genotypes `G` (individuals × variants, minor-allele counts), null phenotypic covariance `V`
(known variance components), null projection `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`, and
single-variant scores `Sⱼ = gⱼᵀ P y` (`variantScore`). Variant weights are `aⱼ` (Lee, Wu and Lin
write `wⱼ`); SKAT then uses T37's `skatQ` with weights `aⱼ²`.

## Main results

* **Kernel score statistics.** `kernelQ X V K y = (P y)ᵀ K (P y)` for any kernel `K`, with law
  `map_kernelQ_multivariateGaussian`: if `y ~ N(X α, V')` and `K` is symmetric, then
  `Q_K ~ ∑ⱼ λⱼ χ²₁`, `λ` the eigenvalues of `(P V'^{1/2})ᵀ K (P V'^{1/2})`. SKAT is the kernel
  `G W Gᵀ` (`skatQ_eq_kernelQ`).
* **Burden test.** `burdenScore = ∑ⱼ aⱼ Sⱼ = Cᵀ P y` with `C = G a`, the per-individual
  weighted count of rare alleles (`burdenScore_eq`), and `burdenQ = burdenScore²`. Under
  `y ~ N(X α, V')` the burden score is `N(0, (Pᵀ C)ᵀ V' (Pᵀ C))`
  (`map_burdenScore_multivariateGaussian`); under `H₀` it is `N(0, Cᵀ P C)`
  (`map_burdenScore_null`), so `Q_B ~ (Cᵀ P C) χ²₁` (`map_burdenQ_null`) with mean `Cᵀ P C`
  (`integral_burdenQ_null`). Cauchy–Schwarz links the two tests:
  `Q_B ≤ m · Q_SKAT` (`burdenQ_le_card_mul_skatQ`).
* **SKAT-O.** `skatOQ ρ = (1 - ρ) Q_SKAT + ρ Q_B`; `ρ = 0` is SKAT and `ρ = 1` the burden test
  (`skatOQ_zero`, `skatOQ_one`). Its kernel is Lee, Wu and Lin's
  `K_ρ = G diag(a) R_ρ diag(a) Gᵀ`, `R_ρ = (1 - ρ) I + ρ 𝟙 𝟙ᵀ` (`skatOKernel_eq`,
  `skatOQ_eq_kernelQ`), positive semidefinite for `ρ ∈ [0, 1]` (`posSemidef_skatOKernel`), and
  `Q_ρ ~ ∑ⱼ λⱼ(ρ) χ²₁` with nonnegative weights (`map_skatOQ_multivariateGaussian`,
  `eigenvalues_skatO_nonneg`). The per-`ρ` null p-value `p_ρ = P₀(Q_ρ ≥ Q_ρ(y))`
  (`skatOPValue`) is valid (`isValidPValue_skatOPValue`), and the SKAT-O statistic
  `min_{ρ ∈ grid} p_ρ` (`skatOMinP`) satisfies the Bonferroni bound
  `P₀(min p_ρ ≤ t) ≤ |grid| t` (`measure_skatOMinP_le`).
* **Davies' p-value formula.** The characteristic function of `∑ⱼ λⱼ χ²₁` is
  `∏ⱼ (1 - 2 i λⱼ t)^{-1/2}` (`charFun_weightedChiSq`, `daviesCharFun`). With Gil-Pelaez's
  inversion theorem (`tendsto_gilPelaez`), this gives
  `½ + π⁻¹ ∫₀^T Im(e^{-i t q} φ(t)) / t dt → ½ (P(Q > q) + P(Q ≥ q))` (`tendsto_davies`), and
  `→ P(Q > q)` whenever some `λⱼ ≠ 0` (`weightedChiSq_singleton`, `tendsto_davies_of_ne_zero`).
  `tendsto_davies_kernelQ` applies it to SKAT, burden and every `Q_ρ`, and
  `tendsto_davies_skatOPValue` shows the limit is the validated p-value `skatOPValue`.
* **Dirichlet integral** (needed for Gil-Pelaez, absent from Mathlib):
  `Si T = ∫₀^T sin u / u du → π / 2` (`tendsto_sineIntegral_atTop`), with rate
  `|Si T - π / 2| ≤ 2 / T` (`abs_sineIntegral_sub_le`) and bound `|Si| ≤ 4`
  (`abs_sineIntegral_le`).

## Boundary cases

* **Zero minor-allele count.** A variant without carriers does not enter the burden score
  (`burdenScore_update_of_col`). With no carriers at all (`C = G a = 0`) the burden score is
  `0` and its null law is the point mass at `0` (`map_burdenScore_null_of_collapse_eq_zero`).
* **Degenerate mixture.** With all weights zero `Q ≡ 0`; there Davies' integral converges to the
  mid-p value `½` at `q = 0`, not to `P(Q > 0) = 0`, which is why `tendsto_davies` states the
  mid-p limit and the exact tail needs a nonzero weight (tested in `MathlibExtTest`).
* **Variance component on the boundary.** As in T37, `H₀` puts every variance component of the
  random variant effects at `0`; every `Q_ρ` with `ρ ∈ [0, 1]` is nonnegative-weighted and used
  one-sided.

## Source contract

* S. Lee, M. C. Wu, X. Lin, *Optimal tests for rare variant effects in sequencing association
  studies*, Biostatistics 13 (2012), 762–775, §2: the burden statistic
  `Q_burden = (∑ⱼ wⱼ Sⱼ)²`, the SKAT statistic `∑ⱼ wⱼ² Sⱼ²`, the family
  `Q_ρ = (1 - ρ) Q_SKAT + ρ Q_burden` with kernel `G W R_ρ W Gᵀ`, its mixture-of-chi-squares
  null law for fixed `ρ`, and the SKAT-O statistic `T = min_ρ p_ρ` over a grid of `ρ`.
  Variance components are treated as known, so (as in T37) our statistics are theirs times the
  known constant `σ⁻⁴` when `V = σ² I`.
* R. B. Davies, *Algorithm AS 155: The distribution of a linear combination of χ² random
  variables*, J. R. Stat. Soc. C 29 (1980), 323–333, eq. (1):
  `P(Q < c) = ½ - π⁻¹ ∫₀^∞ Im[φ(u) e^{-i u c}] / u du`, which we state as the equivalent upper
  tail. We treat the central case without the extra normal term (the case SKAT uses).
* J. Gil-Pelaez, *Note on the inversion theorem*, Biometrika 38 (1951), 481–482.

**Not formalized.** Davies' numerical algorithm (trapezoidal discretization of the integral and
its error bounds); noncentral terms and the normal component in Davies' formula; the exact
SKAT-O p-value of `min_ρ p_ρ` (Lee et al.'s one-dimensional integral), for which we give the
Bonferroni bound `|grid| t` instead; estimation of the variance components.

## API-00 receipt (base `origin/main` f9d20c04a)

Reuse search of `MathlibExt`, `WantedExt`, `CSLibExt` and the pinned Mathlib for burden tests,
SKAT-O, Davies' method, Gil-Pelaez or Imhof inversion, the Dirichlet integral and the chi-square
characteristic function found nothing beyond T37. Reused: T37's `weightedChiSq`,
`stdGaussian_map_inner_eq_weightedChiSq`, `skatQ`, `projP`, `variantScore`, `skatKernel`,
`projP_mul_self`, `transpose_projP`, `projP_mul_mul_projP`; the repository's
`isValidPValue_of_tail_le` and `IsValidPValue`; Mathlib's `Real.sinc`, `charFun`,
`charFun_map_sum_pi_eq_prod`, `integral_gaussian_complex`, `IsGaussian.map_eq_gaussianReal`,
`covarianceBilin_multivariateGaussian` and `Measure.pi_map_pi`. `kernelQ` generalizes T37's
`skatQ` to an arbitrary kernel (bridge `skatQ_eq_kernelQ`), because the burden and SKAT-O kernels
are not of the form `G diag(w) Gᵀ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder
open MathlibExt.Probability.Statistics.GeneralizedLeastSquares
open MathlibExt.Biology.StatisticalGenetics.BurdenSKAT

namespace MathlibExt.Biology.StatisticalGenetics.BurdenSKATO

section Kernel

variable {n q m : Type*} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q] [Fintype m]
  [DecidableEq m]

/-- The variance-component score statistic for a general kernel `K`:
`Q_K = (y - X α̂)ᵀ V⁻¹ K V⁻¹ (y - X α̂) = (P y)ᵀ K (P y)`. SKAT, the burden test and SKAT-O are
the kernels `G W Gᵀ`, `G a aᵀ Gᵀ` and `G diag(a) R_ρ diag(a) Gᵀ`. -/
noncomputable def kernelQ (X : Matrix n q ℝ) (V : Matrix n n ℝ) (K : Matrix n n ℝ) (y : n → ℝ) :
    ℝ :=
  (projP X V *ᵥ y) ⬝ᵥ K *ᵥ (projP X V *ᵥ y)

/-- The matrix whose eigenvalues are the mixture weights of `Q_K` when the phenotype has
covariance `V'`: `(P V'^{1/2})ᵀ K (P V'^{1/2})`. -/
noncomputable def kernelMixtureMatrix (X : Matrix n q ℝ) (V : Matrix n n ℝ) (K : Matrix n n ℝ)
    (V' : Matrix n n ℝ) : Matrix n n ℝ :=
  (projP X V * CFC.sqrt V')ᵀ * K * (projP X V * CFC.sqrt V')

variable {X : Matrix n q ℝ} {V : Matrix n n ℝ} {K : Matrix n n ℝ}

/-- SKAT is the kernel statistic of `K = G W Gᵀ`. -/
theorem skatQ_eq_kernelQ (G : Matrix n m ℝ) (w : m → ℝ) (y : n → ℝ) :
    skatQ X V G w y = kernelQ X V (skatKernel G w) y :=
  skatQ_eq y

/-- The SKAT mixture matrix is the kernel mixture matrix of `K = G W Gᵀ`. -/
theorem skatMixtureMatrix_eq_kernelMixtureMatrix (G : Matrix n m ℝ) (w : m → ℝ)
    (V' : Matrix n n ℝ) :
    skatMixtureMatrix X V G w V' = kernelMixtureMatrix X V (skatKernel G w) V' :=
  rfl

/-- The kernel mixture matrix of a symmetric kernel is symmetric. -/
theorem isHermitian_kernelMixtureMatrix (hK : K.IsHermitian) (V' : Matrix n n ℝ) :
    (kernelMixtureMatrix X V K V').IsHermitian := by
  simpa [kernelMixtureMatrix, conjTranspose_eq_transpose_of_trivial] using
    isHermitian_conjTranspose_mul_mul (projP X V * CFC.sqrt V') hK

/-- With a positive semidefinite kernel the mixture weights are nonnegative. -/
theorem eigenvalues_kernelMixtureMatrix_nonneg (hK : K.PosSemidef) (V' : Matrix n n ℝ) (j : n) :
    0 ≤ (isHermitian_kernelMixtureMatrix (X := X) (V := V) hK.isHermitian V').eigenvalues j := by
  have h : (kernelMixtureMatrix X V K V').PosSemidef := by
    simpa [kernelMixtureMatrix, conjTranspose_eq_transpose_of_trivial] using
      hK.conjTranspose_mul_mul_same (projP X V * CFC.sqrt V')
  exact h.eigenvalues_nonneg j

/-- The covariate effects drop out of `Q_K`. -/
theorem kernelQ_add_covariates (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ) (y : n → ℝ) :
    kernelQ X V K (X *ᵥ α + y) = kernelQ X V K y := by
  simp only [kernelQ, mulVec_add, mulVec_mulVec, projP_mul_self hX, zero_mulVec, zero_add]

/-- `Q_K` is continuous in the phenotype. -/
theorem continuous_kernelQ : Continuous (kernelQ X V K) := by
  unfold kernelQ
  fun_prop

/-- **The law of a kernel score statistic is a weighted chi-square mixture.** If
`y ~ N(X α, V')` and `K` is symmetric, then `Q_K ~ ∑ⱼ λⱼ χ²₁` with `λ` the eigenvalues of
`(P V'^{1/2})ᵀ K (P V'^{1/2})`. This is T37's `map_skatQ_multivariateGaussian` for an
arbitrary symmetric kernel. -/
theorem map_kernelQ_multivariateGaussian (hX : IsUnit (Xᵀ * V⁻¹ * X)) (hK : K.IsHermitian)
    (α : q → ℝ) (V' : Matrix n n ℝ) :
    (multivariateGaussian (toLp 2 (X *ᵥ α)) V').map (fun y => kernelQ X V K (ofLp y)) =
      weightedChiSq (isHermitian_kernelMixtureMatrix (X := X) (V := V) hK V').eigenvalues := by
  set hA := isHermitian_kernelMixtureMatrix (X := X) (V := V) hK V'
  rw [← stdGaussian_map_inner_eq_weightedChiSq _ hA.eigenvectorBasis _
    hA.mulVec_eigenvectorBasis, multivariateGaussian,
    Measure.map_map (by exact (continuous_kernelQ.comp (PiLp.continuous_ofLp 2 _)).measurable)
      (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply, inner_toEuclideanCLM, ofLp_add, ofLp_toEuclideanCLM]
  rw [kernelQ_add_covariates hX, kernelQ, mulVec_mulVec, kernelMixtureMatrix]
  conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

end Kernel

section Burden

variable {n q m : Type*} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q] [Fintype m]

/-- The **burden score** `B = ∑ⱼ aⱼ Sⱼ`: the variant weights `a` collapse the single-variant
scores `Sⱼ = gⱼᵀ P y` into one score. -/
noncomputable def burdenScore (X : Matrix n q ℝ) (V : Matrix n n ℝ) (G : Matrix n m ℝ)
    (a : m → ℝ) (y : n → ℝ) : ℝ :=
  ∑ j, a j * variantScore X V G y j

/-- The **burden test statistic** `Q_B = B² = (∑ⱼ aⱼ Sⱼ)²` (Lee, Wu and Lin 2012, §2). -/
noncomputable def burdenQ (X : Matrix n q ℝ) (V : Matrix n n ℝ) (G : Matrix n m ℝ) (a : m → ℝ)
    (y : n → ℝ) : ℝ :=
  burdenScore X V G a y ^ 2

/-- The burden kernel `K_B = G a aᵀ Gᵀ = C Cᵀ`, `C = G a`. -/
def burdenKernel (G : Matrix n m ℝ) (a : m → ℝ) : Matrix n n ℝ :=
  vecMulVec (G *ᵥ a) (G *ᵥ a)

/-- The null variance of the burden score, `Cᵀ P C` with `C = G a` the per-individual weighted
count of rare alleles. -/
noncomputable def burdenVar (X : Matrix n q ℝ) (V : Matrix n n ℝ) (G : Matrix n m ℝ)
    (a : m → ℝ) : ℝ :=
  (G *ᵥ a) ⬝ᵥ projP X V *ᵥ (G *ᵥ a)

variable {X : Matrix n q ℝ} {V : Matrix n n ℝ} {G : Matrix n m ℝ} {a : m → ℝ}

/-- **The burden score is the score of the collapsed genotype** `C = G a`, the weighted sum of
rare alleles carried by each individual: `B = Cᵀ P y`. -/
theorem burdenScore_eq (y : n → ℝ) :
    burdenScore X V G a y = (G *ᵥ a) ⬝ᵥ projP X V *ᵥ y := by
  rw [burdenScore, variantScore, ← dotProduct, dotProduct_mulVec, vecMul_transpose,
    dotProduct_comm]

/-- The burden statistic is the kernel statistic of `K_B = C Cᵀ`. -/
theorem burdenQ_eq_kernelQ (y : n → ℝ) :
    burdenQ X V G a y = kernelQ X V (burdenKernel G a) y := by
  rw [burdenQ, burdenScore_eq, kernelQ, burdenKernel, vecMulVec_mulVec, op_smul_eq_smul,
    dotProduct_smul, smul_eq_mul, dotProduct_comm (projP X V *ᵥ y), sq]

omit [Fintype n] [DecidableEq n] in
/-- The burden kernel is positive semidefinite. -/
theorem posSemidef_burdenKernel [Finite n] : (burdenKernel G a).PosSemidef := by
  have := Fintype.ofFinite n
  simpa [burdenKernel] using Matrix.posSemidef_vecMulVec_self_star (G *ᵥ a)

/-- The covariate effects drop out of the burden score. -/
theorem burdenScore_add_covariates (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ) (y : n → ℝ) :
    burdenScore X V G a (X *ᵥ α + y) = burdenScore X V G a y := by
  simp only [burdenScore_eq, mulVec_add, mulVec_mulVec, projP_mul_self hX, zero_mulVec, zero_add]

/-- The null variance `Cᵀ P C` is nonnegative. -/
theorem burdenVar_nonneg (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X)) :
    0 ≤ burdenVar X V G a := by
  have h := hV.posSemidef.dotProduct_mulVec_nonneg (projP X V *ᵥ (G *ᵥ a))
  rw [burdenVar, ← projP_mul_mul_projP hV hX, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec, ← mulVec_transpose, transpose_projP hV]
  simpa using h

/-- **The law of the burden score.** If `y ~ N(X α, V')`, the burden score is centred Gaussian
with variance `(Pᵀ C)ᵀ V' (Pᵀ C)`. -/
theorem map_burdenScore_multivariateGaussian (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ)
    {V' : Matrix n n ℝ} (hV' : V'.PosSemidef) :
    (multivariateGaussian (toLp 2 (X *ᵥ α)) V').map (fun y => burdenScore X V G a (ofLp y)) =
      gaussianReal 0 (((projP X V)ᵀ *ᵥ (G *ᵥ a)) ⬝ᵥ V' *ᵥ
        ((projP X V)ᵀ *ᵥ (G *ᵥ a))).toNNReal := by
  set u : EuclideanSpace ℝ n := toLp 2 ((projP X V)ᵀ *ᵥ (G *ᵥ a))
  have hf : (fun y : EuclideanSpace ℝ n => burdenScore X V G a (ofLp y)) = innerSL ℝ u := by
    funext y
    rw [innerSL_apply_apply, burdenScore_eq, dotProduct_mulVec, ← mulVec_transpose,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp [u, dotProduct_comm]
  rw [hf, IsGaussian.map_eq_gaussianReal]
  congr 1
  · rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_multivariateGaussian, innerSL_apply_apply,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp only [u, star_trivial]
    rw [dotProduct_comm, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec,
      projP_mul_self hX, zero_mulVec, dotProduct_zero]
  · congr 1
    change Var[fun y => ⟪u, y⟫; _] = _
    rw [← covarianceBilin_self IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hV']

/-- **Null law of the burden score**: under `H₀` (`y ~ N(X α, V)`), `B ~ N(0, Cᵀ P C)`. -/
theorem map_burdenScore_null (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ) :
    (multivariateGaussian (toLp 2 (X *ᵥ α)) V).map (fun y => burdenScore X V G a (ofLp y)) =
      gaussianReal 0 (burdenVar X V G a).toNNReal := by
  rw [map_burdenScore_multivariateGaussian hX α hV.posSemidef]
  congr 2
  rw [burdenVar, transpose_projP hV]
  conv_rhs => rw [← projP_mul_mul_projP hV hX]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (G *ᵥ a) (projP X V),
    ← mulVec_transpose, transpose_projP hV]

/-- A centred Gaussian squared is a one-term weighted chi-square: if `B ~ N(0, v)` then
`B² ~ v χ²₁`. -/
theorem gaussianReal_map_sq {v : ℝ} (hv : 0 ≤ v) :
    (gaussianReal 0 v.toNNReal).map (· ^ 2) = weightedChiSq (fun _ : Unit => v) := by
  have hg : gaussianReal 0 v.toNNReal = (gaussianReal 0 1).map (Real.sqrt v * ·) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    simp [Real.sq_sqrt hv, hv]
  have hpi : (Measure.pi fun _ : Unit => gaussianReal 0 1).map
      (MeasurableEquiv.funUnique Unit ℝ) = gaussianReal 0 1 :=
    (measurePreserving_funUnique (gaussianReal 0 1) Unit).map_eq
  rw [hg, Measure.map_map (by fun_prop) (by fun_prop), weightedChiSq]
  conv_lhs => rw [← hpi, Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  congr 1
  funext ξ
  simp [mul_pow, Real.sq_sqrt hv]

/-- **Null law of the burden statistic**: under `H₀`, `Q_B ~ (Cᵀ P C) χ²₁`, a one-term weighted
chi-square. -/
theorem map_burdenQ_null (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ) :
    (multivariateGaussian (toLp 2 (X *ᵥ α)) V).map (fun y => burdenQ X V G a (ofLp y)) =
      weightedChiSq (fun _ : Unit => burdenVar X V G a) := by
  have hm : Measurable fun y : EuclideanSpace ℝ n => burdenScore X V G a (ofLp y) := by
    have : Continuous fun y : n → ℝ => burdenScore X V G a y := by
      simp only [burdenScore_eq]
      fun_prop
    exact (this.comp (PiLp.continuous_ofLp 2 _)).measurable
  rw [← gaussianReal_map_sq (burdenVar_nonneg hV hX), ← map_burdenScore_null hV hX α,
    Measure.map_map (by fun_prop) hm]
  rfl

/-- **Null mean of the burden statistic**: `𝔼₀ Q_B = Cᵀ P C`. -/
theorem integral_burdenQ_null (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ) :
    ∫ y, burdenQ X V G a (ofLp y) ∂multivariateGaussian (toLp 2 (X *ᵥ α)) V =
      burdenVar X V G a := by
  have hc : Continuous fun y : EuclideanSpace ℝ n => burdenQ X V G a (ofLp y) := by
    have : Continuous fun y : n → ℝ => burdenQ X V G a y := by
      simp only [burdenQ, burdenScore_eq]
      fun_prop
    exact this.comp (PiLp.continuous_ofLp 2 _)
  rw [← integral_map (f := fun x : ℝ => x) hc.aemeasurable (by fun_prop), map_burdenQ_null hV hX,
    integral_weightedChiSq]
  simp

/-! ### Boundary cases for the burden test -/

/-- **Zero minor-allele count**: a variant with no carriers does not enter the burden score,
whatever its weight. -/
theorem burdenScore_update_of_col [DecidableEq m] {j : m} (hj : ∀ i, G i j = 0) (c : ℝ)
    (y : n → ℝ) :
    burdenScore X V G (Function.update a j c) y = burdenScore X V G a y := by
  have h : G *ᵥ Function.update a j c = G *ᵥ a := by
    funext i
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = j
    · subst hk; simp [hj i]
    · rw [Function.update_of_ne hk]
  rw [burdenScore_eq, burdenScore_eq, h]

/-- **No carriers in the region**: when the collapsed genotype `C = G a` vanishes, the burden
score is identically `0`, its null variance is `0`, and its null law is the point mass at `0`. -/
theorem map_burdenScore_null_of_collapse_eq_zero (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X))
    (α : q → ℝ) (hC : G *ᵥ a = 0) :
    (multivariateGaussian (toLp 2 (X *ᵥ α)) V).map (fun y => burdenScore X V G a (ofLp y)) =
      Measure.dirac 0 := by
  rw [map_burdenScore_null hV hX α, burdenVar, hC, zero_dotProduct, Real.toNNReal_zero,
    gaussianReal_zero_var]

/-- **Burden versus SKAT**: by Cauchy–Schwarz, `Q_B = (∑ⱼ aⱼ Sⱼ)² ≤ m ∑ⱼ aⱼ² Sⱼ²`, i.e. the
burden statistic is at most `m` times the SKAT statistic with weights `wⱼ = aⱼ²`. -/
theorem burdenQ_le_card_mul_skatQ [DecidableEq m] (y : n → ℝ) :
    burdenQ X V G a y ≤ Fintype.card m * skatQ X V G (fun j => a j ^ 2) y := by
  rw [burdenQ, burdenScore, skatQ_eq_sum_variantScore]
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun j => a j * variantScore X V G y j)
  rw [Finset.card_univ] at h
  convert h using 3 with j
  ring

end Burden

section SKATO

variable {n q m : Type*} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q] [Fintype m]
  [DecidableEq m]

/-- The SKAT-O correlation matrix `R_ρ = (1 - ρ) I + ρ 𝟙 𝟙ᵀ` between the variant effects. -/
def skatOCorr (ρ : ℝ) : Matrix m m ℝ := (1 - ρ) • 1 + ρ • Matrix.of fun _ _ => 1

/-- The SKAT-O kernel `K_ρ = G diag(a) R_ρ diag(a) Gᵀ` (Lee, Wu and Lin 2012, §2). -/
def skatOKernel (G : Matrix n m ℝ) (a : m → ℝ) (ρ : ℝ) : Matrix n n ℝ :=
  G * diagonal a * (skatOCorr ρ : Matrix m m ℝ) * diagonal a * Gᵀ

/-- The **SKAT-O family of statistics** `Q_ρ = (1 - ρ) Q_S + ρ Q_B`, the convex combination of
the SKAT statistic `Q_S` with weights `wⱼ = aⱼ²` and the burden statistic `Q_B`. -/
noncomputable def skatOQ (X : Matrix n q ℝ) (V : Matrix n n ℝ) (G : Matrix n m ℝ) (a : m → ℝ)
    (ρ : ℝ) (y : n → ℝ) : ℝ :=
  (1 - ρ) * skatQ X V G (fun j => a j ^ 2) y + ρ * burdenQ X V G a y

variable {X : Matrix n q ℝ} {V : Matrix n n ℝ} {G : Matrix n m ℝ} {a : m → ℝ}

/-- `ρ = 0` gives SKAT. -/
theorem skatOQ_zero (y : n → ℝ) : skatOQ X V G a 0 y = skatQ X V G (fun j => a j ^ 2) y := by
  simp [skatOQ]

/-- `ρ = 1` gives the burden test. -/
theorem skatOQ_one (y : n → ℝ) : skatOQ X V G a 1 y = burdenQ X V G a y := by
  simp [skatOQ]

omit [Fintype n] [DecidableEq n] in
/-- **The SKAT-O kernel is the convex combination of the SKAT and burden kernels**:
`G diag(a) R_ρ diag(a) Gᵀ = (1 - ρ) G diag(a²) Gᵀ + ρ (G a)(G a)ᵀ`. -/
theorem skatOKernel_eq (ρ : ℝ) :
    skatOKernel G a ρ = (1 - ρ) • skatKernel G (fun j => a j ^ 2) + ρ • burdenKernel G a := by
  have hJ : diagonal a * (Matrix.of fun _ _ => (1 : ℝ)) * diagonal a = vecMulVec a a := by
    ext i j
    simp [diagonal_mul, mul_diagonal, vecMulVec_apply]
  have hD : diagonal a * diagonal a = diagonal fun j => a j ^ 2 := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext j
    ring
  have h1 : G * diagonal a * diagonal a * Gᵀ = skatKernel G (fun j => a j ^ 2) := by
    rw [skatKernel, Matrix.mul_assoc G, hD]
  have h2 : G * diagonal a * (Matrix.of fun _ _ => (1 : ℝ) : Matrix m m ℝ) * diagonal a * Gᵀ =
      burdenKernel G a := by
    rw [show G * diagonal a * (Matrix.of fun _ _ => (1 : ℝ) : Matrix m m ℝ) * diagonal a =
        G * (diagonal a * (Matrix.of fun _ _ => (1 : ℝ) : Matrix m m ℝ) * diagonal a) by
          simp only [Matrix.mul_assoc], hJ, burdenKernel, mul_vecMulVec, vecMulVec_mul,
      vecMul_transpose]
  simp only [skatOKernel, skatOCorr, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, h1, h2]

/-- `Q_K` is linear in the kernel. -/
theorem kernelQ_add_smul (c₁ c₂ : ℝ) (K₁ K₂ : Matrix n n ℝ) (y : n → ℝ) :
    kernelQ X V (c₁ • K₁ + c₂ • K₂) y = c₁ * kernelQ X V K₁ y + c₂ * kernelQ X V K₂ y := by
  rw [kernelQ, kernelQ, kernelQ, add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]

/-- **SKAT-O is a kernel score statistic**: `Q_ρ = (P y)ᵀ K_ρ (P y)`. -/
theorem skatOQ_eq_kernelQ (ρ : ℝ) (y : n → ℝ) :
    skatOQ X V G a ρ y = kernelQ X V (skatOKernel G a ρ) y := by
  rw [skatOKernel_eq, kernelQ_add_smul, skatOQ, skatQ_eq_kernelQ, burdenQ_eq_kernelQ]

omit [Fintype n] [DecidableEq n] in
/-- The SKAT-O kernel is symmetric. -/
theorem isHermitian_skatOKernel (ρ : ℝ) : (skatOKernel G a ρ).IsHermitian := by
  rw [skatOKernel_eq]
  refine (isHermitian_skatKernel.smul (IsSelfAdjoint.all _)).add
    (IsHermitian.smul ?_ (IsSelfAdjoint.all _))
  simp [IsHermitian, burdenKernel, conjTranspose_eq_transpose_of_trivial, transpose_vecMulVec]

omit [Fintype n] [DecidableEq n] in
/-- For `ρ ∈ [0, 1]` the SKAT-O kernel is positive semidefinite. -/
theorem posSemidef_skatOKernel [Finite n] {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    (skatOKernel G a ρ).PosSemidef := by
  rw [skatOKernel_eq]
  exact ((posSemidef_skatKernel fun j => sq_nonneg (a j)).smul (by linarith)).add
    (posSemidef_burdenKernel.smul h0)

/-- **The law of the SKAT-O statistic.** If `y ~ N(X α, V')`, then for each `ρ`,
`Q_ρ ~ ∑ⱼ λⱼ(ρ) χ²₁` with `λ(ρ)` the eigenvalues of `(P V'^{1/2})ᵀ K_ρ (P V'^{1/2})`; `V' = V`
gives the null law. -/
theorem map_skatOQ_multivariateGaussian (hX : IsUnit (Xᵀ * V⁻¹ * X)) (ρ : ℝ) (α : q → ℝ)
    (V' : Matrix n n ℝ) :
    (multivariateGaussian (toLp 2 (X *ᵥ α)) V').map (fun y => skatOQ X V G a ρ (ofLp y)) =
      weightedChiSq (isHermitian_kernelMixtureMatrix (X := X) (V := V)
        (isHermitian_skatOKernel (G := G) (a := a) ρ) V').eigenvalues := by
  simp_rw [skatOQ_eq_kernelQ]
  exact map_kernelQ_multivariateGaussian hX (isHermitian_skatOKernel ρ) α V'

/-- For `ρ ∈ [0, 1]` the SKAT-O mixture weights are nonnegative. -/
theorem eigenvalues_skatO_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (V' : Matrix n n ℝ) (j : n) :
    0 ≤ (isHermitian_kernelMixtureMatrix (X := X) (V := V)
      (isHermitian_skatOKernel (G := G) (a := a) ρ) V').eigenvalues j :=
  eigenvalues_kernelMixtureMatrix_nonneg (posSemidef_skatOKernel h0 h1) V' j

end SKATO

section GilPelaez

open Real Set Filter Topology

/-- The sine integral `Si z = ∫₀ᶻ sinc u du`, `sinc u = sin u / u` (Mathlib's `Real.sinc`). -/
noncomputable def sineIntegral (z : ℝ) : ℝ := ∫ u in (0 : ℝ)..z, sinc u

private theorem hasDerivAt_expSinAux (t u : ℝ) :
    HasDerivAt (fun u => -(exp (-(u * t)) * (t * sin u + cos u)) / (1 + t ^ 2))
      (exp (-(u * t)) * sin u) u := by
  have h1 : HasDerivAt (fun u => exp (-(u * t))) (exp (-(u * t)) * (-t)) u := by
    have := ((hasDerivAt_id u).mul_const t).neg.exp
    simpa using this
  have h2 : HasDerivAt (fun u => t * sin u + cos u) (t * cos u - sin u) u := by
    exact (((hasDerivAt_sin u).const_mul t).add (hasDerivAt_cos u)).congr_deriv (by ring)
  have := ((h1.mul h2).neg).div_const (1 + t ^ 2)
  convert this using 1
  have : (1 + t ^ 2) ≠ 0 := by positivity
  field_simp
  ring

private theorem integral_exp_mul_sin (t T : ℝ) :
    ∫ u in (0 : ℝ)..T, exp (-(u * t)) * sin u =
      (1 - exp (-(T * t)) * (t * sin T + cos T)) / (1 + t ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_expSinAux t u)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have : (1 + t ^ 2) ≠ 0 := by positivity
  simp
  field_simp
  ring

/-- Laplace representation of the sine integral: writing `1 / u = ∫₀^∞ e^{-u t} dt` and
swapping the integrals (Fubini),
`Si T = ∫₀^∞ (1 - e^{-T t} (t sin T + cos T)) / (1 + t²) dt` for `T > 0`. -/
theorem sineIntegral_eq {T : ℝ} (hT : 0 < T) :
    sineIntegral T =
      ∫ t in Ioi 0, (1 - exp (-(T * t)) * (t * sin T + cos T)) / (1 + t ^ 2) := by
  set F : ℝ → ℝ → ℝ := fun u t => exp (-(u * t)) * sin u
  have hF : Continuous (Function.uncurry F) := by unfold F; fun_prop
  have hinner : ∀ u, 0 < u → ∫ t in Ioi 0, ‖F u t‖ = |sin u| / u := by
    intro u hu
    have h := integral_exp_mul_Ioi (neg_lt_zero.2 hu) 0
    simp only [mul_zero, exp_zero] at h
    simp only [F, norm_mul, Real.norm_eq_abs, abs_exp]
    rw [integral_mul_const]
    simp_rw [neg_mul] at h ⊢
    rw [h]
    field_simp
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff hF.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun u hu => ?_
      have h := integrableOn_exp_mul_Ioi (neg_lt_zero.2 hu.1) 0
      simpa [F, neg_mul] using h.mul_const (sin u)
    · refine Integrable.mono' (integrable_const (1 : ℝ))
        (hF.norm.aestronglyMeasurable.integral_prod_right') ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun u hu => ?_
      simp only [Function.uncurry_apply_pair]
      rw [hinner u hu.1, Real.norm_eq_abs, abs_div, abs_abs, abs_of_pos hu.1]
      exact div_le_one_of_le₀ (by simpa [abs_of_pos hu.1] using abs_sin_le_abs (x := u)) hu.1.le
  have h1 : sineIntegral T = ∫ u in Ioc 0 T, ∫ t in Ioi 0, F u t := by
    rw [sineIntegral, intervalIntegral.integral_of_le hT.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have h := integral_exp_mul_Ioi (neg_lt_zero.2 hu.1) 0
    simp only [mul_zero, exp_zero] at h
    simp only [F]
    rw [integral_mul_const]
    simp_rw [neg_mul] at h ⊢
    rw [h, sinc_of_ne_zero hu.1.ne']
    field_simp
  rw [h1, integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [← intervalIntegral.integral_of_le hT.le]
  exact integral_exp_mul_sin t T

/-- Rate in the Dirichlet integral: `|Si T - π / 2| ≤ 2 / T` for `T > 0`. -/
theorem abs_sineIntegral_sub_le {T : ℝ} (hT : 0 < T) : |sineIntegral T - π / 2| ≤ 2 / T := by
  set B : ℝ → ℝ := fun t => exp (-(T * t)) * (t * sin T + cos T) / (1 + t ^ 2)
  have hexp : IntegrableOn (fun t => exp (-(T * t))) (Ioi 0) := by
    simpa [neg_mul] using integrableOn_exp_mul_Ioi (neg_lt_zero.2 hT) 0
  have hbound : ∀ t ∈ Ioi (0 : ℝ), ‖B t‖ ≤ 2 * exp (-(T * t)) := by
    intro t ht
    have ht : 0 < t := ht
    have h1 : |t * sin T + cos T| ≤ t + 1 := by
      calc |t * sin T + cos T| ≤ |t * sin T| + |cos T| := abs_add_le _ _
        _ ≤ t * 1 + 1 := by
          rw [abs_mul, abs_of_pos ht]
          gcongr
          · exact abs_sin_le_one T
          · exact abs_cos_le_one T
        _ = t + 1 := by ring
    have hd : 0 < 1 + t ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_exp, abs_of_pos hd, div_le_iff₀ hd]
    have he := exp_pos (-(T * t))
    have : exp (-(T * t)) * |t * sin T + cos T| ≤ exp (-(T * t)) * (t + 1) :=
      mul_le_mul_of_nonneg_left h1 he.le
    nlinarith [sq_nonneg (t - 1/2)]
  have hB : IntegrableOn B (Ioi 0) := by
    refine Integrable.mono' (hexp.const_mul 2)
      ((Continuous.div (by fun_prop) (by fun_prop) fun t => by positivity).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall hbound
  have hA : IntegrableOn (fun t : ℝ => (1 + t ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  have hsplit : sineIntegral T = π / 2 - ∫ t in Ioi 0, B t := by
    have hπ : ∫ t in Ioi (0 : ℝ), (1 + t ^ 2)⁻¹ = π / 2 := by simp
    rw [sineIntegral_eq hT, ← hπ, ← integral_sub hA hB]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [B]
    have hd : (1 + t ^ 2) ≠ 0 := by positivity
    field_simp
  rw [hsplit, sub_sub_cancel_left, abs_neg]
  have hI : ∫ t in Ioi 0, 2 * exp (-(T * t)) = 2 / T := by
    rw [integral_const_mul]
    have h := integral_exp_mul_Ioi (neg_lt_zero.2 hT) 0
    simp only [mul_zero, exp_zero, neg_mul] at h
    rw [h]
    field_simp
  rw [← hI, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le (hexp.const_mul 2)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hbound))

/-- **The Dirichlet integral**: `∫₀^T sin u / u du → π / 2`. -/
theorem tendsto_sineIntegral_atTop : Tendsto sineIntegral atTop (𝓝 (π / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    ((eventually_gt_atTop 0).mono fun T hT => abs_sineIntegral_sub_le hT)
    (tendsto_const_nhds.div_atTop tendsto_id)

/-- The sine integral is odd. -/
theorem sineIntegral_neg (z : ℝ) : sineIntegral (-z) = -sineIntegral z := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := z) sinc
  simp only [sinc_neg, neg_zero] at h
  rw [sineIntegral, sineIntegral, h, intervalIntegral.integral_symm]

/-- `Si 0 = 0`. -/
theorem sineIntegral_zero : sineIntegral 0 = 0 := by simp [sineIntegral]

/-- The sine integral is continuous. -/
theorem continuous_sineIntegral : Continuous sineIntegral :=
  intervalIntegral.continuous_primitive (fun a b => continuous_sinc.intervalIntegrable a b) 0

/-- The sine integral is bounded: `|Si z| ≤ 4`. -/
theorem abs_sineIntegral_le (z : ℝ) : |sineIntegral z| ≤ 4 := by
  have hpos : ∀ z, 0 ≤ z → |sineIntegral z| ≤ 4 := by
    intro z hz
    rcases le_or_gt z 1 with h1 | h1
    · have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := z) (C := 1)
        (f := sinc) fun x _ => by simpa using abs_sinc_le_one x
      rw [sub_zero, abs_of_nonneg hz, one_mul] at h
      exact (h.trans h1).trans (by norm_num)
    · have h := abs_sineIntegral_sub_le (by linarith : (0 : ℝ) < z)
      have h2 : 2 / z ≤ 2 := div_le_self (by norm_num) h1.le
      have := abs_sub_abs_le_abs_sub (sineIntegral z) (π / 2)
      rw [abs_of_pos (by positivity : (0 : ℝ) < π / 2)] at this
      linarith [pi_le_four]
  rcases le_total 0 z with hz | hz
  · exact hpos z hz
  · have := hpos (-z) (by linarith)
    rwa [sineIntegral_neg, abs_neg] at this

/-- `Si(s T) → (π / 2) sign s` as `T → ∞`. -/
theorem tendsto_sineIntegral_mul_atTop (s : ℝ) :
    Tendsto (fun T => sineIntegral (s * T)) atTop (𝓝 (π / 2 * Real.sign s)) := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · rw [Real.sign_of_neg hs, mul_neg_one]
    have h := tendsto_sineIntegral_atTop.comp (tendsto_id.const_mul_atTop (neg_pos.2 hs))
    have h2 := h.neg
    refine h2.congr fun T => ?_
    simp [Function.comp, ← sineIntegral_neg, neg_mul]
  · simp [sineIntegral_zero]
  · rw [Real.sign_of_pos hs, mul_one]
    exact tendsto_sineIntegral_atTop.comp (tendsto_id.const_mul_atTop hs)

open Complex in
/-- `Im(e^{-i t x} φ_μ(t)) = ∫ sin(t (y - x)) dμ(y)`. -/
theorem im_cexp_mul_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ] (t x : ℝ) :
    (cexp (-(t * x) * I) * charFun μ t).im = ∫ y, Real.sin (t * (y - x)) ∂μ := by
  have h : ∀ y : ℝ, cexp (-(t * x) * I) * cexp (t * y * I) = cexp (↑(t * (y - x)) * I) := by
    intro y
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hint : Integrable (fun y : ℝ => cexp (↑(t * (y - x)) * I)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun y => ?_)
    rw [norm_exp_ofReal_mul_I]
  rw [charFun_apply_real, ← integral_const_mul]
  simp_rw [h]
  have := integral_im hint
  simp only [RCLike.im_to_complex] at this
  rw [← this]
  simp_rw [exp_ofReal_mul_I_im]

private theorem sin_div_eq_mul_sinc {t : ℝ} (ht : t ≠ 0) (s : ℝ) :
    Real.sin (t * s) / t = s * sinc (t * s) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  · rw [sinc_of_ne_zero (mul_ne_zero ht hs)]
    field_simp

/-- `∫₀^T sin(t s) / t dt = Si(s T)`, written with `sinc`. -/
theorem integral_mul_sinc (s T : ℝ) :
    ∫ t in (0 : ℝ)..T, s * sinc (t * s) = sineIntegral (s * T) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [sineIntegral_zero]
  · rw [intervalIntegral.integral_const_mul]
    simp_rw [mul_comm _ s]
    rw [intervalIntegral.integral_comp_mul_left (fun u => sinc u) hs, mul_zero, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hs, one_mul, sineIntegral]

/-- `∫ sign(y - x) dμ(y) = P(Y > x) + P(Y ≥ x) - 1`. -/
theorem integral_sign_sub {μ : Measure ℝ} [IsProbabilityMeasure μ] (x : ℝ) :
    ∫ y, Real.sign (y - x) ∂μ = μ.real (Ioi x) + μ.real (Ici x) - 1 := by
  have h : (fun y => Real.sign (y - x)) =
      fun y => (Ioi x).indicator 1 y - (Iio x).indicator 1 y := by
    funext y
    rcases lt_trichotomy y x with h | rfl | h
    · simp [Real.sign_of_neg (sub_neg.2 h), h, not_lt.2 h.le]
    · simp
    · simp [Real.sign_of_pos (sub_pos.2 h), h, not_lt.2 h.le]
  have h1 : Integrable ((Ioi x).indicator (1 : ℝ → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  have h2 : Integrable ((Iio x).indicator (1 : ℝ → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Iio
  rw [h, integral_sub h1 h2,
    integral_indicator_one measurableSet_Ioi, integral_indicator_one measurableSet_Iio,
    ← compl_Ici, measureReal_compl measurableSet_Ici, probReal_univ]
  ring

open Complex in
/-- **Gil-Pelaez inversion formula** (Gil-Pelaez 1951). For a probability law `μ` on `ℝ` with
finite mean and every `x`,
`½ + π⁻¹ ∫₀^T Im(e^{-i t x} φ_μ(t)) / t dt → ½ (μ(x, ∞) + μ[x, ∞))` as `T → ∞`.
The finite mean is used only for Fubini on `[0, T] × ℝ`. -/
theorem tendsto_gilPelaez {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (x : ℝ) :
    Tendsto (fun T => 1 / 2 + π⁻¹ * ∫ t in (0 : ℝ)..T, (cexp (-(t * x) * I) * charFun μ t).im / t)
      atTop (𝓝 ((μ.real (Ioi x) + μ.real (Ici x)) / 2)) := by
  have hsub : Integrable (fun y => y - x) μ := hμ.sub (integrable_const x)
  -- the inner integral over `t`, after Fubini
  have key : ∀ T, 0 < T → ∫ t in (0 : ℝ)..T, (cexp (-(t * x) * I) * charFun μ t).im / t =
      ∫ y, sineIntegral ((y - x) * T) ∂μ := by
    intro T hT
    set F : ℝ → ℝ → ℝ := fun t y => (y - x) * sinc (t * (y - x))
    have hF : Continuous (Function.uncurry F) := by
      unfold F; exact (by fun_prop : Continuous fun p : ℝ × ℝ => (p.2 - x) * sinc (p.1 * (p.2 - x)))
    have hFle : ∀ t y, ‖F t y‖ ≤ |y - x| := by
      intro t y
      simp only [F, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_sinc_le_one _)
    have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioc 0 T)).prod μ) := by
      rw [integrable_prod_iff hF.aestronglyMeasurable]
      refine ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
      · exact hsub.abs.mono' (hF.comp (Continuous.prodMk_right t)).aestronglyMeasurable
          (ae_of_all _ fun y => hFle t y)
      · refine Integrable.mono' (integrable_const (∫ y, |y - x| ∂μ))
          (hF.norm.aestronglyMeasurable.integral_prod_right') (ae_of_all _ fun t => ?_)
        simp only [Function.uncurry_apply_pair]
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact integral_mono (hsub.abs.mono'
          (hF.comp (Continuous.prodMk_right t)).norm.aestronglyMeasurable
          (ae_of_all _ fun y => by simpa using hFle t y)) hsub.abs fun y => hFle t y
    calc ∫ t in (0 : ℝ)..T, (cexp (-(t * x) * I) * charFun μ t).im / t
        = ∫ t in Ioc 0 T, ∫ y, F t y ∂μ := by
          rw [intervalIntegral.integral_of_le hT.le]
          refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
          rw [im_cexp_mul_charFun, ← integral_div]
          exact integral_congr_ae (ae_of_all _ fun y => sin_div_eq_mul_sinc ht.1.ne' _)
      _ = ∫ y, (∫ t in Ioc 0 T, F t y) ∂μ := integral_integral_swap hint
      _ = ∫ y, sineIntegral ((y - x) * T) ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          beta_reduce
          rw [← intervalIntegral.integral_of_le hT.le]
          exact integral_mul_sinc (y - x) T
  have hlim : Tendsto (fun T => ∫ y, sineIntegral ((y - x) * T) ∂μ) atTop
      (𝓝 (∫ y, π / 2 * Real.sign (y - x) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 4)
      (Filter.Eventually.of_forall fun T => ?_) (Filter.Eventually.of_forall fun T =>
        ae_of_all _ fun y => abs_sineIntegral_le _) (integrable_const _)
      (ae_of_all _ fun y => tendsto_sineIntegral_mul_atTop (y - x))
    exact (continuous_sineIntegral.comp
      (by fun_prop : Continuous fun y : ℝ => (y - x) * T)).aestronglyMeasurable
  rw [integral_const_mul, integral_sign_sub] at hlim
  have h2 := (hlim.const_mul π⁻¹).const_add (1 / 2)
  have hval : 1 / 2 + π⁻¹ * (π / 2 * (μ.real (Ioi x) + μ.real (Ici x) - 1)) =
      (μ.real (Ioi x) + μ.real (Ici x)) / 2 := by
    field_simp
    ring
  rw [hval] at h2
  refine h2.congr' ((eventually_gt_atTop 0).mono fun T hT => ?_)
  beta_reduce
  rw [key T hT]

end GilPelaez

section Davies

open Real Set Filter Topology

open Complex in
private theorem ofReal_mul_cpow' {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z ≠ 0) (s : ℂ) :
    ((a : ℂ) * z) ^ s = (a : ℂ) ^ s * z ^ s := by
  rw [cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.2 ha.ne') hz),
    cpow_def_of_ne_zero (ofReal_ne_zero.2 ha.ne'), cpow_def_of_ne_zero hz, log_ofReal_mul ha hz,
    ← Complex.exp_add, ofReal_log ha.le]
  ring_nf

open Complex in
/-- The characteristic function of `c χ²₁`: `𝔼 exp(i t c ξ²) = (1 - 2 i c t)^{-1/2}`. -/
theorem charFun_map_mul_sq_gaussianReal (c t : ℝ) :
    charFun ((gaussianReal 0 1).map fun x => c * x ^ 2) t =
      (1 - 2 * c * t * I) ^ (-(1 / 2) : ℂ) := by
  set w : ℂ := 1 - 2 * c * t * I
  set b : ℂ := 1 / 2 - c * t * I
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [w] at this
  have hbre : 0 < b.re := by simp [b]
  have hwarg : w.arg ≠ π := by
    have h := abs_arg_lt_pi_div_two_iff.2 (Or.inl (by simp [w] : 0 < w.re))
    intro hπ
    rw [hπ, abs_of_pos pi_pos] at h
    linarith [pi_pos]
  have hpi : (π : ℂ) / b = ((2 * π : ℝ) : ℂ) * w⁻¹ := by
    have hb : b = w / 2 := by simp only [b, w]; ring
    rw [hb]
    push_cast
    field_simp
  have hsq : ((2 * π : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((√(2 * π) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h : ∀ x : ℝ, gaussianPDFReal 0 1 x • cexp (↑t * ↑(c * x ^ 2) * I) =
      ((√(2 * π))⁻¹ : ℝ) * cexp (-b * (x : ℂ) ^ 2) := by
    intro x
    rw [gaussianPDFReal, Complex.real_smul, ofReal_mul, ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    · simp
    · simp only [b]; push_cast; ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian_complex hbre, hpi,
    ofReal_mul_cpow' (by positivity) (inv_ne_zero hw0), hsq, inv_cpow _ _ hwarg, cpow_neg]
  have : ((√(2 * π) : ℝ) : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; positivity
  push_cast
  field_simp

open Complex in
/-- **Characteristic function of a weighted chi-square mixture**:
`𝔼 exp(i t ∑ⱼ λⱼ ξⱼ²) = ∏ⱼ (1 - 2 i λⱼ t)^{-1/2}`. -/
theorem charFun_weightedChiSq {k : Type*} [Fintype k] (lam : k → ℝ) (t : ℝ) :
    charFun (weightedChiSq lam) t = ∏ j, (1 - 2 * lam j * t * I) ^ (-(1 / 2) : ℂ) := by
  have hpi : (Measure.pi fun _ : k => gaussianReal 0 1).map (fun ξ j => lam j * ξ j ^ 2) =
      Measure.pi fun j => (gaussianReal 0 1).map fun x => lam j * x ^ 2 :=
    Measure.pi_map_pi (f := fun j x => lam j * x ^ 2) fun j => by fun_prop
  have hw : weightedChiSq lam = (Measure.pi fun j => (gaussianReal 0 1).map
      fun x => lam j * x ^ 2).map fun p => ∑ j, p j := by
    rw [← hpi, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hw, charFun_map_sum_pi_eq_prod, Finset.prod_apply]
  exact Finset.prod_congr rfl fun j _ => charFun_map_mul_sq_gaussianReal (lam j) t

/-- The characteristic function of `∑ⱼ λⱼ χ²₁` used in Davies' formula,
`φ(t) = ∏ⱼ (1 - 2 i λⱼ t)^{-1/2}` (principal branch; each base has real part `1`). -/
noncomputable def daviesCharFun {k : Type*} [Fintype k] (lam : k → ℝ) (t : ℝ) : ℂ :=
  ∏ j, (1 - 2 * lam j * t * Complex.I) ^ (-(1 / 2) : ℂ)

/-- The weighted chi-square law has a finite mean. -/
theorem integrable_id_weightedChiSq {k : Type*} [Fintype k] (lam : k → ℝ) :
    Integrable id (weightedChiSq lam) := by
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
  rw [weightedChiSq, integrable_map_measure aestronglyMeasurable_id
    (by fun_prop : Measurable fun ξ : k → ℝ => ∑ j, lam j * ξ j ^ 2).aemeasurable]
  exact integrable_finsetSum _ fun j _ => (hint j).const_mul _

/-- **Davies' p-value formula** (Davies 1980, eq. (1), from Gil-Pelaez's inversion theorem).
For `Q ~ ∑ⱼ λⱼ χ²₁` and every `q`,
`½ + π⁻¹ ∫₀^T Im(e^{-i t q} φ(t)) / t dt → ½ (P(Q > q) + P(Q ≥ q))` as `T → ∞`, with
`φ = daviesCharFun λ`. The improper integral is the one Davies' algorithm discretizes. -/
theorem tendsto_davies {k : Type*} [Fintype k] (lam : k → ℝ) (q : ℝ) :
    Tendsto (fun T => 1 / 2 + π⁻¹ * ∫ t in (0 : ℝ)..T,
        (Complex.exp (-(t * q) * Complex.I) * daviesCharFun lam t).im / t) atTop
      (𝓝 (((weightedChiSq lam).real (Ioi q) + (weightedChiSq lam).real (Ici q)) / 2)) := by
  have h := tendsto_gilPelaez (integrable_id_weightedChiSq lam) q
  simp_rw [charFun_weightedChiSq] at h
  exact h

/-- **Davies' formula for the upper tail**: at a point `q` without mass, the limit is the
p-value `P(Q > q)`. -/
theorem tendsto_davies_of_measure_singleton {k : Type*} [Fintype k] (lam : k → ℝ) {q : ℝ}
    (hq : weightedChiSq lam {q} = 0) :
    Tendsto (fun T => 1 / 2 + π⁻¹ * ∫ t in (0 : ℝ)..T,
        (Complex.exp (-(t * q) * Complex.I) * daviesCharFun lam t).im / t) atTop
      (𝓝 ((weightedChiSq lam).real (Ioi q))) := by
  have h := tendsto_davies lam q
  rwa [measureReal_congr (Ioi_ae_eq_Ici' hq).symm, add_self_div_two] at h

/-- **No atoms**: if some weight is nonzero, the weighted chi-square law gives every point
mass `0`. -/
theorem weightedChiSq_singleton {k : Type*} [Fintype k] {lam : k → ℝ} {j : k} (hj : lam j ≠ 0)
    (q : ℝ) : weightedChiSq lam {q} = 0 := by
  classical
  set f : (k → ℝ) → ℝ := fun ξ => ∑ i, lam i * ξ i ^ 2 with hfdef
  have hf : Measurable f := by fun_prop
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : k => ℝ) (· = j)
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ : k => gaussianReal 0 1) (· = j)
  set j0 : {i // i = j} := ⟨j, rfl⟩
  have hpt : ∀ c : ℝ, gaussianReal 0 1 {x | lam j * x ^ 2 = c} = 0 := by
    intro c
    refine measure_mono_null (t := {√(c / lam j), -√(c / lam j)}) (fun x hx => ?_)
      (gaussianReal_absolutelyContinuous 0 one_ne_zero ((Set.toFinite _).measure_zero _))
    have hx : lam j * x ^ 2 = c := hx
    have hx2 : x ^ 2 = c / lam j := by rw [← hx]; field_simp
    have habs : |x| = √(c / lam j) := by rw [← hx2, Real.sqrt_sq_eq_abs]
    rcases (abs_eq (Real.sqrt_nonneg _)).1 habs with h | h <;> simp [h]
  have key : ∀ a b, f (e.symm (a, b)) = lam j * a j0 ^ 2 + f (e.symm (0, b)) := by
    intro a b
    have h : f (e.symm (a, b)) - f (e.symm (0, b)) = lam j * a j0 ^ 2 := by
      simp only [hfdef, ← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single j]
      · simp [e, MeasurableEquiv.piEquivPiSubtypeProd, j0]
      · intro i _ hi
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd, hi]
      · simp
    linarith
  rw [weightedChiSq, Measure.map_apply hf (measurableSet_singleton q), ← he.symm.map_eq,
    MeasurableEquiv.map_apply,
    Measure.prod_apply_symm (e.symm.measurable (hf (measurableSet_singleton q)))]
  refine (lintegral_congr fun b => ?_).trans lintegral_zero
  have hs : (fun a => (a, b)) ⁻¹' (e.symm ⁻¹' (f ⁻¹' {q})) =
      Function.eval j0 ⁻¹' {x | lam j * x ^ 2 = q - f (e.symm (0, b))} := by
    ext a
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq, Function.eval, key a b]
    constructor <;> intro h <;> linarith
  rw [hs]
  convert ((measurePreserving_eval (fun _ : {i // i = j} => gaussianReal 0 1) j0).measure_preimage
    (s := {x | lam j * x ^ 2 = q - f (e.symm (0, b))})
    (measurableSet_eq_fun (by fun_prop : Measurable fun x : ℝ => lam j * x ^ 2)
      measurable_const).nullMeasurableSet).trans (hpt _)

/-- **Davies' formula, nondegenerate case**: when some weight is nonzero, the limit is the exact
upper tail `P(Q > q)` for every `q`. -/
theorem tendsto_davies_of_ne_zero {k : Type*} [Fintype k] {lam : k → ℝ} {j : k} (hj : lam j ≠ 0)
    (q : ℝ) :
    Tendsto (fun T => 1 / 2 + π⁻¹ * ∫ t in (0 : ℝ)..T,
        (Complex.exp (-(t * q) * Complex.I) * daviesCharFun lam t).im / t) atTop
      (𝓝 ((weightedChiSq lam).real (Ioi q))) :=
  tendsto_davies_of_measure_singleton lam (weightedChiSq_singleton hj q)

end Davies

section Application

open Real Set Filter Topology MathlibExt.Probability.Statistics.MultipleTesting

variable {n q m : Type*} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q] [Fintype m]
  [DecidableEq m] {X : Matrix n q ℝ} {V : Matrix n n ℝ}

/-- **Davies' formula for a kernel score test.** Under `y ~ N(X α, V')`, the Davies integral
built from the eigenvalues `λ` of `(P V'^{1/2})ᵀ K (P V'^{1/2})` converges to the mid-p upper
tail `½ (P(Q_K > c) + P(Q_K ≥ c))` of the statistic. This covers SKAT, the burden test and
every SKAT-O statistic `Q_ρ`. -/
theorem tendsto_davies_kernelQ (hX : IsUnit (Xᵀ * V⁻¹ * X)) {K : Matrix n n ℝ}
    (hK : K.IsHermitian) (α : q → ℝ) (V' : Matrix n n ℝ) (c : ℝ) :
    Tendsto (fun T => 1 / 2 + π⁻¹ * ∫ t in (0 : ℝ)..T,
        (Complex.exp (-(t * c) * Complex.I) *
          daviesCharFun (isHermitian_kernelMixtureMatrix (X := X) (V := V) hK V').eigenvalues
            t).im / t) atTop
      (𝓝 (((multivariateGaussian (toLp 2 (X *ᵥ α)) V').real
          {y | c < kernelQ X V K (ofLp y)} +
        (multivariateGaussian (toLp 2 (X *ᵥ α)) V').real
          {y | c ≤ kernelQ X V K (ofLp y)}) / 2)) := by
  have hm : Measurable fun y : EuclideanSpace ℝ n => kernelQ X V K (ofLp y) :=
    (continuous_kernelQ.comp (PiLp.continuous_ofLp 2 _)).measurable
  have h := tendsto_davies (isHermitian_kernelMixtureMatrix (X := X) (V := V) hK V').eigenvalues c
  rwa [← map_kernelQ_multivariateGaussian hX hK α V', map_measureReal_apply hm measurableSet_Ioi,
    map_measureReal_apply hm measurableSet_Ici] at h

/-- The exact null p-value of the SKAT-O statistic at a fixed `ρ`:
`p_ρ(y) = P₀(Q_ρ ≥ Q_ρ(y))`, computed from the null mixture law `∑ⱼ λⱼ(ρ) χ²₁`. -/
noncomputable def skatOPValue (X : Matrix n q ℝ) (V : Matrix n n ℝ) (G : Matrix n m ℝ)
    (a : m → ℝ) (ρ : ℝ) (y : n → ℝ) : ℝ :=
  (weightedChiSq (isHermitian_kernelMixtureMatrix (X := X) (V := V)
    (isHermitian_skatOKernel (G := G) (a := a) ρ) V).eigenvalues).real
      (Ici (skatOQ X V G a ρ y))

/-- The **SKAT-O statistic**: the minimum of the SKAT-O p-values over a finite grid of `ρ`
(Lee, Wu and Lin 2012, §2.2). -/
noncomputable def skatOMinP (X : Matrix n q ℝ) (V : Matrix n n ℝ) (G : Matrix n m ℝ) (a : m → ℝ)
    (grid : Finset ℝ) (hgrid : grid.Nonempty) (y : n → ℝ) : ℝ :=
  grid.inf' hgrid fun ρ => skatOPValue X V G a ρ y

variable {G : Matrix n m ℝ} {a : m → ℝ}

/-- **Each SKAT-O p-value is valid under the null**: `P₀(p_ρ ≤ t) ≤ t` for `t ∈ [0, 1]`. -/
theorem isValidPValue_skatOPValue (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ) (ρ : ℝ) :
    IsValidPValue (multivariateGaussian (toLp 2 (X *ᵥ α)) V)
      fun y => skatOPValue X V G a ρ (ofLp y) := by
  set ν := weightedChiSq (isHermitian_kernelMixtureMatrix (X := X) (V := V)
    (isHermitian_skatOKernel (G := G) (a := a) ρ) V).eigenvalues
  have hm : Measurable fun y : EuclideanSpace ℝ n => skatOQ X V G a ρ (ofLp y) := by
    simp_rw [skatOQ_eq_kernelQ]
    exact (continuous_kernelQ.comp (PiLp.continuous_ofLp 2 _)).measurable
  refine RareVariantInference.MultipleTesting.isValidPValue_of_tail_le
    (T := fun y => skatOQ X V G a ρ (ofLp y))
    (G := fun s => ν.real (Ici s)) (fun s t hst => measureReal_mono (Ici_subset_Ici.2 hst))
    fun s => ?_
  have hν : ν = (multivariateGaussian (toLp 2 (X *ᵥ α)) V).map
      (fun y => skatOQ X V G a ρ (ofLp y)) := (map_skatOQ_multivariateGaussian hX ρ α V).symm
  rw [ofReal_measureReal, hν, Measure.map_apply hm measurableSet_Ici]
  rfl

/-- **Davies' formula computes the SKAT-O p-value.** If some weight `λⱼ(ρ)` of the null mixture is
nonzero, the Davies integral at `c = Q_ρ(y)` converges to `skatOPValue ρ y = P₀(Q_ρ ≥ Q_ρ(y))`,
the p-value proved valid in `isValidPValue_skatOPValue`. -/
theorem tendsto_davies_skatOPValue (ρ : ℝ) {j : n}
    (hj : (isHermitian_kernelMixtureMatrix (X := X) (V := V)
      (isHermitian_skatOKernel (G := G) (a := a) ρ) V).eigenvalues j ≠ 0) (y : n → ℝ) :
    Tendsto (fun T => 1 / 2 + π⁻¹ * ∫ t in (0 : ℝ)..T,
        (Complex.exp (-(t * skatOQ X V G a ρ y) * Complex.I) *
          daviesCharFun (isHermitian_kernelMixtureMatrix (X := X) (V := V)
            (isHermitian_skatOKernel (G := G) (a := a) ρ) V).eigenvalues t).im / t) atTop
      (𝓝 (skatOPValue X V G a ρ y)) := by
  have h := tendsto_davies_of_ne_zero hj (skatOQ X V G a ρ y)
  rwa [measureReal_congr (Ioi_ae_eq_Ici' (weightedChiSq_singleton hj _))] at h

/-- **Bonferroni validity of SKAT-O**: under the null,
`P₀(min_{ρ ∈ grid} p_ρ ≤ t) ≤ |grid| t`. -/
theorem measure_skatOMinP_le (hX : IsUnit (Xᵀ * V⁻¹ * X)) (α : q → ℝ) (grid : Finset ℝ)
    (hgrid : grid.Nonempty) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    multivariateGaussian (toLp 2 (X *ᵥ α)) V {y | skatOMinP X V G a grid hgrid (ofLp y) ≤ t} ≤
      grid.card * ENNReal.ofReal t := by
  have hset : {y : EuclideanSpace ℝ n | skatOMinP X V G a grid hgrid (ofLp y) ≤ t} =
      ⋃ ρ ∈ grid, {y | skatOPValue X V G a ρ (ofLp y) ≤ t} := by
    ext y
    simp [skatOMinP, Finset.inf'_le_iff]
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ ρ ∈ grid, multivariateGaussian (toLp 2 (X *ᵥ α)) V
        {y | skatOPValue X V G a ρ (ofLp y) ≤ t}
      ≤ ∑ _ρ ∈ grid, ENNReal.ofReal t :=
        Finset.sum_le_sum fun ρ _ => isValidPValue_skatOPValue hX α ρ t ht
    _ = grid.card * ENNReal.ofReal t := by simp

end Application

end MathlibExt.Biology.StatisticalGenetics.BurdenSKATO
