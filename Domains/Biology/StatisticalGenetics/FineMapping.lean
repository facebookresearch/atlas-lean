/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import MathlibExt.Probability.Distributions.GaussianConditioning
public import MathlibExt.Probability.Distributions.GaussianDensity

/-!
# Bayesian fine-mapping and colocalization

Exact identities behind summary-statistic fine-mapping (Wakefield's approximate Bayes factor and
the single-effect regression of SuSiE), the coloc test for a shared causal variant, and
credible sets.

## Conventions

* Variances are `ℝ≥0`, as in Mathlib's `gaussianReal`; theorems assume a positive sampling
  (residual) variance. Bayes factors compare the alternative with the null (large values favor
  association), as in coloc and SuSiE; Wakefield (2009) reports the reciprocal.
* The single-effect regression has `n` samples, genotype vector `x ≠ 0`, phenotype
  `y = x β + e` with `β ~ N(0, σ₀²)` independent of `e ~ N(0, σ² I)` (`σ² > 0` known), and the
  summary statistics `β̂ = xᵀ y / xᵀ x` (`olsEffect`) and `s² = σ² / xᵀ x` (`olsVar`). For
  `x = 0` both are junk values (`0`); every theorem about them assumes `x ≠ 0`.
* coloc configurations are pairs `(causal variant of trait 1, causal variant of trait 2)` in
  `Option ι × Option ι`, `none` meaning no causal variant. The cited Giambartolomei et al. (2014)
  calculation uses unnormalized configuration weights with H0 weight `1`.

## Main results

* `wakefieldABF_eq`: **Wakefield's closed form**
  `ABF = √(V / (V + W)) · exp (z² W / (2 (V + W)))`, `z = β̂ / √V`, of the density ratio
  `N(β̂; 0, V + W) / N(β̂; 0, V)`; `rnDeriv_map_add_ae_eq`: it is the Radon–Nikodym derivative
  of the law of `β̂ = β + ε` under the alternative `β ~ N(0, W)` with respect to its law under the
  null `β = 0`.
* `multivariateGaussianPDFReal_serCov_div`: the Bayes factor of the regression (density of `y`
  given that `x` carries the effect, over its density with no effect) is the ABF of `(β̂, s²)`;
  `map_ser_eq_withDensity` identifies that density as the law of `y`.
  `serPosterior_eq_pip`: hence, for a normalized non-negative causal-variant prior `w`, the
  posterior inclusion probabilities are `α_j = w_j BF_j / ∑_k w_k BF_k` (`pip`).
  `condDistrib_ser_effect`: given `y`, the effect is `N(σ₀² β̂ / (σ₀² + s²), σ₀² s² / (σ₀² + s²))`.
* `sum_colocWeight_mul_colocBF`: **the coloc closed forms**: the sums of unnormalized weight ×
  Bayes factor over the configurations of H0–H4 equal `1`, `p1 ∑ BF1`, `p2 ∑ BF2`,
  `p1 p2 (∑ BF1 ∑ BF2 - ∑ BF1 BF2)` and `p12 ∑ BF1 BF2`; `colocPosterior_eq` is the
  unconditional algebraic normalization identity, while `colocPosterior_nonneg` and
  `sum_colocPosterior_eq_one` give its probability interpretation for non-negative Bayes factors.
  `ColocPrior.sum_categoricalPrior` preserves the separate categorical-prior model.
* `le_card_of_isCredibleSet`, `exists_minimal_credible_prefix`: **credible sets**: the shortest
  prefix of the variants sorted by decreasing inclusion probability whose mass is at least `ρ`
  has the minimum size among all sets of mass at least `ρ`.

## Not covered

The posterior over the causal variant is Bayes' rule for densities (`serPosterior_eq_pip`), not
Mathlib's posterior kernel of the mixture model. The iterative Bayesian stepwise selection of
SuSiE (several effects), the estimation of `σ²` and `σ₀²`, and the coloc approximation of
per-variant Bayes factors from p-values are not formalized. Raw coloc closed forms accept arbitrary
real inputs as algebraic scores; their probability-domain theorems assume non-negative Bayes
factors.

## References

* J. Wakefield, *Bayes factors for genome-wide association studies: comparison with P-values*,
  Genet. Epidemiol. 33 (2009) 79–86.
* G. Wang, A. Sarkar, P. Carbonetto, M. Stephens, *A simple new approach to variable selection
  in regression, with application to genetic fine mapping*, J. R. Stat. Soc. B 82 (2020)
  1273–1300.
* C. Giambartolomei et al., *Bayesian test for colocalisation between pairs of genetic
  association studies using summary statistics*, PLoS Genet. 10 (2014) e1004383.
* J. B. Maller et al., *Bayesian refinement of association signals for 14 loci in 3 common
  diseases*, Nat. Genet. 44 (2012) 1294–1301.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Biology.StatisticalGenetics.FineMapping

open MeasureTheory ProbabilityTheory Real Matrix WithLp MetaMathlibExt
open scoped NNReal ENNReal RealInnerProductSpace

/-! ### Wakefield's approximate Bayes factor -/

/-- Wakefield's approximate Bayes factor: the `N(0, V + W)` density of the estimate `b` (its
marginal law under the alternative `β ~ N(0, W)`) divided by its `N(0, V)` density (the null
`β = 0`). Wakefield (2009) reports the reciprocal, null over alternative; coloc and SuSiE use
this orientation, in which large values favor association. For `V = 0` the null density is
Mathlib's junk value `0` and so is the ratio; the theorems assume `V ≠ 0`. -/
noncomputable def wakefieldABF (V W : ℝ≥0) (b : ℝ) : ℝ :=
  gaussianPDFReal 0 (V + W) b / gaussianPDFReal 0 V b

/-- **Wakefield's closed form**: with `z = b / √V`,
`ABF = √(V / (V + W)) · exp (z² W / (2 (V + W)))`. -/
theorem wakefieldABF_eq {V : ℝ≥0} (hV : V ≠ 0) (W : ℝ≥0) (b : ℝ) :
    wakefieldABF V W b =
      √((V : ℝ) / (V + W)) * exp ((b / √(V : ℝ)) ^ 2 * W / (2 * (V + W))) := by
  have hV0 : (0 : ℝ) < V := by positivity
  have hVW : (0 : ℝ) < V + W := by positivity
  have h2pi : (0 : ℝ) ≤ 2 * π := by positivity
  simp only [wakefieldABF, gaussianPDFReal, NNReal.coe_add, sub_zero]
  rw [div_pow, Real.sq_sqrt hV0.le, Real.sqrt_div' _ hVW.le, Real.sqrt_mul h2pi,
    Real.sqrt_mul h2pi]
  have h1 : (0:ℝ) < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have h2 : (0:ℝ) < √(V:ℝ) := Real.sqrt_pos.2 hV0
  have h3 : (0:ℝ) < √((V:ℝ) + W) := Real.sqrt_pos.2 hVW
  rw [show ∀ a b c d : ℝ, a⁻¹ * b / (c⁻¹ * d) = c / a * (b / d) by intros; field_simp,
    ← Real.exp_sub]
  congr 1
  · field_simp
  · congr 1
    field_simp
    ring

/-- Wakefield's ABF is strictly positive on its sampling-variance domain. -/
theorem wakefieldABF_pos {V : ℝ≥0} (hV : V ≠ 0) (W : ℝ≥0) (b : ℝ) :
    0 < wakefieldABF V W b := by
  rw [wakefieldABF_eq hV]
  positivity

/-- The alternative marginal `N(0, V + W)` has density `wakefieldABF V W` with respect to the null
law `N(0, V)`. -/
theorem gaussianReal_eq_withDensity_wakefieldABF {V : ℝ≥0} (hV : V ≠ 0) (W : ℝ≥0) :
    gaussianReal 0 (V + W) =
      (gaussianReal 0 V).withDensity fun b => ENNReal.ofReal (wakefieldABF V W b) := by
  have hVW : V + W ≠ 0 := by positivity
  rw [gaussianReal_of_var_ne_zero _ hV, gaussianReal_of_var_ne_zero _ hVW,
    ← withDensity_mul _ (measurable_gaussianPDF _ _)
      (show Measurable fun b => ENNReal.ofReal (wakefieldABF V W b) from
        ENNReal.measurable_ofReal.comp
          ((measurable_gaussianPDFReal _ _).div (measurable_gaussianPDFReal _ _)))]
  congr 1
  funext b
  simp only [Pi.mul_apply, gaussianPDF, wakefieldABF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    mul_div_cancel₀ _ (gaussianPDFReal_pos _ _ _ hV).ne']

/-- **The ABF is the Bayes factor**: if `β ~ N(0, W)` and the sampling error `ε ~ N(0, V)` are
independent, the law of the estimate `β + ε` (alternative) has density `wakefieldABF V W` with
respect to the law of `ε` (null). -/
theorem rnDeriv_map_add_ae_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {β ε : Ω → ℝ} (hβ : Measurable β) (hε : Measurable ε)
    (hind : IndepFun β ε P) {V W : ℝ≥0} (hV : V ≠ 0) (hβl : P.map β = gaussianReal 0 W)
    (hεl : P.map ε = gaussianReal 0 V) :
    (P.map (fun ω => β ω + ε ω)).rnDeriv (P.map ε) =ᵐ[P.map ε]
      fun b => ENNReal.ofReal (wakefieldABF V W b) := by
  have hsum : P.map (fun ω => β ω + ε ω) = gaussianReal 0 (V + W) := by
    have := gaussianReal_add_gaussianReal_of_indepFun hind ⟨hβ.aemeasurable, hβl⟩
      ⟨hε.aemeasurable, hεl⟩
    rw [show (fun ω => β ω + ε ω) = β + ε from rfl, this, add_zero, add_comm]
  rw [hsum, hεl, gaussianReal_eq_withDensity_wakefieldABF hV W]
  exact Measure.rnDeriv_withDensity _ (ENNReal.measurable_ofReal.comp
    ((measurable_gaussianPDFReal _ _).div (measurable_gaussianPDFReal _ _)))

/-! ### Single-effect regression -/

section SingleEffect

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The marginal least-squares effect estimate `xᵀ y / xᵀ x` of a variant with genotype vector
`x`. -/
noncomputable def olsEffect (x y : EuclideanSpace ℝ n) : ℝ := ⟪x, y⟫ / ‖x‖ ^ 2

/-- The sampling variance `σ² / xᵀ x` of `olsEffect x y` for residual variance `σ²`. -/
noncomputable def olsVar (σ2 : ℝ≥0) (x : EuclideanSpace ℝ n) : ℝ≥0 := σ2 / ‖x‖₊ ^ 2

/-- The covariance `σ₀² x xᵀ + σ² I` of `y = x β + e` for `β ~ N(0, σ₀²)` and
`e ~ N(0, σ² I)`. -/
noncomputable def serCov (σ2 σ02 : ℝ≥0) (x : EuclideanSpace ℝ n) : Matrix n n ℝ :=
  replicateCol Unit (ofLp x) * ((σ02 : ℝ) • (1 : Matrix Unit Unit ℝ)) *
      (replicateCol Unit (ofLp x))ᵀ + (σ2 : ℝ) • (1 : Matrix n n ℝ)

omit [DecidableEq n] in
/-- `(x xᵀ)(x xᵀ) = (xᵀ x) (x xᵀ)`. -/
private theorem colMulRow_mul_self (u : n → ℝ) :
    (replicateCol Unit u * replicateRow Unit u) * (replicateCol Unit u * replicateRow Unit u) =
      (u ⬝ᵥ u) • (replicateCol Unit u * replicateRow Unit u) := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (replicateRow Unit u), replicateRow_mul_replicateCol,
    show (of fun _ _ => u ⬝ᵥ u : Matrix Unit Unit ℝ) = (u ⬝ᵥ u) • 1 by ext; simp,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

omit [DecidableEq n] in
/-- `(x xᵀ) v = (xᵀ v) x`. -/
private theorem colMulRow_mulVec (u v : n → ℝ) :
    (replicateCol Unit u * replicateRow Unit u) *ᵥ v = (u ⬝ᵥ v) • u := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, replicateCol, replicateRow, Finset.mul_sum,
    mul_comm, mul_left_comm]

omit [Fintype n] in
/-- `serCov` as `σ₀² x xᵀ + σ² I`. -/
private theorem serCov_eq_smul_add (σ2 σ02 : ℝ≥0) (x : EuclideanSpace ℝ n) :
    serCov σ2 σ02 x = (σ02 : ℝ) • (replicateCol Unit (ofLp x) * replicateRow Unit (ofLp x)) +
      (σ2 : ℝ) • 1 := by
  rw [serCov, Matrix.mul_smul, Matrix.mul_one, transpose_replicateCol, Matrix.smul_mul]

/-- The Sherman–Morrison inverse of `serCov` is a right inverse. -/
private theorem serCov_mul_inv {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (σ02 : ℝ≥0) (x : EuclideanSpace ℝ n) :
    serCov σ2 σ02 x * ((σ2 : ℝ)⁻¹ • 1 - ((σ02 : ℝ) / (σ2 * (σ2 + σ02 * (ofLp x ⬝ᵥ ofLp x)))) •
      (replicateCol Unit (ofLp x) * replicateRow Unit (ofLp x))) = 1 := by
  have hσ' : (0 : ℝ) < σ2 := by positivity
  have ha : 0 ≤ ofLp x ⬝ᵥ ofLp x := dotProduct_self_star_nonneg (ofLp x)
  have hd : (0 : ℝ) < σ2 + σ02 * (ofLp x ⬝ᵥ ofLp x) := by positivity
  rw [serCov_eq_smul_add]
  set K := replicateCol Unit (ofLp x) * replicateRow Unit (ofLp x)
  set a := ofLp x ⬝ᵥ ofLp x
  have hK : K * K = a • K := colMulRow_mul_self _
  simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, hK, Matrix.one_mul,
    Matrix.mul_one, smul_smul]
  match_scalars
  · field_simp
    ring
  · field_simp

omit [DecidableEq n] in
/-- The inner product as a dot product. -/
private theorem inner_eq_dotProduct (x y : EuclideanSpace ℝ n) :
    ⟪x, y⟫ = ofLp x ⬝ᵥ ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

omit [DecidableEq n] in
/-- The squared norm as a dot product. -/
private theorem norm_sq_eq_dotProduct (x : EuclideanSpace ℝ n) :
    ‖x‖ ^ 2 = ofLp x ⬝ᵥ ofLp x := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]

/-- **Sherman–Morrison**: `(σ₀² x xᵀ + σ² I)⁻¹ = σ²⁻¹ I - σ₀² / (σ² (σ² + σ₀² xᵀx)) x xᵀ`. -/
private theorem serCov_inv {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (σ02 : ℝ≥0) (x : EuclideanSpace ℝ n) :
    (serCov σ2 σ02 x)⁻¹ = (σ2 : ℝ)⁻¹ • 1 -
      ((σ02 : ℝ) / (σ2 * (σ2 + σ02 * (ofLp x ⬝ᵥ ofLp x)))) •
        (replicateCol Unit (ofLp x) * replicateRow Unit (ofLp x)) :=
  inv_eq_right_inv (serCov_mul_inv hσ σ02 x)

/-- `serCov⁻¹` applied to a vector. -/
private theorem serCov_inv_mulVec {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (σ02 : ℝ≥0) (x : EuclideanSpace ℝ n)
    (v : n → ℝ) :
    (serCov σ2 σ02 x)⁻¹ *ᵥ v = (σ2 : ℝ)⁻¹ • v -
      ((σ02 : ℝ) / (σ2 * (σ2 + σ02 * (ofLp x ⬝ᵥ ofLp x))) * (ofLp x ⬝ᵥ v)) • ofLp x := by
  rw [serCov_inv hσ, sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec, colMulRow_mulVec, smul_smul]

/-- **Matrix determinant lemma**: `det (σ₀² x xᵀ + σ² I) = σ²ⁿ (1 + σ₀² xᵀx / σ²)`. -/
private theorem det_serCov {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (σ02 : ℝ≥0) (x : EuclideanSpace ℝ n) :
    (serCov σ2 σ02 x).det =
      (σ2 : ℝ) ^ Fintype.card n * (1 + σ02 / σ2 * (ofLp x ⬝ᵥ ofLp x)) := by
  have hσ' : (σ2 : ℝ) ≠ 0 := by positivity
  have h : serCov σ2 σ02 x = (σ2 : ℝ) • (1 + replicateCol Unit (((σ02 : ℝ) / σ2) • ofLp x) *
      replicateRow Unit (ofLp x)) := by
    rw [serCov_eq_smul_add, smul_add, add_comm]
    congr 1
    rw [replicateCol_smul, Matrix.smul_mul, smul_smul, mul_div_cancel₀ _ hσ']
  rw [h, det_smul, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul]

omit [DecidableEq n] in
/-- `olsVar σ2 x = σ² / xᵀx` as a real number. -/
private theorem coe_olsVar (σ2 : ℝ≥0) (x : EuclideanSpace ℝ n) :
    (olsVar σ2 x : ℝ) = σ2 / (ofLp x ⬝ᵥ ofLp x) := by
  rw [olsVar, NNReal.coe_div, NNReal.coe_pow, coe_nnnorm, norm_sq_eq_dotProduct]

omit [DecidableEq n] in
/-- `0 < xᵀx` for `x ≠ 0`. -/
private theorem dotProduct_self_pos {x : EuclideanSpace ℝ n} (hx : x ≠ 0) :
    0 < ofLp x ⬝ᵥ ofLp x := by
  rw [← norm_sq_eq_dotProduct]; positivity

/-- The quadratic form of `serCov⁻¹`. -/
private theorem dotProduct_serCov_inv_mulVec {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (σ02 : ℝ≥0)
    (x : EuclideanSpace ℝ n) (v : n → ℝ) :
    v ⬝ᵥ (serCov σ2 σ02 x)⁻¹ *ᵥ v = (σ2 : ℝ)⁻¹ * (v ⬝ᵥ v) -
      (σ02 : ℝ) / (σ2 * (σ2 + σ02 * (ofLp x ⬝ᵥ ofLp x))) * (ofLp x ⬝ᵥ v) ^ 2 := by
  rw [serCov_inv_mulVec hσ, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, dotProduct_comm v (ofLp x)]
  ring

omit [Fintype n] in
/-- `serCov σ2 σ02 x` is positive definite for `σ² > 0`. -/
theorem posDef_serCov [Finite n] {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (σ02 : ℝ≥0)
    (x : EuclideanSpace ℝ n) : (serCov σ2 σ02 x).PosDef := by
  have hS : ((σ02 : ℝ) • (1 : Matrix Unit Unit ℝ)).PosSemidef :=
    PosSemidef.one.smul σ02.coe_nonneg
  have hR : ((σ2 : ℝ) • (1 : Matrix n n ℝ)).PosDef :=
    PosDef.one.smul (by positivity : (0 : ℝ) < σ2)
  refine PosDef.posSemidef_add ?_ hR
  simpa [conjTranspose_eq_transpose_of_trivial] using
    hS.mul_mul_conjTranspose_same (replicateCol Unit (ofLp x))

/-- **The marginal law of the phenotype given the causal variant**: if `y = x β + e` with
`β ~ N(0, σ₀²)` independent of `e ~ N(0, σ² I)`, then `y` has density
`multivariateGaussianPDFReal 0 (serCov σ2 σ02 x)`. -/
theorem map_ser_eq_withDensity {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {β : Ω → EuclideanSpace ℝ Unit} {e : Ω → EuclideanSpace ℝ n}
    (hβ : Measurable β) (he : Measurable e) (hind : IndepFun β e P) {σ2 σ02 : ℝ≥0}
    (hσ : σ2 ≠ 0) (hβl : P.map β = multivariateGaussian 0 ((σ02 : ℝ) • 1))
    (hel : P.map e = multivariateGaussian 0 ((σ2 : ℝ) • 1)) (x : EuclideanSpace ℝ n) :
    P.map (fun ω => toEuclideanLin (replicateCol Unit (ofLp x)) (β ω) + e ω) =
      volume.withDensity fun y =>
        ENNReal.ofReal (multivariateGaussianPDFReal 0 (serCov σ2 σ02 x) y) := by
  rw [map_linear_add_of_indepFun hβ he hind (PosSemidef.one.smul σ02.coe_nonneg)
    (PosSemidef.one.smul σ2.coe_nonneg) hβl hel, map_zero, add_zero]
  exact multivariateGaussian_eq_withDensity 0 (posDef_serCov hσ σ02 x)

/-- **The regression Bayes factor is the Wakefield ABF** (Wang et al. 2020): the
density of `y` when variant `x` carries an `N(0, σ₀²)` effect, divided by its density with no
effect, is the ABF of the summary statistics `olsEffect x y` and `olsVar σ2 x`. -/
theorem multivariateGaussianPDFReal_serCov_div {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (σ02 : ℝ≥0)
    {x : EuclideanSpace ℝ n} (hx : x ≠ 0) (y : EuclideanSpace ℝ n) :
    multivariateGaussianPDFReal 0 (serCov σ2 σ02 x) y /
        multivariateGaussianPDFReal 0 (serCov σ2 0 x) y =
      wakefieldABF (olsVar σ2 x) σ02 (olsEffect x y) := by
  have hσ' : (0 : ℝ) < σ2 := by positivity
  have ha := dotProduct_self_pos hx
  have hV : olsVar σ2 x ≠ 0 := by
    rw [← NNReal.coe_ne_zero, coe_olsVar]; positivity
  have hdet := det_serCov hσ σ02 x
  have hdet0 := det_serCov hσ 0 x
  have hq := dotProduct_serCov_inv_mulVec hσ σ02 x (ofLp y)
  have hq0 := dotProduct_serCov_inv_mulVec hσ 0 x (ofLp y)
  simp only [NNReal.coe_zero, zero_div, zero_mul, add_zero, mul_one, zero_mul, sub_zero]
    at hdet0 hq0
  rw [wakefieldABF_eq hV, coe_olsVar, olsEffect, inner_eq_dotProduct, norm_sq_eq_dotProduct]
  simp only [multivariateGaussianPDFReal, sub_zero]
  rw [hdet, hdet0, hq, hq0]
  have hC : 0 < ((√(2 * Real.pi)) ^ Fintype.card n)⁻¹ := by
    have : 0 < √(2 * Real.pi) := Real.sqrt_pos.2 (by positivity); positivity
  have hD : 0 < 1 + σ02 / σ2 * (ofLp x ⬝ᵥ ofLp x) := by positivity
  have hP : 0 < √((σ2 : ℝ) ^ Fintype.card n) := Real.sqrt_pos.2 (by positivity)
  rw [mul_assoc, mul_assoc, mul_div_mul_left _ _ hC.ne', Real.sqrt_mul (by positivity),
    show ∀ p d e1 e2 : ℝ, p ≠ 0 → (p * d)⁻¹ * e1 / (p⁻¹ * e2) = d⁻¹ * (e1 / e2) from
      fun p d e1 e2 hp => by field_simp, ← Real.exp_sub, div_pow, Real.sq_sqrt (by positivity),
    ← Real.sqrt_inv]
  · congr 2
    · field_simp
    · field_simp
      ring
  · exact hP.ne'

/-- A finite probability distribution used as the prior over the single causal variant. -/
structure PriorWeights (ι : Type*) [Fintype ι] where
  /-- The prior probability of each variant. -/
  weight : ι → ℝ
  weight_nonneg : ∀ j, 0 ≤ weight j
  sum_weight : ∑ j, weight j = 1

instance {ι : Type*} [Fintype ι] : CoeFun (PriorWeights ι) fun _ => ι → ℝ :=
  ⟨PriorWeights.weight⟩

namespace PriorWeights

/-- A normalized non-negative finite prior assigns positive weight to some variant. -/
theorem exists_weight_pos {ι : Type*} [Fintype ι] (w : PriorWeights ι) :
    ∃ j, 0 < w j := by
  by_contra h
  push Not at h
  have hw : w.weight = 0 := funext fun j => le_antisymm (h j) (w.weight_nonneg j)
  have hsum := w.sum_weight
  simp [hw] at hsum

/-- Strictly positive evidence has a strictly positive prior-weighted marginal likelihood. -/
theorem evidence_pos {ι : Type*} [Fintype ι] (w : PriorWeights ι) {BF : ι → ℝ}
    (hBF : ∀ j, 0 < BF j) : 0 < ∑ j, w j * BF j := by
  refine Finset.sum_pos' (fun j _ => mul_nonneg (w.weight_nonneg j) (hBF j).le) ?_
  obtain ⟨j, hj⟩ := w.exists_weight_pos
  exact ⟨j, Finset.mem_univ j, mul_pos hj (hBF j)⟩

end PriorWeights

/-- Algebraic normalization of arbitrary weights times evidence. This is useful even outside the
probability domain; it takes Lean's value `0` when the denominator vanishes. -/
noncomputable def normalizedWeightedEvidence {ι : Type*} [Fintype ι]
    (w BF : ι → ℝ) (j : ι) : ℝ :=
  w j * BF j / ∑ k, w k * BF k

/-- Posterior inclusion probability from a normalized non-negative prior and variant evidence.
When every evidence value is positive, `PriorWeights.evidence_pos` makes the denominator strictly
positive, and `pip_nonneg` and `sum_pip` prove that these values form a probability distribution. -/
noncomputable def pip {ι : Type*} [Fintype ι] (w : PriorWeights ι)
    (BF : ι → ℝ) (j : ι) : ℝ :=
  normalizedWeightedEvidence w.weight BF j

/-- Posterior inclusion probabilities are non-negative when every evidence value is positive. -/
theorem pip_nonneg {ι : Type*} [Fintype ι] (w : PriorWeights ι) {BF : ι → ℝ}
    (hBF : ∀ j, 0 < BF j) (j : ι) : 0 ≤ pip w BF j := by
  exact div_nonneg (mul_nonneg (w.weight_nonneg j) (hBF j).le) (w.evidence_pos hBF).le

/-- Posterior inclusion probabilities normalize to one when every evidence value is positive. -/
theorem sum_pip {ι : Type*} [Fintype ι] (w : PriorWeights ι) {BF : ι → ℝ}
    (hBF : ∀ j, 0 < BF j) : ∑ j, pip w BF j = 1 := by
  simp only [pip, normalizedWeightedEvidence, ← Finset.sum_div]
  exact div_self (w.evidence_pos hBF).ne'

/-- The unconditional algebraic single-effect likelihood-ratio identity for arbitrary real
weights. Its right side is accurately named algebraic normalization, not a posterior probability. -/
theorem serLikelihoodRatio_eq_normalizedWeightedEvidence {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {σ2 : ℝ≥0} (hσ : σ2 ≠ 0)
    (σ02 : ℝ≥0) (X : ι → EuclideanSpace ℝ n) (hX : ∀ k, X k ≠ 0) (y : EuclideanSpace ℝ n)
    (j : ι) :
    w j * multivariateGaussianPDFReal 0 (serCov σ2 σ02 (X j)) y /
        ∑ k, w k * multivariateGaussianPDFReal 0 (serCov σ2 σ02 (X k)) y =
      normalizedWeightedEvidence w
        (fun k => wakefieldABF (olsVar σ2 (X k)) σ02 (olsEffect (X k) y)) j := by
  set L0 := multivariateGaussianPDFReal 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ)) y
  have hnull : ∀ x : EuclideanSpace ℝ n, serCov σ2 0 x = (σ2 : ℝ) • 1 := fun x => by
    simp [serCov]
  have hL0 : 0 < L0 := by
    have hdet : 0 < ((σ2 : ℝ) • (1 : Matrix n n ℝ)).det := by
      rw [det_smul, det_one, mul_one]; positivity
    unfold L0 multivariateGaussianPDFReal
    have : 0 < √(2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have : 0 < √(((σ2 : ℝ) • (1 : Matrix n n ℝ)).det) := Real.sqrt_pos.2 hdet
    positivity
  have hL : ∀ k, multivariateGaussianPDFReal 0 (serCov σ2 σ02 (X k)) y =
      L0 * wakefieldABF (olsVar σ2 (X k)) σ02 (olsEffect (X k) y) := fun k => by
    rw [← multivariateGaussianPDFReal_serCov_div hσ σ02 (hX k) y, hnull,
      mul_div_cancel₀ _ hL0.ne']
  simp only [hL, normalizedWeightedEvidence]
  simp_rw [mul_left_comm (w _) L0, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hL0.ne'

omit [DecidableEq n] in
/-- The prior-weighted single-effect evidence is strictly positive on the regression domain. -/
theorem serPosterior_evidence_pos {ι : Type*} [Fintype ι] (w : PriorWeights ι)
    {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (σ02 : ℝ≥0) (X : ι → EuclideanSpace ℝ n)
    (hX : ∀ k, X k ≠ 0) (y : EuclideanSpace ℝ n) :
    0 < ∑ k, w k * wakefieldABF (olsVar σ2 (X k)) σ02 (olsEffect (X k) y) := by
  apply w.evidence_pos
  intro k
  apply wakefieldABF_pos
  rw [← NNReal.coe_ne_zero, coe_olsVar]
  have := dotProduct_self_pos (hX k)
  positivity

/-- **Posterior inclusion probabilities of the single-effect regression** (Wang et al. 2020):
Bayes' rule for the causal variant with a normalized non-negative prior equals `pip` applied to
the strictly positive Wakefield ABFs. -/
theorem serPosterior_eq_pip {ι : Type*} [Fintype ι] (w : PriorWeights ι)
    {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (σ02 : ℝ≥0) (X : ι → EuclideanSpace ℝ n)
    (hX : ∀ k, X k ≠ 0) (y : EuclideanSpace ℝ n) (j : ι) :
    w j * multivariateGaussianPDFReal 0 (serCov σ2 σ02 (X j)) y /
        ∑ k, w k * multivariateGaussianPDFReal 0 (serCov σ2 σ02 (X k)) y =
      pip w (fun k => wakefieldABF (olsVar σ2 (X k)) σ02 (olsEffect (X k) y)) j := by
  simpa only [pip] using
    serLikelihoodRatio_eq_normalizedWeightedEvidence w.weight hσ σ02 X hX y j

/-- The posterior gain: `σ₀² Hᵀ (σ₀² H Hᵀ + σ² I)⁻¹ y = σ₀² / (σ₀² + s²) · β̂` for the
genotype column `H = x`. -/
private theorem serGain_apply {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (σ02 : ℝ≥0) {x : EuclideanSpace ℝ n}
    (hx : x ≠ 0) (y : EuclideanSpace ℝ n) :
    toEuclideanLin (((σ02 : ℝ) • (1 : Matrix Unit Unit ℝ)) * (replicateCol Unit (ofLp x))ᵀ *
        (serCov σ2 σ02 x)⁻¹) y =
      EuclideanSpace.single () ((σ02 : ℝ) / (σ02 + olsVar σ2 x) * olsEffect x y) := by
  have hσ' : (0 : ℝ) < σ2 := by positivity
  have ha := dotProduct_self_pos hx
  apply WithLp.ofLp_injective
  funext i
  change ((((σ02 : ℝ) • (1 : Matrix Unit Unit ℝ)) * (replicateCol Unit (ofLp x))ᵀ *
        (serCov σ2 σ02 x)⁻¹) *ᵥ ofLp y) i = _
  rw [← mulVec_mulVec, serCov_inv_mulVec hσ, transpose_replicateCol]
  simp only [Matrix.smul_mul, Matrix.one_mul, smul_eq_mul,
    mulVec, replicateRow, dotProduct_sub, dotProduct_smul,
    olsEffect, coe_olsVar, inner_eq_dotProduct, norm_sq_eq_dotProduct]
  simp only [Matrix.smul_apply, of_apply, smul_eq_mul, PiLp.single_eq_same]
  have hd : ∀ v : n → ℝ, (fun j => (σ02 : ℝ) * ofLp x j) ⬝ᵥ v = σ02 * (ofLp x ⬝ᵥ v) :=
    fun v => by simp [dotProduct, Finset.mul_sum, mul_assoc]
  simp only [hd]
  field_simp
  ring

/-- The posterior covariance: `σ₀² - σ₀² Hᵀ (σ₀² H Hᵀ + σ² I)⁻¹ H σ₀² = σ₀² s² / (σ₀² + s²)`. -/
private theorem serPostCov_eq {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (σ02 : ℝ≥0) {x : EuclideanSpace ℝ n}
    (hx : x ≠ 0) :
    ((σ02 : ℝ) • (1 : Matrix Unit Unit ℝ)) - ((σ02 : ℝ) • (1 : Matrix Unit Unit ℝ)) *
        (replicateCol Unit (ofLp x))ᵀ * (serCov σ2 σ02 x)⁻¹ *
        (replicateCol Unit (ofLp x) * ((σ02 : ℝ) • (1 : Matrix Unit Unit ℝ))) =
      ((σ02 : ℝ) * olsVar σ2 x / (σ02 + olsVar σ2 x)) • 1 := by
  have hσ' : (0 : ℝ) < σ2 := by positivity
  have ha := dotProduct_self_pos hx
  rw [serCov_inv hσ, transpose_replicateCol]
  ext i j
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_sub,
    Matrix.sub_mul, ← Matrix.mul_assoc, replicateRow_mul_replicateCol, coe_olsVar]
  have hentry : ((of fun _ _ => ofLp x ⬝ᵥ ofLp x : Matrix Unit Unit ℝ) *
      replicateRow Unit (ofLp x) * replicateCol Unit (ofLp x)) i j =
      (ofLp x ⬝ᵥ ofLp x) * (ofLp x ⬝ᵥ ofLp x) := by
    rw [Matrix.mul_assoc, replicateRow_mul_replicateCol]
    simp [Matrix.mul_apply]
  simp only [smul_of, Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one,
    of_apply, Pi.smul_apply]
  rw [hentry]
  field_simp
  ring

/-- **The effect posterior of the single-effect regression** (Wang et al. 2020): given
`y = x β + e` with `β ~ N(0, σ₀²)` independent of `e ~ N(0, σ² I)`, for almost every `y` the
effect is normal with mean `σ₀² / (σ₀² + s²) · β̂` and variance `σ₀² s² / (σ₀² + s²)`, where
`β̂ = olsEffect x y` and `s² = olsVar σ2 x`. -/
theorem condDistrib_ser_effect {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {β : Ω → EuclideanSpace ℝ Unit} {e : Ω → EuclideanSpace ℝ n}
    (hβ : Measurable β) (he : Measurable e) (hind : IndepFun β e P) {σ2 σ02 : ℝ≥0}
    (hσ : σ2 ≠ 0) (hβl : P.map β = multivariateGaussian 0 ((σ02 : ℝ) • 1))
    (hel : P.map e = multivariateGaussian 0 ((σ2 : ℝ) • 1)) {x : EuclideanSpace ℝ n}
    (hx : x ≠ 0) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin (replicateCol Unit (ofLp x)) (β ω) + e ω),
      condDistrib β (fun ω => toEuclideanLin (replicateCol Unit (ofLp x)) (β ω) + e ω) P y =
        multivariateGaussian
          (EuclideanSpace.single () ((σ02 : ℝ) / (σ02 + olsVar σ2 x) * olsEffect x y))
          (((σ02 : ℝ) * olsVar σ2 x / (σ02 + olsVar σ2 x)) • 1) := by
  have h := condDistrib_linear_add_of_indepFun hβ he hind (PosSemidef.one.smul σ02.coe_nonneg)
    (PosSemidef.one.smul σ2.coe_nonneg) hβl hel (replicateCol Unit (ofLp x))
    ((isUnit_iff_isUnit_det _).1 (posDef_serCov hσ σ02 x).isUnit)
  filter_upwards [h] with y hy
  rw [hy]
  simp only [map_zero, sub_zero, zero_add]
  congr 1
  · exact serGain_apply hσ σ02 hx y
  · exact serPostCov_eq hσ σ02 hx

end SingleEffect

/-! ### Colocalization -/

section Coloc

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The five coloc hypotheses: no association (`h0`), trait 1 only (`h1`), trait 2 only (`h2`),
two distinct causal variants (`h3`), one shared causal variant (`h4`). -/
inductive ColocHypothesis
  | h0 | h1 | h2 | h3 | h4
  deriving DecidableEq

instance : Fintype ColocHypothesis :=
  ⟨{.h0, .h1, .h2, .h3, .h4}, fun h => by cases h <;> simp⟩

private theorem univ_colocHypothesis :
    (Finset.univ : Finset ColocHypothesis) = {.h0, .h1, .h2, .h3, .h4} := rfl

/-- The hypothesis of a configuration `(causal variant of trait 1, causal variant of trait 2)`,
`none` meaning no causal variant. -/
def colocHypothesis : Option ι × Option ι → ColocHypothesis
  | (none, none) => .h0
  | (some _, none) => .h1
  | (none, some _) => .h2
  | (some j, some k) => if j = k then .h4 else .h3

/-- Non-negative coloc configuration-weight parameters (Giambartolomei et al. 2014): `p1`, `p2`,
`p12` for a variant causal for trait 1 only, trait 2 only, and both. The cited hypothesis weights
use null weight `1`. The bound also supports a separate normalized categorical-prior model. -/
structure ColocPrior (ι : Type*) [Fintype ι] where
  /-- Weight of a configuration in `h1`. -/
  p1 : ℝ
  /-- Weight of a configuration in `h2`. -/
  p2 : ℝ
  /-- Weight of a configuration in `h4`. -/
  p12 : ℝ
  p1_nonneg : 0 ≤ p1
  p2_nonneg : 0 ≤ p2
  p12_nonneg : 0 ≤ p12
  /-- The optional categorical priors leave non-negative mass for the null configuration. -/
  sum_le_one : (Fintype.card ι : ℝ) * p1 + Fintype.card ι * p2 +
    Fintype.card ι * (Fintype.card ι - 1) * (p1 * p2) + Fintype.card ι * p12 ≤ 1

namespace ColocPrior

variable (P : ColocPrior ι)

/-- The remaining null mass in the optional normalized categorical-prior model. -/
def p0 : ℝ :=
  1 - ((Fintype.card ι : ℝ) * P.p1 + Fintype.card ι * P.p2 +
    Fintype.card ι * (Fintype.card ι - 1) * (P.p1 * P.p2) + Fintype.card ι * P.p12)

/-- A normalized categorical prior, distinct from the cited coloc relative weights. -/
def categoricalPrior (S : Option ι × Option ι) : ℝ :=
  match colocHypothesis S with
  | .h0 => P.p0
  | .h1 => P.p1
  | .h2 => P.p2
  | .h3 => P.p1 * P.p2
  | .h4 => P.p12

/-- The cited coloc unnormalized configuration weight, whose H0 weight is `1`. -/
def weight (S : Option ι × Option ι) : ℝ :=
  match colocHypothesis S with
  | .h0 => 1
  | .h1 => P.p1
  | .h2 => P.p2
  | .h3 => P.p1 * P.p2
  | .h4 => P.p12

/-- Categorical configuration priors are non-negative. -/
theorem categoricalPrior_nonneg (S : Option ι × Option ι) : 0 ≤ P.categoricalPrior S := by
  have := P.p1_nonneg
  have := P.p2_nonneg
  have := P.p12_nonneg
  have h0 : 0 ≤ P.p0 := by
    have := P.sum_le_one
    unfold p0
    linarith
  unfold categoricalPrior
  split <;> first | assumption | positivity

/-- Cited coloc configuration weights are non-negative. -/
theorem weight_nonneg (S : Option ι × Option ι) : 0 ≤ P.weight S := by
  have := P.p1_nonneg
  have := P.p2_nonneg
  have := P.p12_nonneg
  unfold weight
  split <;> first | assumption | positivity

end ColocPrior

/-- The Bayes factor of a configuration against the null: the product of the two traits' Bayes
factors, `1` for a trait without a causal variant (the two studies are independent). -/
def colocBF (bf1 bf2 : ι → ℝ) (S : Option ι × Option ι) : ℝ :=
  S.1.elim 1 bf1 * S.2.elim 1 bf2

omit [Fintype ι] [DecidableEq ι] in
/-- A configuration Bayes factor is non-negative when both traits' Bayes factors are. -/
theorem colocBF_nonneg (bf1 bf2 : ι → ℝ) (hbf1 : ∀ j, 0 ≤ bf1 j)
    (hbf2 : ∀ j, 0 ≤ bf2 j) (S : Option ι × Option ι) : 0 ≤ colocBF bf1 bf2 S := by
  rcases S with ⟨a, b⟩
  cases a with
  | none =>
      cases b with
      | none => simp [colocBF]
      | some k => simpa [colocBF] using hbf2 k
  | some j =>
      cases b with
      | none => simpa [colocBF] using hbf1 j
      | some k => exact mul_nonneg (hbf1 j) (hbf2 k)

/-- The cited coloc closed-form algebraic scores. H0 has score `1`; H1--H4 retain the
per-configuration coefficients of Giambartolomei et al. (2014). They are unnormalized hypothesis
weights, and hence have a probability interpretation, when the Bayes factors are non-negative. -/
def colocClosedForm (P : ColocPrior ι) (bf1 bf2 : ι → ℝ) : ColocHypothesis → ℝ
  | .h0 => 1
  | .h1 => P.p1 * ∑ j, bf1 j
  | .h2 => P.p2 * ∑ k, bf2 k
  | .h3 => P.p1 * P.p2 * ((∑ j, bf1 j) * (∑ k, bf2 k) - ∑ j, bf1 j * bf2 j)
  | .h4 => P.p12 * ∑ j, bf1 j * bf2 j

/-- Closed forms for the optional normalized categorical-prior model. This differs from the cited
coloc formula only in using its remaining null mass rather than the cited H0 weight `1`. -/
def colocCategoricalClosedForm (P : ColocPrior ι) (bf1 bf2 : ι → ℝ) :
    ColocHypothesis → ℝ
  | .h0 => P.p0
  | .h1 => P.p1 * ∑ j, bf1 j
  | .h2 => P.p2 * ∑ k, bf2 k
  | .h3 => P.p1 * P.p2 * ((∑ j, bf1 j) * (∑ k, bf2 k) - ∑ j, bf1 j * bf2 j)
  | .h4 => P.p12 * ∑ j, bf1 j * bf2 j

/-- **The coloc closed forms** (Giambartolomei et al. 2014): the sum of unnormalized configuration
weight times Bayes factor over each hypothesis equals its closed form. -/
theorem sum_colocWeight_mul_colocBF (P : ColocPrior ι) (bf1 bf2 : ι → ℝ)
    (h : ColocHypothesis) :
    ∑ S ∈ Finset.univ.filter (fun S => colocHypothesis S = h), P.weight S * colocBF bf1 bf2 S =
      colocClosedForm P bf1 bf2 h := by
  have key : ∀ j k : ι, (if colocHypothesis (some j, some k) = h then
      P.weight (some j, some k) * colocBF bf1 bf2 (some j, some k) else 0) =
      (if h = .h4 then (if j = k then P.p12 * (bf1 j * bf2 k) else 0) else 0) +
      (if h = .h3 then P.p1 * P.p2 * (bf1 j * bf2 k) -
        (if j = k then P.p1 * P.p2 * (bf1 j * bf2 k) else 0) else 0) := by
    intro j k
    by_cases hjk : j = k <;> cases h <;>
      simp [colocHypothesis, ColocPrior.weight, colocBF, hjk]
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_option]
  simp only [Fintype.sum_option, key, Finset.sum_add_distrib]
  cases h
  case h3 =>
    simp only [reduceCtorEq, ↓reduceIte, Finset.sum_const_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, zero_add, colocHypothesis, colocClosedForm, mul_sub,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  all_goals
    simp [colocHypothesis, ColocPrior.weight, colocBF, colocClosedForm, Finset.mul_sum,
      Finset.sum_ite_eq]

omit [DecidableEq ι] in
/-- Cited coloc closed-form scores are non-negative on the Bayes-factor domain. -/
theorem colocClosedForm_nonneg (P : ColocPrior ι) (bf1 bf2 : ι → ℝ)
    (hbf1 : ∀ j, 0 ≤ bf1 j) (hbf2 : ∀ j, 0 ≤ bf2 j) (h : ColocHypothesis) :
    0 ≤ colocClosedForm P bf1 bf2 h := by
  classical
  rw [← sum_colocWeight_mul_colocBF]
  exact Finset.sum_nonneg fun S _ =>
    mul_nonneg (P.weight_nonneg S) (colocBF_nonneg bf1 bf2 hbf1 hbf2 S)

omit [DecidableEq ι] in
/-- Cited coloc evidence is strictly positive for non-negative Bayes factors because H0 has
unnormalized weight `1`. -/
theorem colocEvidence_pos (P : ColocPrior ι) (bf1 bf2 : ι → ℝ)
    (hbf1 : ∀ j, 0 ≤ bf1 j) (hbf2 : ∀ j, 0 ≤ bf2 j) :
    0 < ∑ h, colocClosedForm P bf1 bf2 h := by
  refine Finset.sum_pos' (fun h _ => colocClosedForm_nonneg P bf1 bf2 hbf1 hbf2 h) ?_
  exact ⟨.h0, Finset.mem_univ _, by simp [colocClosedForm]⟩

/-- The corresponding closed forms for the optional normalized categorical-prior model. -/
theorem sum_categoricalPrior_mul_colocBF (P : ColocPrior ι) (bf1 bf2 : ι → ℝ)
    (h : ColocHypothesis) :
    ∑ S ∈ Finset.univ.filter (fun S => colocHypothesis S = h),
        P.categoricalPrior S * colocBF bf1 bf2 S = colocCategoricalClosedForm P bf1 bf2 h := by
  have key : ∀ j k : ι, (if colocHypothesis (some j, some k) = h then
      P.categoricalPrior (some j, some k) * colocBF bf1 bf2 (some j, some k) else 0) =
      (if h = .h4 then (if j = k then P.p12 * (bf1 j * bf2 k) else 0) else 0) +
      (if h = .h3 then P.p1 * P.p2 * (bf1 j * bf2 k) -
        (if j = k then P.p1 * P.p2 * (bf1 j * bf2 k) else 0) else 0) := by
    intro j k
    by_cases hjk : j = k <;> cases h <;>
      simp [colocHypothesis, ColocPrior.categoricalPrior, colocBF, hjk]
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_option]
  simp only [Fintype.sum_option, key, Finset.sum_add_distrib]
  cases h
  case h3 =>
    simp only [reduceCtorEq, ↓reduceIte, Finset.sum_const_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, zero_add, colocHypothesis, colocCategoricalClosedForm,
      mul_sub, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  all_goals
    simp [colocHypothesis, ColocPrior.categoricalPrior, colocBF, colocCategoricalClosedForm,
      Finset.mul_sum, Finset.sum_ite_eq]


/-- The brute-force total cited weight is the sum of the five closed forms. -/
private theorem sum_weight_mul_colocBF (P : ColocPrior ι) (bf1 bf2 : ι → ℝ) :
    ∑ S, P.weight S * colocBF bf1 bf2 S = ∑ h, colocClosedForm P bf1 bf2 h := by
  rw [← Finset.sum_fiberwise Finset.univ colocHypothesis]
  exact Finset.sum_congr rfl fun h _ => sum_colocWeight_mul_colocBF P bf1 bf2 h

/-- The brute-force categorical total is the sum of its five closed forms. -/
private theorem sum_categoricalPrior_mul_colocBF_total (P : ColocPrior ι)
    (bf1 bf2 : ι → ℝ) :
    ∑ S, P.categoricalPrior S * colocBF bf1 bf2 S =
      ∑ h, colocCategoricalClosedForm P bf1 bf2 h := by
  rw [← Finset.sum_fiberwise Finset.univ colocHypothesis]
  exact Finset.sum_congr rfl fun h _ => sum_categoricalPrior_mul_colocBF P bf1 bf2 h

/-- The optional categorical configuration priors sum to one. -/
theorem ColocPrior.sum_categoricalPrior (P : ColocPrior ι) :
    ∑ S, P.categoricalPrior S = 1 := by
  have h := sum_categoricalPrior_mul_colocBF_total P (1 : ι → ℝ) 1
  have h1 : ∀ S : Option ι × Option ι, colocBF (1 : ι → ℝ) 1 S = 1 := fun ⟨a, b⟩ => by
    cases a <;> cases b <;> simp [colocBF]
  simp only [h1, mul_one] at h
  rw [h, univ_colocHypothesis]
  simp [colocCategoricalClosedForm, ColocPrior.p0]
  ring

/-- The unconditional algebraic coloc normalization identity: each hypothesis's configuration
score divided by the total score equals its closed-form score divided by the closed-form total.
For arbitrary real `bf1` and `bf2` these ratios need not be probabilities. See
`colocPosterior_nonneg` and `sum_colocPosterior_eq_one` for the probability-domain results. -/
theorem colocPosterior_eq (P : ColocPrior ι) (bf1 bf2 : ι → ℝ) (h : ColocHypothesis) :
    (∑ S ∈ Finset.univ.filter (fun S => colocHypothesis S = h), P.weight S * colocBF bf1 bf2 S) /
        ∑ S, P.weight S * colocBF bf1 bf2 S =
      colocClosedForm P bf1 bf2 h / ∑ h', colocClosedForm P bf1 bf2 h' := by
  rw [sum_colocWeight_mul_colocBF, sum_weight_mul_colocBF]

omit [DecidableEq ι] in
/-- Normalized cited coloc hypothesis weights are non-negative for non-negative Bayes factors. -/
theorem colocPosterior_nonneg (P : ColocPrior ι) (bf1 bf2 : ι → ℝ)
    (hbf1 : ∀ j, 0 ≤ bf1 j) (hbf2 : ∀ j, 0 ≤ bf2 j) (h : ColocHypothesis) :
    0 ≤ colocClosedForm P bf1 bf2 h / ∑ h', colocClosedForm P bf1 bf2 h' := by
  exact div_nonneg (colocClosedForm_nonneg P bf1 bf2 hbf1 hbf2 h)
    (colocEvidence_pos P bf1 bf2 hbf1 hbf2).le

omit [DecidableEq ι] in
/-- Normalized cited coloc hypothesis weights sum to one for non-negative Bayes factors. -/
theorem sum_colocPosterior_eq_one (P : ColocPrior ι) (bf1 bf2 : ι → ℝ)
    (hbf1 : ∀ j, 0 ≤ bf1 j) (hbf2 : ∀ j, 0 ≤ bf2 j) :
    ∑ h, colocClosedForm P bf1 bf2 h / ∑ h', colocClosedForm P bf1 bf2 h' = 1 := by
  simp only [← Finset.sum_div]
  exact div_self (colocEvidence_pos P bf1 bf2 hbf1 hbf2).ne'

/-- The normalized posterior identity for the separate categorical-prior model. -/
theorem colocCategoricalPosterior_eq (P : ColocPrior ι) (bf1 bf2 : ι → ℝ)
    (h : ColocHypothesis) :
    (∑ S ∈ Finset.univ.filter (fun S => colocHypothesis S = h),
        P.categoricalPrior S * colocBF bf1 bf2 S) /
        ∑ S, P.categoricalPrior S * colocBF bf1 bf2 S =
      colocCategoricalClosedForm P bf1 bf2 h /
        ∑ h', colocCategoricalClosedForm P bf1 bf2 h' := by
  rw [sum_categoricalPrior_mul_colocBF, sum_categoricalPrior_mul_colocBF_total]

end Coloc

/-! ### Credible sets -/

section CredibleSet

variable {ι : Type*} [Fintype ι]

/-- A `ρ`-credible set: its total posterior inclusion probability is at least `ρ`. -/
def IsCredibleSet (α : ι → ℝ) (ρ : ℝ) (S : Finset ι) : Prop := ρ ≤ ∑ j ∈ S, α j

/-- The first `k` variants in the order `σ`. -/
def sortedPrefix (σ : Fin (Fintype.card ι) ≃ ι) (k : ℕ) : Finset ι :=
  (Finset.univ.filter fun i : Fin (Fintype.card ι) => i.val < k).map σ.toEmbedding

/-- A prefix of length `k ≤ card ι` has `k` elements. -/
theorem card_sortedPrefix (σ : Fin (Fintype.card ι) ≃ ι) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    (sortedPrefix σ k).card = k := by
  rw [sortedPrefix, Finset.card_map, Fin.card_filter_val_lt, min_eq_right hk]

/-- The `k` largest values carry the most mass: if `σ` sorts `α` in decreasing order, no set of
`S.card` variants has more mass than the prefix of that length. -/
theorem sum_le_sum_sortedPrefix (α : ι → ℝ) {σ : Fin (Fintype.card ι) ≃ ι}
    (hσ : Antitone (α ∘ σ)) (S : Finset ι) :
    ∑ j ∈ S, α j ≤ ∑ j ∈ sortedPrefix σ S.card, α j := by
  set T : Finset (Fin (Fintype.card ι)) := S.map σ.symm.toEmbedding
  set Q : Finset (Fin (Fintype.card ι)) :=
    Finset.univ.filter fun i : Fin (Fintype.card ι) => i.val < S.card
  have hT : T.card = S.card := Finset.card_map _
  have hTN : S.card ≤ Fintype.card ι := by
    simpa [hT] using Finset.card_le_univ T
  have hQ : Q.card = S.card := by
    rw [Fin.card_filter_val_lt, min_eq_right hTN]
  have hS : ∑ j ∈ S, α j = ∑ i ∈ T, α (σ i) := by
    rw [Finset.sum_map]; simp
  have hP : ∑ j ∈ sortedPrefix σ S.card, α j = ∑ i ∈ Q, α (σ i) := by
    rw [sortedPrefix, Finset.sum_map]; rfl
  rw [hS, hP, ← Finset.sum_inter_add_sum_sdiff T Q, ← Finset.sum_inter_add_sum_sdiff Q T,
    Finset.inter_comm Q T]
  refine add_le_add_right ?_ _
  have hcard : (T \ Q).card = (Q \ T).card := by
    have h1 := Finset.card_sdiff_add_card_inter T Q
    have h2 := Finset.card_sdiff_add_card_inter Q T
    rw [Finset.inter_comm] at h2
    omega
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · have : T \ Q = ∅ := by
      rw [← Finset.card_eq_zero]
      have := Finset.card_le_card (Finset.sdiff_subset (s := T) (t := Q))
      omega
    have h' : Q \ T = ∅ := by
      rw [← Finset.card_eq_zero, ← hcard, this, Finset.card_empty]
    simp [this, h']
  · set c : Fin (Fintype.card ι) := ⟨S.card - 1, by omega⟩
    calc ∑ i ∈ T \ Q, α (σ i) ≤ (T \ Q).card • α (σ c) := by
          refine Finset.sum_le_card_nsmul _ _ _ fun i hi => hσ ?_
          simp only [Finset.mem_sdiff, Q, Finset.mem_filter, Finset.mem_univ, true_and,
            not_lt] at hi
          change c.val ≤ i.val
          simp only [c]
          omega
      _ = (Q \ T).card • α (σ c) := by rw [hcard]
      _ ≤ ∑ i ∈ Q \ T, α (σ i) := by
          refine Finset.card_nsmul_le_sum _ _ _ fun i hi => hσ ?_
          simp only [Finset.mem_sdiff, Q, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          change i.val ≤ c.val
          simp only [c]
          omega

/-- **The shortest credible prefix has minimum size** (Maller et al. 2012; Wang et al. 2020): if
`σ` sorts `α` in decreasing order and no prefix shorter than `k` is `ρ`-credible, every
`ρ`-credible set has at least `k` elements. -/
theorem le_card_of_isCredibleSet (α : ι → ℝ) {σ : Fin (Fintype.card ι) ≃ ι}
    (hσ : Antitone (α ∘ σ)) {ρ : ℝ} {k : ℕ}
    (hk : ∀ m < k, ¬IsCredibleSet α ρ (sortedPrefix σ m)) {S : Finset ι}
    (hS : IsCredibleSet α ρ S) : k ≤ S.card := by
  by_contra h
  exact hk S.card (by omega) (hS.trans (sum_le_sum_sortedPrefix α hσ S))

/-- **A minimum-size credible set exists and is a sorted prefix**: if the total mass is at least
`ρ`, some prefix of length `k` is `ρ`-credible, has `k` elements, and every `ρ`-credible set has
at least `k` elements. -/
theorem exists_minimal_credible_prefix (α : ι → ℝ) {σ : Fin (Fintype.card ι) ≃ ι}
    (hσ : Antitone (α ∘ σ)) {ρ : ℝ} (hρ : ρ ≤ ∑ j, α j) :
    ∃ k, IsCredibleSet α ρ (sortedPrefix σ k) ∧ (sortedPrefix σ k).card = k ∧
      ∀ S, IsCredibleSet α ρ S → k ≤ S.card := by
  classical
  have hall : IsCredibleSet α ρ (sortedPrefix σ (Fintype.card ι)) := by
    have : sortedPrefix σ (Fintype.card ι) = Finset.univ :=
      Finset.eq_univ_of_card _ (card_sortedPrefix σ le_rfl)
    rw [IsCredibleSet, this]
    exact hρ
  have hex : ∃ k, IsCredibleSet α ρ (sortedPrefix σ k) := ⟨_, hall⟩
  have hle : Nat.find hex ≤ Fintype.card ι := Nat.find_min' hex hall
  exact ⟨Nat.find hex, Nat.find_spec hex, card_sortedPrefix σ hle,
    fun S hS => le_card_of_isCredibleSet α hσ (fun m hm => Nat.find_min hex hm) hS⟩

end CredibleSet

end MathlibExt.Biology.StatisticalGenetics.FineMapping
