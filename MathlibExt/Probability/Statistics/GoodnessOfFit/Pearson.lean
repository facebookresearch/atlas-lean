/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.CochranTheorem
public import MathlibExt.Probability.Statistics.MultivariateCLT
public import MathlibExt.Probability.Statistics.DeltaMethod
public import MathlibExt.Probability.Statistics.Slutsky

/-!
# Pearson's chi-square goodness-of-fit statistic: fixed-cell asymptotics

Let `X 0, X 1, …` be i.i.d. observations in a finite set `ι` of `k` cells with cell
probabilities `pᵢ = P(X 0 = i)`, and let `Nᵢ = #{j < n | X j = i}` be the cell counts (the
classical multinomial `Mult(n, p)` vector; that identification of the law is standard and is
neither used nor proved here). Pearson's statistic is
`χ²ₙ = ∑ᵢ (Nᵢ - n pᵢ)² / (n pᵢ)`.

## Main definitions

* `ProbabilityTheory.cellCount X n ω`: the cell counts of the first `n` observations.
* `ProbabilityTheory.pearsonStatistic n p N`: `∑ᵢ (Nᵢ - n pᵢ)² / (n pᵢ)`.
* `ProbabilityTheory.pearsonResidual n p N`: the residual vector `((Nᵢ - n pᵢ) / √(n pᵢ))ᵢ` in
  `EuclideanSpace ℝ ι`, whose squared norm is the statistic (`norm_sq_pearsonResidual`).

## Main results

* `tendstoInDistribution_pearsonResidual`: for `pᵢ > 0`, the residual vector converges in
  distribution to `P_K Z`, the orthogonal projection of a standard Gaussian onto the hyperplane
  `K = (√p)ᗮ` of dimension `k - 1`.
* `hasLaw_inner_starProjection_orthogonal_sqrt`: that limit has covariance `I - √p √pᵀ`, the
  weighted multinomial covariance; it is singular in the direction `√p`.
* `tendstoInDistribution_pearsonStatistic`: **Pearson's theorem**, `χ²ₙ → χ²_{k-1}` in
  distribution (simple null hypothesis, `k ≥ 2`, all `pᵢ > 0`).
* `tendstoInDistribution_pearsonStatistic_fitted`: with cell probabilities `p(θ̂)` estimated
  by an efficient grouped-count estimator of a differentiable model with weighted tangent space
  `V`, the fitted statistic converges to `χ²_{k-1-dim V}`;
  `tendstoInDistribution_pearsonStatistic_fitted_of_injective` is the `χ²_{k-1-s}` form for an
  identifiable model with `s` parameters.

## Method

The weighted centered indicators `((1{X j = i} - pᵢ) / √pᵢ)ᵢ` are i.i.d. with mean `0` and
covariance `I - √p √pᵀ`, the projection onto `K`. The multivariate central limit theorem
(`tendstoInDistribution_inv_sqrt_smul_sum_sub`, which allows a singular covariance) with limit
`P_K Z` gives the residual limit; no inverse of the multinomial covariance is used. Squaring the
norm and Cochran's theorem in projection form (`stdGaussian_map_norm_sq_starProjection`) give
`χ²_{dim K} = χ²_{k-1}`. With estimated parameters, the delta method applied jointly to the
residuals and `θ̂` replaces `P_K Z` by `P_K Z - P_V P_K Z = P_{Vᗮ ⊓ K} Z`, and Cochran's theorem
on `Vᗮ ⊓ K` gives `k - 1 - dim V` degrees of freedom.

## Boundary cases

* All cell probabilities must be positive. A cell with `pᵢ = 0` has `Nᵢ = 0` almost surely and
  contributes `0 / 0 = 0` (Lean's convention), so one expects the degrees of freedom to drop
  to `#{i | pᵢ > 0} - 1`; that general statement is not proved here. The test file proves a
  two-cell example where the statistic is identically `0` and does not converge to `χ²₁`.
* `k ≥ 2` (respectively `dim V + 1 < k`) is needed: `chiSquareMeasure 0` is the zero measure,
  not the Dirac mass at `0`.
* The fitted theorem needs the efficient-estimator expansion as a hypothesis; it is not
  derived here from the likelihood equations, and inefficient estimators are not covered.
* Sparse-cell (`n pᵢ` bounded) and growing-cell asymptotics are not covered: the number of
  cells and the cell probabilities are fixed as `n → ∞`.

## References

* K. Pearson, *On the criterion that a given system of deviations from the probable in the case
  of a correlated system of variables is such that it can be reasonably supposed to have arisen
  from random sampling*, Philos. Mag. (5) 50 (1900), 157–175.
* R. A. Fisher, *The conditions under which χ² measures the discrepancy between observation and
  hypothesis*, J. Roy. Statist. Soc. 87 (1924), 442–450.
* H. Cramér, *Mathematical Methods of Statistics*, Princeton (1946), §§30.1–30.3.
* M. W. Birch, *A new proof of the Pearson–Fisher theorem*, Ann. Math. Statist. 35 (1964),
  817–824.
* H. Chernoff and E. L. Lehmann, *The use of maximum likelihood estimates in χ² tests for
  goodness of fit*, Ann. Math. Statist. 25 (1954), 579–586.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge (1998), §17.
-/

@[expose] public section

open MeasureTheory Filter Finset Module
open scoped Real RealInnerProductSpace

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-! ### Cell counts and the statistic -/

/-- The cell counts of the first `n` categorical observations `X 0, …, X (n - 1)`:
`cellCount X n ω i = #{k < n | X k ω = i}`, as a real number. For i.i.d. observations with cell
probabilities `p` this is the classical multinomial `Mult(n, p)` count vector (that
identification of its law is standard and not used or proved here). -/
noncomputable def cellCount [DecidableEq ι] {Ω : Type*} (X : ℕ → Ω → ι) (n : ℕ) (ω : Ω)
    (i : ι) : ℝ :=
  ∑ k ∈ range n, if X k ω = i then 1 else 0

/-- **Pearson's chi-square statistic** `∑ᵢ (Nᵢ - n pᵢ)² / (n pᵢ)` of the cell counts `N` against
the cell probabilities `p` with `n` observations. A cell with `n pᵢ = 0` contributes `0` (Lean's
`x / 0 = 0`). -/
noncomputable def pearsonStatistic (n : ℕ) (p N : ι → ℝ) : ℝ :=
  ∑ i, (N i - n * p i) ^ 2 / (n * p i)

/-- The vector of **Pearson residuals** `(Nᵢ - n pᵢ) / √(n pᵢ)` in `EuclideanSpace ℝ ι`; its
squared norm is Pearson's statistic (`norm_sq_pearsonResidual`). -/
noncomputable def pearsonResidual (n : ℕ) (p N : ι → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => (N i - n * p i) / √(n * p i)

/-- Pearson's statistic is the squared norm of the residual vector, for nonnegative cell
probabilities (zero cells contribute `0` to both sides). -/
theorem norm_sq_pearsonResidual {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (n : ℕ) (N : ι → ℝ) :
    ‖pearsonResidual n p N‖ ^ 2 = pearsonStatistic n p N := by
  rw [EuclideanSpace.norm_sq_eq, pearsonStatistic]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [pearsonResidual, Real.norm_eq_abs, sq_abs, div_pow]
  rw [Real.sq_sqrt (mul_nonneg n.cast_nonneg (hp i))]

/-- The weighted centered indicator `((1{x = i} - pᵢ) / √pᵢ)ᵢ` of one observation `x`. -/
private noncomputable def increment [DecidableEq ι] (p : ι → ℝ) (x : ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => ((if x = i then 1 else 0) - p i) / √(p i)

/-- The unit vector `(√pᵢ)ᵢ`. -/
private noncomputable def sqrtVec (p : ι → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => √(p i)

omit [Fintype ι] in
private theorem pearsonResidual_cellCount [DecidableEq ι] {Ω : Type*} {p : ι → ℝ}
    (X : ℕ → Ω → ι) (n : ℕ) (ω : Ω) :
    pearsonResidual n p (cellCount X n ω) = (√n)⁻¹ • ∑ k ∈ range n, increment p (X k ω) := by
  ext i
  simp only [pearsonResidual, increment, cellCount, PiLp.smul_apply, WithLp.ofLp_sum,
    Finset.sum_apply, smul_eq_mul]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
    Real.sqrt_mul n.cast_nonneg, ← div_div, div_eq_inv_mul (_ / _)]
  ring

private theorem inner_increment [DecidableEq ι] {p : ι → ℝ} (x : ι) (t : EuclideanSpace ℝ ι) :
    ⟪increment p x, t⟫ = t x / √(p x) - ⟪sqrtVec p, t⟫ := by
  have h : ∀ j, t j * (((if x = j then 1 else 0) - p j) / √(p j)) =
      (if x = j then t j / √(p j) else 0) - t j * √(p j) := by
    intro j
    have := Real.div_sqrt (x := p j)
    split_ifs <;> linear_combination (-t j) * this
  simp only [increment, sqrtVec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

private theorem inner_sqrtVec (p : ι → ℝ) (t : EuclideanSpace ℝ ι) :
    ⟪sqrtVec p, t⟫ = ∑ j, √(p j) * t j := by
  simp [sqrtVec, PiLp.inner_apply, mul_comm]

private theorem norm_sq_sqrtVec {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) :
    ‖sqrtVec p‖ ^ 2 = ∑ i, p i := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [sqrtVec, Real.sq_sqrt (hp _)]

/-- The orthogonal projection onto the complement of a unit vector `u` has squared norm
`‖t‖² - ⟪u, t⟫²`. -/
private theorem norm_sq_starProjection_orthogonal_unit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {u : E} (hu : ‖u‖ = 1) (t : E) :
    ‖(ℝ ∙ u)ᗮ.starProjection t‖ ^ 2 = ‖t‖ ^ 2 - ⟪u, t⟫ ^ 2 := by
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_unit_singleton ℝ hu,
    norm_sub_sq_real, real_inner_smul_right, norm_smul, real_inner_comm, hu]
  simp only [Real.norm_eq_abs, mul_one, sq_abs]
  ring

section Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

private theorem integral_comp_eq_sum {Y : Ω → ι} (hY : AEMeasurable Y P) {p : ι → ℝ}
    (hp : ∀ i, P.real (Y ⁻¹' {i}) = p i) (g : ι → ℝ) :
    ∫ ω, g (Y ω) ∂P = ∑ j, p j * g j := by
  rw [← integral_map hY Measurable.of_discrete.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, ← hp j, measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable hY (measurableSet_singleton j)]

private theorem sum_eq_one {Y : Ω → ι} (hY : AEMeasurable Y P) {p : ι → ℝ}
    (hp : ∀ i, P.real (Y ⁻¹' {i}) = p i) : ∑ j, p j = 1 := by
  simpa using (integral_comp_eq_sum hY hp fun _ => 1).symm

omit [Fintype ι] in
private theorem memLp_comp [Finite ι] {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] {Y : Ω → ι} (hY : AEMeasurable Y P) (f : ι → F) :
    MemLp (fun ω => f (Y ω)) 2 P :=
  (memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable hY).1 MemLp.of_discrete

/-- The mean of `tⱼ / √pⱼ - ⟪√p, t⟫` under `p` is `0`. -/
private theorem sum_mul_sub_inner_eq_zero {Y : Ω → ι} (hY : AEMeasurable Y P) {p : ι → ℝ}
    (hp : ∀ i, P.real (Y ⁻¹' {i}) = p i) (t : EuclideanSpace ℝ ι) :
    ∑ j, p j * (t j / √(p j) - ⟪sqrtVec p, t⟫) = 0 := by
  have hm : ∀ j, p j * (t j / √(p j) - ⟪sqrtVec p, t⟫) =
      √(p j) * t j - ⟪sqrtVec p, t⟫ * p j := by
    intro j
    rw [mul_sub, mul_div_assoc', mul_div_right_comm, Real.div_sqrt]
    ring
  rw [Finset.sum_congr rfl fun j _ => hm j, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_eq_one hY hp, mul_one, inner_sqrtVec, sub_self]

private theorem integral_increment [DecidableEq ι] {Y : Ω → ι} (hY : AEMeasurable Y P) {p : ι → ℝ}
    (hp : ∀ i, P.real (Y ⁻¹' {i}) = p i) : ∫ ω, increment p (Y ω) ∂P = 0 := by
  refine ext_inner_left ℝ fun t => ?_
  rw [inner_zero_right, ← integral_inner ((memLp_comp hY _).integrable one_le_two) t]
  simp_rw [← real_inner_comm t, inner_increment]
  rw [integral_comp_eq_sum hY hp fun j => t j / √(p j) - ⟪sqrtVec p, t⟫]
  exact sum_mul_sub_inner_eq_zero hY hp t

private theorem variance_inner_increment [DecidableEq ι] {Y : Ω → ι} (hY : AEMeasurable Y P)
    {p : ι → ℝ} (hp : ∀ i, P.real (Y ⁻¹' {i}) = p i) (hpos : ∀ i, 0 < p i)
    (t : EuclideanSpace ℝ ι) :
    Var[fun ω => ⟪increment p (Y ω), t⟫; P] = ‖t‖ ^ 2 - ⟪sqrtVec p, t⟫ ^ 2 := by
  have hc : ∑ j, √(p j) * t j = ⟪sqrtVec p, t⟫ := (inner_sqrtVec p t).symm
  have h1 := sum_mul_sub_inner_eq_zero hY hp t
  simp_rw [inner_increment]
  set c := ⟪sqrtVec p, t⟫
  rw [variance_of_integral_eq_zero (memLp_comp hY fun j => t j / √(p j) - c).aemeasurable
    ((integral_comp_eq_sum hY hp fun j => t j / √(p j) - c).trans h1)]
  rw [integral_comp_eq_sum hY hp fun j => (t j / √(p j) - c) ^ 2]
  have h2 : ∀ j, p j * (t j / √(p j) - c) ^ 2 =
      t j ^ 2 - 2 * c * (√(p j) * t j) + c ^ 2 * p j := by
    intro j
    have hp' : p j = √(p j) ^ 2 := (Real.sq_sqrt (hpos j).le).symm
    have hs0 : √(p j) ≠ 0 := (Real.sqrt_pos.2 (hpos j)).ne'
    generalize √(p j) = s at hp' hs0 ⊢
    rw [hp']
    field_simp
    ring
  rw [Finset.sum_congr rfl fun j _ => h2 j, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_eq_one hY hp, EuclideanSpace.norm_sq_eq, hc]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

/-- Under the standard Gaussian law, `⟪P_K z, t⟫` is centered normal with variance
`‖P_K t‖²`. -/
private theorem hasLaw_inner_starProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K : Submodule ℝ E) (t : E) :
    HasLaw (fun z => ⟪K.starProjection z, t⟫)
      (gaussianReal 0 (‖K.starProjection t‖ ^ 2).toNNReal) (stdGaussian E) := by
  have hfun : (fun z => ⟪K.starProjection z, t⟫) = innerSL ℝ (K.starProjection t) := by
    ext z
    change ⟪K.starProjection z, t⟫ = ⟪K.starProjection t, z⟫
    rw [Submodule.inner_starProjection_left_eq_right]
    exact real_inner_comm _ _
  refine ⟨by fun_prop, ?_⟩
  rw [hfun, IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm]

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
/-- **The singular multinomial Gaussian.** For a probability vector `p`, the projection
`P_K Z` of a standard Gaussian `Z` on `EuclideanSpace ℝ ι` onto `K = (√p)ᗮ` (the limit in
`tendstoInDistribution_pearsonResidual`) has every coordinate projection `⟪P_K Z, t⟫` centered
normal with variance `‖t‖² - ⟪√p, t⟫²`: its covariance is `I - √p √pᵀ`, the multinomial
covariance `diag p - p pᵀ` in the weighted coordinates `xᵢ / √pᵢ`. It is singular: the
variance in the direction `t = √p` is `0`. -/
theorem hasLaw_inner_starProjection_orthogonal_sqrt {p : ι → ℝ} (hp₀ : ∀ i, 0 ≤ p i)
    (hp₁ : ∑ i, p i = 1) (t : EuclideanSpace ℝ ι) :
    HasLaw
      (fun z => ⟪(ℝ ∙ (WithLp.toLp 2 fun i => √(p i) : EuclideanSpace ℝ ι))ᗮ.starProjection z, t⟫)
      (gaussianReal 0
        (‖t‖ ^ 2 - ⟪(WithLp.toLp 2 fun i => √(p i) : EuclideanSpace ℝ ι), t⟫ ^ 2).toNNReal)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  have h := norm_sq_sqrtVec hp₀
  rw [hp₁] at h
  have hu : ‖sqrtVec p‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  change HasLaw (fun z => ⟪(ℝ ∙ sqrtVec p)ᗮ.starProjection z, t⟫)
    (gaussianReal 0 (‖t‖ ^ 2 - ⟪sqrtVec p, t⟫ ^ 2).toNNReal) _
  rw [← norm_sq_starProjection_orthogonal_unit hu t]
  exact hasLaw_inner_starProjection _ t

/-- Convergence in distribution depends on the limit only through its law.

Copied verbatim from the private helper of the same name in
`MathlibExt.Probability.Statistics.LikelihoodRatioTests` (that file is outside this task's
scope, so it is not made public here); the two copies should be merged into one public lemma. -/
private theorem tendstoInDistribution_of_hasLaw {Ω₂ Ω₃ : Type*} [MeasurableSpace Ω₂]
    [MeasurableSpace Ω₃] {P₂ : Measure Ω₂} {P₃ : Measure Ω₃} [IsProbabilityMeasure P₂]
    [IsProbabilityMeasure P₃] {A : ℕ → Ω → ℝ} {Y : Ω₂ → ℝ} {Z : Ω₃ → ℝ} {ρ : Measure ℝ}
    (h : TendstoInDistribution A atTop Y (fun _ => P) P₂) (hY : HasLaw Y ρ P₂)
    (hZ : HasLaw Z ρ P₃) :
    TendstoInDistribution A atTop Z (fun _ => P) P₃ where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    convert h.tendsto using 3
    exact congrArg nhds (Subtype.ext (hZ.map_eq.trans hY.map_eq.symm))

private theorem norm_sqrtVec {Y : Ω → ι} (hY : AEMeasurable Y P) {p : ι → ℝ}
    (hp : ∀ i, P.real (Y ⁻¹' {i}) = p i) : ‖sqrtVec p‖ = 1 := by
  have h := norm_sq_sqrtVec (p := p) fun i => (hp i) ▸ measureReal_nonneg
  rw [sum_eq_one hY hp] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
private theorem finrank_orthogonal_sqrtVec {p : ι → ℝ} (hu : ‖sqrtVec p‖ = 1) :
    finrank ℝ (ℝ ∙ sqrtVec p)ᗮ = Fintype.card ι - 1 := by
  have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ sqrtVec p)
  rw [finrank_span_singleton (norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)),
    finrank_euclideanSpace] at h
  omega

/-- **The Pearson residual vector is asymptotically a singular multinomial Gaussian.** For
i.i.d. categorical observations with all cell probabilities `pᵢ > 0`, the Pearson residuals
`((Nᵢ - n pᵢ) / √(n pᵢ))ᵢ` converge in distribution to `P_K Z`, where `Z` is standard Gaussian
on `EuclideanSpace ℝ ι` and `P_K` is the orthogonal projection onto the hyperplane
`K = (√p)ᗮ`. The limit covariance `I - √p √pᵀ` is singular (the limit is orthogonal to `√p`);
no invertibility of the multinomial covariance is used. -/
theorem tendstoInDistribution_pearsonResidual [DecidableEq ι] {X : ℕ → Ω → ι} {p : ι → ℝ}
    (hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = p i) (hpos : ∀ i, 0 < p i)
    (hindep : iIndepFun X P) (hident : ∀ k, IdentDistrib (X k) (X 0) P P) :
    TendstoInDistribution (fun n ω => pearsonResidual n p (cellCount X n ω)) atTop
      (fun z => (ℝ ∙ (WithLp.toLp 2 fun i => √(p i) : EuclideanSpace ℝ ι))ᗮ.starProjection z)
      (fun _ => P) (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hY : AEMeasurable (X 0) P := (hident 0).aemeasurable_fst
  have hu : ‖sqrtVec p‖ = 1 := norm_sqrtVec hY hX0
  have hlaw : ∀ t : EuclideanSpace ℝ ι,
      HasLaw (fun z => ⟪(ℝ ∙ sqrtVec p)ᗮ.starProjection z, t⟫)
        (gaussianReal 0 (Var[fun ω => ⟪increment p (X 0 ω), t⟫; P]).toNNReal)
        (stdGaussian (EuclideanSpace ℝ ι)) := by
    intro t
    rw [variance_inner_increment hY hX0 hpos t,
      ← norm_sq_starProjection_orthogonal_unit hu t]
    exact hasLaw_inner_starProjection _ t
  have hclt := tendstoInDistribution_inv_sqrt_smul_sum_sub
    (X := fun k ω => increment p (X k ω)) (by fun_prop) hlaw (memLp_comp hY _)
    (hindep.comp (fun _ => increment p) fun _ => Measurable.of_discrete)
    (fun k => (hident k).comp (u := increment p) Measurable.of_discrete)
  rw [integral_increment hY hX0] at hclt
  change TendstoInDistribution _ atTop (fun z => (ℝ ∙ sqrtVec p)ᗮ.starProjection z) _ _
  convert hclt using 3 with n ω
  rw [smul_zero, sub_zero, pearsonResidual_cellCount]

/-- **Pearson's chi-square theorem** (simple null hypothesis, fixed cells). Let `X 0, X 1, …` be
i.i.d. observations in a finite set `ι` of `k ≥ 2` cells, with cell probabilities
`P(X 0 = i) = pᵢ > 0`. Then Pearson's statistic `∑ᵢ (Nᵢ - n pᵢ)² / (n pᵢ)` of the cell counts
`N = cellCount X n` converges in distribution to the chi-square law with `k - 1` degrees of
freedom.

The limit is derived from the singular Gaussian limit of the Pearson residuals
(`tendstoInDistribution_pearsonResidual`): the statistic is the squared norm of the residual
vector, and the squared norm of the projection of a standard Gaussian onto the rank-`(k - 1)`
hyperplane `(√p)ᗮ` is `χ²_{k-1}` by Cochran's theorem (`stdGaussian_map_norm_sq_starProjection`).
The assumption `k ≥ 2` is needed: for `k = 1` the statistic is identically `0` while
`chiSquareMeasure 0` is the zero measure. -/
theorem tendstoInDistribution_pearsonStatistic [DecidableEq ι] {X : ℕ → Ω → ι} {p : ι → ℝ}
    (hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = p i) (hpos : ∀ i, 0 < p i)
    (hindep : iIndepFun X P) (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hk : 2 ≤ Fintype.card ι) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (chiSquareMeasure (Fintype.card ι - 1)) P') :
    TendstoInDistribution (fun n ω => pearsonStatistic n p (cellCount X n ω)) atTop Z
      (fun _ => P) P' := by
  have hY : AEMeasurable (X 0) P := (hident 0).aemeasurable_fst
  have hu : ‖sqrtVec p‖ = 1 := norm_sqrtVec hY hX0
  have h := (show TendstoInDistribution (fun n ω => pearsonResidual n p (cellCount X n ω)) atTop
      (fun z => (ℝ ∙ sqrtVec p)ᗮ.starProjection z) (fun _ => P) (stdGaussian _) from
    tendstoInDistribution_pearsonResidual hX0 hpos hindep hident).continuous_comp
    (g := fun v => ‖v‖ ^ 2) (by fun_prop)
  have hrank := finrank_orthogonal_sqrtVec hu
  have hlaw : HasLaw ((fun v : EuclideanSpace ℝ ι => ‖v‖ ^ 2) ∘
      fun z => (ℝ ∙ sqrtVec p)ᗮ.starProjection z)
      (chiSquareMeasure (Fintype.card ι - 1)) (stdGaussian (EuclideanSpace ℝ ι)) :=
    ⟨by fun_prop, by
      rw [← hrank]
      exact stdGaussian_map_norm_sq_starProjection _ (by omega)⟩
  refine tendstoInDistribution_of_hasLaw ?_ hlaw hZ
  convert h using 2 with n
  ext ω
  exact (norm_sq_pearsonResidual (fun i => (hpos i).le) n _).symm

end Probability

/-! ### Fitted cell probabilities -/

section Fitted

/-- For nested subspaces `V ≤ K`, removing the `V`-component of the `K`-projection is the
projection onto `Vᗮ ⊓ K`. -/
private theorem starProjection_sub_starProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {V K : Submodule ℝ E} (h : V ≤ K) (z : E) :
    K.starProjection z - V.starProjection (K.starProjection z) = (Vᗮ ⊓ K).starProjection z := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨V.sub_starProjection_mem_orthogonal _,
      K.sub_mem (K.starProjection_apply_mem z) (h (V.starProjection_apply_mem _))⟩
  · intro w hw
    have hz : z - (K.starProjection z - V.starProjection (K.starProjection z)) =
        (z - K.starProjection z) + V.starProjection (K.starProjection z) := by abel
    rw [hz, inner_add_left,
      Submodule.inner_left_of_mem_orthogonal hw.2 (K.sub_starProjection_mem_orthogonal z),
      Submodule.inner_right_of_mem_orthogonal (V.starProjection_apply_mem _) hw.1, add_zero]

/-- The coordinatewise weighting `q ↦ (qᵢ / √pᵢ)ᵢ` as a continuous linear map into
`EuclideanSpace ℝ ι`. -/
private noncomputable def weight (p : ι → ℝ) : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (√(p i))⁻¹ • ContinuousLinearMap.proj i)

omit [Fintype ι] in
private theorem weight_apply (p q : ι → ℝ) (i : ι) : weight p q i = q i / √(p i) := by
  simp [weight, div_eq_inv_mul]

/-- The tangent space of a model of probability vectors is orthogonal to `√p` after weighting:
differentiating `∑ᵢ pᵢ(θ) = 1` (near `θ₀`) gives `∑ᵢ (D a)ᵢ = 0`. -/
private theorem range_le_orthogonal_sqrtVec {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {pθ : F → ι → ℝ} {θ₀ : F} (hpos : ∀ i, 0 < pθ θ₀ i)
    (hsum : ∀ᶠ θ in nhds θ₀, ∑ i, pθ θ i = 1) {D : F →L[ℝ] (ι → ℝ)} (hD : HasFDerivAt pθ D θ₀)
    {J : F →L[ℝ] EuclideanSpace ℝ ι} (hJ : ∀ a i, J a i = D a i / √(pθ θ₀ i)) :
    LinearMap.range J.toLinearMap ≤ (ℝ ∙ sqrtVec (pθ θ₀))ᗮ := by
  rintro _ ⟨a, rfl⟩
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sqrtVec]
  set S : (ι → ℝ) →L[ℝ] ℝ := ∑ i, ContinuousLinearMap.proj i
  have hS : HasFDerivAt (fun θ => ∑ i, pθ θ i) (S.comp D) θ₀ := by
    convert S.hasFDerivAt.comp θ₀ hD using 1
    ext θ
    simp [S]
  have h0 : S.comp D = 0 :=
    hS.unique ((hasFDerivAt_const (1 : ℝ) θ₀).congr_of_eventuallyEq hsum)
  have hDa : ∑ i, D a i = 0 := by simpa [S] using congrArg (fun T => T a) h0
  rw [← hDa]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.coe_coe, hJ, mul_div_cancel₀ _ (Real.sqrt_pos.2 (hpos i)).ne']

/-- The fitted Pearson residual factors as a ratio of square roots times a linearized
residual. -/
private theorem fitted_residual_eq (n : ℕ) {N p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    √p / √q * (√n * ((√n)⁻¹ * ((N - n * p) / √(n * p)) - (q / √p - p / √p))) =
      (N - n * q) / √(n * q) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases hq.eq_or_lt with rfl | hq
  · simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [Real.sqrt_mul hn'.le, Real.sqrt_mul hn'.le]
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have hsp : 0 < √p := Real.sqrt_pos.2 hp
  have hsq : 0 < √q := Real.sqrt_pos.2 hq
  have hn2 : (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt hn'.le).symm
  have hp2 : p = √p ^ 2 := (Real.sq_sqrt hp.le).symm
  have hq2 : q = √q ^ 2 := (Real.sq_sqrt hq.le).symm
  generalize √(n : ℝ) = a at hsn hn2 ⊢
  generalize √p = b at hsp hp2 ⊢
  generalize √q = c at hsq hq2 ⊢
  rw [hn2, hp2, hq2]
  field_simp
  ring

/-- A deterministic sequence converging to `c` converges to `c` in probability. -/
private theorem tendstoInMeasure_const_seq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {E : Type*} [SeminormedAddCommGroup E] {a : ℕ → E}
    {c : E} (ha : Tendsto a atTop (nhds c)) :
    TendstoInMeasure P (fun n (_ : Ω) => a n) atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.1 ha).eventually (gt_mem_nhds hε)]
    with n hn
  simp [hn.not_ge]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

/-- **Pearson's chi-square theorem with estimated parameters** (fixed cells, `k - 1 - s`
degrees of freedom). Let the cell probabilities follow a model `θ ↦ pθ θ` on a
finite-dimensional parameter space `F` (`pθ θ i ≥ 0` for every `θ`, `∑ᵢ pθ θ i = 1` for `θ`
near `θ₀`), with
true parameter `θ₀`, all `pθ θ₀ i > 0`, and Fréchet derivative `D` at `θ₀`. Write
`J a = ((D a)ᵢ / √(pθ θ₀ i))ᵢ` for the weighted Jacobian and `V = range J` for the weighted
tangent space.

The estimator hypothesis is the **efficient grouped-count estimator** condition: for some
continuous linear `L` with `J ∘ L` the orthogonal projection onto `V` (that is,
`L = (JᵀJ)⁻¹ Jᵀ` when `J` is injective),
`√n (θ̂ n - θ₀) = L (Pearson residuals at θ₀) + o_P(1)`. This is the asymptotic linear
expansion of the grouped-data maximum-likelihood and minimum chi-square estimators
(Cramér 1946, §30.3; Birch 1964); it is assumed here, not proved, and it is exactly what makes
the limit chi-square: other estimators (e.g. the ungrouped MLE) give a different limit in
general (Chernoff–Lehmann 1954).

Under these hypotheses Pearson's statistic with the fitted probabilities
`∑ᵢ (Nᵢ - n pᵢ(θ̂))² / (n pᵢ(θ̂))` converges in distribution to `χ²_{k - 1 - dim V}`. The proof
applies the delta method to `(r, θ) ↦ r - (w(pθ θ) - w(pθ θ₀))` jointly in the Pearson residuals
and `θ̂`, giving the limit `P_K Z - P_V (P_K Z) = P_{Vᗮ ⊓ K} Z` (the tangent space lies in
`K = (√p)ᗮ` because `∑ᵢ pθ θ i = 1`), and Cochran's theorem on the subspace `Vᗮ ⊓ K` of
dimension `k - 1 - dim V`. Fitted cells with `pᵢ(θ̂) = 0` contribute `0`; the event has
probability tending to `0`.

The nonnegativity hypothesis `hnn` is global although only `θ` near `θ₀` matter: since
`θ̂ n → θ₀` in probability, it could be localized to a neighbourhood of `θ₀` by comparing the
statistics on events of probability tending to `1`. That localization is not done here (a
follow-up); models that leave the simplex away from `θ₀`, such as Hardy–Weinberg proportions
`(θ², 2θ(1 - θ), (1 - θ)²)` on all of `ℝ`, must for now be reparametrized or clamped. -/
theorem tendstoInDistribution_pearsonStatistic_fitted [DecidableEq ι] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] {X : ℕ → Ω → ι} {pθ : F → ι → ℝ} {θ₀ : F}
    (hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = pθ θ₀ i) (hpos : ∀ i, 0 < pθ θ₀ i)
    (hindep : iIndepFun X P) (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hnn : ∀ θ i, 0 ≤ pθ θ i) (hsum : ∀ᶠ θ in nhds θ₀, ∑ i, pθ θ i = 1) (hmeas : Measurable pθ)
    {D : F →L[ℝ] (ι → ℝ)} (hD : HasFDerivAt pθ D θ₀)
    {J : F →L[ℝ] EuclideanSpace ℝ ι} (hJ : ∀ a i, J a i = D a i / √(pθ θ₀ i))
    {L : EuclideanSpace ℝ ι →L[ℝ] F}
    (hJL : ∀ v, J (L v) = (LinearMap.range J.toLinearMap).starProjection v)
    {θhat : ℕ → Ω → F} (hθm : ∀ n, AEMeasurable (θhat n) P)
    (hθ : TendstoInMeasure P (fun (n : ℕ) ω => √n • (θhat n ω - θ₀) -
      L (pearsonResidual n (pθ θ₀) (cellCount X n ω))) atTop 0)
    (hdf : finrank ℝ (LinearMap.range J.toLinearMap) + 1 < Fintype.card ι)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z (chiSquareMeasure
      (Fintype.card ι - 1 - finrank ℝ (LinearMap.range J.toLinearMap))) P') :
    TendstoInDistribution (fun n ω => pearsonStatistic n (pθ (θhat n ω)) (cellCount X n ω))
      atTop Z (fun _ => P) P' := by
  set p := pθ θ₀ with hp_def
  set K : Submodule ℝ (EuclideanSpace ℝ ι) := (ℝ ∙ sqrtVec p)ᗮ with hK
  set V : Submodule ℝ (EuclideanSpace ℝ ι) := LinearMap.range J.toLinearMap with hV
  set R : ℕ → Ω → EuclideanSpace ℝ ι := fun n ω => pearsonResidual n p (cellCount X n ω)
    with hR_def
  have hY : AEMeasurable (X 0) P := (hident 0).aemeasurable_fst
  have hu : ‖sqrtVec p‖ = 1 := norm_sqrtVec hY hX0
  have hVK : V ≤ K := range_le_orthogonal_sqrtVec hpos hsum hD hJ
  have hR : TendstoInDistribution R atTop (fun z => K.starProjection z) (fun _ => P)
      (stdGaussian _) :=
    tendstoInDistribution_pearsonResidual hX0 hpos hindep hident
  have hRm : ∀ n, AEMeasurable (R n) P := hR.forall_aemeasurable
  have hsqrt : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  -- Step 1: the joint limit of `(R n, √n (θ̂ n - θ₀))`.
  set S : ℕ → Ω → F := fun n ω => √n • (θhat n ω - θ₀) with hS_def
  have hSm : ∀ n, AEMeasurable (S n) P := fun n => ((hθm n).sub_const θ₀).const_smul _
  have hRL : TendstoInDistribution (fun n ω => (R n ω, L (R n ω))) atTop
      (fun z => (K.starProjection z, L (K.starProjection z))) (fun _ => P) (stdGaussian _) :=
    hR.continuous_comp (g := fun v => (v, L v)) (by fun_prop)
  have hT : TendstoInDistribution (fun n ω => (R n ω, S n ω)) atTop
      (fun z => (K.starProjection z, L (K.starProjection z))) (fun _ => P)
      (stdGaussian _) := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hRL ?_
      fun n => (hRm n).prodMk (hSm n)
    have hθ' : TendstoInMeasure P (fun n ω => S n ω - L (R n ω)) atTop (fun _ => (0 : F)) := hθ
    have h := hθ'.comp_const_of_continuousAt
      (f := fun x : F => ((0 : EuclideanSpace ℝ ι), x)) (by fun_prop)
    refine h.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => rfl)
    simp
  -- Step 2: the delta method for `G (r, θ) = r - (w(p(θ)) - w(p(θ₀)))` at `(0, θ₀)`.
  set W := weight p with hW_def
  set G : EuclideanSpace ℝ ι × F → EuclideanSpace ℝ ι :=
    fun x => x.1 - (W (pθ x.2) - W (pθ θ₀)) with hG_def
  set DG : EuclideanSpace ℝ ι × F →L[ℝ] EuclideanSpace ℝ ι :=
    ContinuousLinearMap.fst ℝ _ F - J.comp (ContinuousLinearMap.snd ℝ _ F) with hDG_def
  have hG : HasFDerivAt G DG ((0 : EuclideanSpace ℝ ι), θ₀) := by
    have hWD : W.comp D = J := by
      ext a i
      simp [W, weight_apply, hJ, p]
    have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ ι × F => W (pθ x.2))
        (J.comp (ContinuousLinearMap.snd ℝ _ F)) ((0 : EuclideanSpace ℝ ι), θ₀) := by
      have hs : HasFDerivAt (Prod.snd : EuclideanSpace ℝ ι × F → F)
          (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ ι) F) ((0 : EuclideanSpace ℝ ι), θ₀) :=
        hasFDerivAt_snd
      rw [← hWD]
      exact (W.hasFDerivAt.comp θ₀ hD).comp _ hs
    exact hasFDerivAt_fst.sub (h1.sub_const _)
  set Xn : ℕ → Ω → EuclideanSpace ℝ ι × F := fun n ω => ((√n)⁻¹ • R n ω, θhat n ω)
    with hXn_def
  have hXZ : TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • (Xn n ω - ((0 : EuclideanSpace ℝ ι), θ₀))) atTop
      (fun z => (K.starProjection z, L (K.starProjection z))) (fun _ => P)
      (stdGaussian _) := by
    refine hT.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun _ => rfl)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine Prod.ext ?_ ?_
      · ext i
        simp [R, pearsonResidual, cellCount]
      · simp [S]
    · have hs : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
      refine Prod.ext ?_ ?_
      · simp [Xn, smul_smul, mul_inv_cancel₀ hs]
      · simp [Xn, S]
  have hB := TendstoInDistribution.delta_method (X := Xn)
    (θ := ((0 : EuclideanSpace ℝ ι), θ₀)) (r := fun n : ℕ => √(n : ℝ)) (g := G) (L := DG)
    hXZ hsqrt hG (fun n => ((hRm n).const_smul (√(n : ℝ))⁻¹).prodMk (hθm n)) (fun n => by
      have h1 : AEMeasurable (fun ω => W (pθ (θhat n ω))) P :=
        (W.continuous.measurable.comp hmeas).comp_aemeasurable (hθm n)
      exact ((hRm n).const_smul (√(n : ℝ))⁻¹).sub (h1.sub_const (W (pθ θ₀))))
  -- Step 3: consistency `θ̂ n → θ₀` in probability.
  have hScl : TendstoInDistribution S atTop (fun z => L (K.starProjection z)) (fun _ => P)
      (stdGaussian _) :=
    hT.continuous_comp (g := Prod.snd) continuous_snd
  have hinv : TendstoInMeasure P (fun (n : ℕ) (_ : Ω) => (√(n : ℝ))⁻¹) atTop (fun _ => 0) :=
    tendstoInMeasure_const_seq (tendsto_inv_atTop_zero.comp hsqrt)
  have h1 : TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • S n ω) atTop
      (fun _ => (0 : F))
      (fun _ => P) (stdGaussian (EuclideanSpace ℝ ι)) :=
    (hScl.smul_of_tendstoInMeasure_const hinv fun _ => aemeasurable_const).congr
      (fun _ => ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => zero_smul ℝ _)
  have hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀) := by
    have h := (tendstoInMeasure_of_tendstoInDistribution_const h1).congr'
      (f' := fun n ω => θhat n ω - θ₀) ?_ EventuallyEq.rfl
    · rw [tendstoInMeasure_iff_norm] at h ⊢
      simpa using h
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hs : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
      exact ae_of_all _ fun ω => by simp [S, smul_smul, inv_mul_cancel₀ hs]
  -- Step 4: the ratios `√pᵢ / √p̂ᵢ` tend to `1` in probability.
  set Φ : (ι → ℝ) → (ι → ℝ) := fun q i => √(p i) / √(q i) with hΦ_def
  have hΦc : ContinuousAt (fun θ => Φ (pθ θ)) θ₀ := by
    refine ContinuousAt.comp (f := pθ) (g := Φ) ?_ hD.continuousAt
    refine continuousAt_pi.2 fun i => ?_
    exact continuousAt_const.div
      ((Real.continuous_sqrt.comp (continuous_apply i)).continuousAt)
      (Real.sqrt_pos.2 (hpos i)).ne'
  have hf : TendstoInMeasure P (fun n ω => Φ (pθ (θhat n ω))) atTop (fun _ => 1) := by
    have h := hcons.comp_const_of_continuousAt hΦc
    have h1 : Φ (pθ θ₀) = 1 := by
      ext i
      simp [Φ, p, div_self (Real.sqrt_pos.2 (hpos i)).ne']
    rwa [h1] at h
  have hΦm : Measurable Φ := by
    refine measurable_pi_iff.2 fun i => ?_
    exact measurable_const.div (Real.continuous_sqrt.measurable.comp (measurable_pi_apply i))
  have hfm : ∀ n, AEMeasurable (fun ω => Φ (pθ (θhat n ω))) P :=
    fun n => (hΦm.comp hmeas).comp_aemeasurable (hθm n)
  -- Step 5: Slutsky.
  set g : EuclideanSpace ℝ ι × (ι → ℝ) → ℝ :=
    fun x => ‖(WithLp.toLp 2 fun i => x.2 i * x.1 i : EuclideanSpace ℝ ι)‖ ^ 2 with hg_def
  have hgc : Continuous g := by
    have : Continuous fun x : EuclideanSpace ℝ ι × (ι → ℝ) =>
        (WithLp.toLp 2 fun i => x.2 i * x.1 i : EuclideanSpace ℝ ι) := by
      fun_prop
    exact (continuous_norm.comp this).pow 2
  have hfin := hB.continuous_comp_prodMk_of_tendstoInMeasure_const hgc hf hfm
  -- Step 6: the limit law, by Cochran's theorem on `Vᗮ ⊓ K`.
  have hrank : finrank ℝ (Vᗮ ⊓ K : Submodule ℝ _) = Fintype.card ι - 1 - finrank ℝ V := by
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal hVK
    have h2 : finrank ℝ K = Fintype.card ι - 1 := finrank_orthogonal_sqrtVec hu
    omega
  have hlaw : HasLaw (fun z => g (DG (K.starProjection z, L (K.starProjection z)), 1))
      (chiSquareMeasure (Fintype.card ι - 1 - finrank ℝ V))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    refine ⟨hfin.aemeasurable_limit, ?_⟩
    have hfun : (fun z => g (DG (K.starProjection z, L (K.starProjection z)), 1)) =
        fun z => ‖(Vᗮ ⊓ K).starProjection z‖ ^ 2 := by
      ext z
      simp only [g, DG, FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', Pi.one_apply, one_mul,
        WithLp.toLp_ofLp]
      rw [hJL, starProjection_sub_starProjection hVK]
    rw [hfun, ← hrank]
    exact stdGaussian_map_norm_sq_starProjection _ (by omega)
  -- Step 7: the Slutsky sequence is the fitted Pearson statistic.
  refine tendstoInDistribution_of_hasLaw (hfin.congr (fun n => ae_of_all _ fun ω => ?_)
    (ae_of_all _ fun _ => rfl)) hlaw hZ
  change _ = pearsonStatistic n (pθ (θhat n ω)) (cellCount X n ω)
  rw [← norm_sq_pearsonResidual (hnn _) n]
  simp only [g]
  congr 2
  ext i
  simp only [G, Xn, R, Φ, pearsonResidual, PiLp.smul_apply, PiLp.sub_apply, weight_apply, W,
    sub_self, sub_zero, smul_eq_mul, PiLp.toLp_apply]
  exact fitted_residual_eq n (hpos i) (hnn _ i)

/-- **Pearson's chi-square theorem with `s` estimated parameters**: the form of
`tendstoInDistribution_pearsonStatistic_fitted` for an injective weighted Jacobian `J` (an
identifiable model with full-rank derivative at `θ₀`), where `dim V = s = dim F` and the limit
is `χ²_{k - 1 - s}`. -/
theorem tendstoInDistribution_pearsonStatistic_fitted_of_injective [DecidableEq ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] {X : ℕ → Ω → ι} {pθ : F → ι → ℝ} {θ₀ : F}
    (hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = pθ θ₀ i) (hpos : ∀ i, 0 < pθ θ₀ i)
    (hindep : iIndepFun X P) (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hnn : ∀ θ i, 0 ≤ pθ θ i) (hsum : ∀ᶠ θ in nhds θ₀, ∑ i, pθ θ i = 1) (hmeas : Measurable pθ)
    {D : F →L[ℝ] (ι → ℝ)} (hD : HasFDerivAt pθ D θ₀)
    {J : F →L[ℝ] EuclideanSpace ℝ ι} (hJ : ∀ a i, J a i = D a i / √(pθ θ₀ i))
    (hinj : Function.Injective J) {L : EuclideanSpace ℝ ι →L[ℝ] F}
    (hJL : ∀ v, J (L v) = (LinearMap.range J.toLinearMap).starProjection v)
    {θhat : ℕ → Ω → F} (hθm : ∀ n, AEMeasurable (θhat n) P)
    (hθ : TendstoInMeasure P (fun (n : ℕ) ω => √n • (θhat n ω - θ₀) -
      L (pearsonResidual n (pθ θ₀) (cellCount X n ω))) atTop 0)
    (hdf : finrank ℝ F + 1 < Fintype.card ι)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure (Fintype.card ι - 1 - finrank ℝ F)) P') :
    TendstoInDistribution (fun n ω => pearsonStatistic n (pθ (θhat n ω)) (cellCount X n ω))
      atTop Z (fun _ => P) P' := by
  have hr : finrank ℝ (LinearMap.range J.toLinearMap) = finrank ℝ F :=
    LinearMap.finrank_range_of_inj hinj
  exact tendstoInDistribution_pearsonStatistic_fitted hX0 hpos hindep hident hnn hsum hmeas hD
    hJ hJL hθm hθ (by rwa [hr]) (by rwa [hr])

end Fitted

end ProbabilityTheory
