/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.PoissonRandomField
public import MathlibExt.Probability.Distributions.GammaMoments
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The distribution of fitness effects and its Poisson-random-field likelihood

In the Poisson random field (Sawyer and Hartl 1992; `prfDensity`, `expectedSFS`) every new
mutation carries the same scaled selection coefficient `σ = 2Ns` (time in units of `2N`
generations, `θ = 4Nu`). A *distribution of fitness effects* (DFE) lets `σ` vary from site to
site: each new mutation draws its own `σ` from a probability law `μ` on `ℝ`, independently of
everything else. Boyko et al. (2008) model the DFE of deleterious nonsynonymous mutations by a
gamma law on the scaled strength `γ = 2N|s|` (heterozygote disadvantage `s`, homozygote `2s`,
which is genic selection with `σ = -γ` in the convention used here) and fit it by extending the
Poisson-random-field maximum-likelihood method of Williamson et al. (2005), in which each entry
of the site-frequency spectrum is a Poisson count.

## Main results

* `dfeSFS μ θ n i = ∫ E ξ_i(σ) dμ(σ)` is the expected unfolded spectrum under the DFE `μ`, and
  `dfeDensity μ θ x = ∫ φ_σ(x) dμ(σ)` the DFE-averaged frequency density.
* `dfeSFS_eq_integral_dfeDensity` (**mixture identity**): for a finite measure `μ` and
  `1 ≤ i < n`, averaging the spectra equals sampling from the averaged density,
  `∫ E ξ_i(σ) dμ(σ) = ∫₀¹ C(n, i) x ^ i (1 - x) ^ (n - i) (∫ φ_σ(x) dμ(σ)) dx`.
  The interchange rests on `abs_expectedSFS_le`, a bound uniform in `σ`, which in turn uses
  the bounds `kimuraFixation_nonneg` and `kimuraFixation_le_one` of the Wright–Fisher
  diffusion file.
* `dfeSFS_dirac`, `dfeSFS_add_measure`, `dfeSFS_smul_measure`: a point-mass DFE recovers the
  single-`σ` spectrum, and the spectrum is additive and homogeneous in the DFE, so mixtures of
  DFEs (for example a neutral point mass plus a gamma law) give mixtures of spectra.
* `gammaDFE a r`: the law of `σ = -T` with `T ~ Gamma(a, r)` (shape `a`, rate `r`, scale
  `1 / r`), so every mutation is deleterious or neutral (`gammaDFE_Ioi_zero`). Its mean is
  `-a / r` (`integral_id_gammaDFE`), its variance `a / r ^ 2` (`variance_id_gammaDFE`), and
  `gammaDFE_map_const_mul` converts a gamma DFE of `s` into one of `σ = 2Ns`.
* `gammaDFE_real_Iio`: the fraction of new mutations with `σ < -c` (`c ≥ 0`) is the gamma tail
  `Γ(a, r c) / Γ(a)`; `gammaDFE_real_Ico` gives the fraction in a band of strengths. Boyko et
  al. report such fractions for the bins `|s| < 10⁻⁴`, `10⁻⁴ < |s| < 10⁻²`, `|s| > 10⁻²`; by
  `gammaDFE_map_const_mul` the law of `s = σ / (2N)` is the gamma DFE with rate `2N r`.
* `poissonLogLik`: with independent Poisson counts `k_i` of mean `E_i` per frequency class (the
  Poisson-random-field sampling model), `log_pi_poissonMeasure_real_singleton` shows that the
  log-likelihood of the counts is `∑ (k_i log E_i - E_i - log k_i!)`.
* `hasFDerivAt_poissonLogLik`, `score_eq_zero_of_isMaxOn`: when the means depend
  differentiably on a parameter `ψ` (DFE and demographic parameters), a maximizer in the
  interior of the parameter set solves the score equations
  `∑ (k_i / E_i(ψ) - 1) · DE_i(ψ) = 0`. Consistency of the estimator is not covered.
* `poissonLogLik_le_profile`: the mutation-rate parameter enters linearly, `E_i = θ f_i`, and
  for fixed `f` the likelihood is maximized at `θ̂ = ∑ k_i / ∑ f_i`.

## References

* S. A. Sawyer and D. L. Hartl, *Population genetics of polymorphism and divergence*,
  Genetics 132 (1992) 1161–1176.
* A. R. Boyko et al., *Assessing the evolutionary impact of amino acid mutations in the human
  genome*, PLoS Genet. 4 (2008) e1000083.
* S. H. Williamson et al., *Simultaneous inference of selection and population growth from
  patterns of variation in the human genome*, Proc. Natl. Acad. Sci. USA 102 (2005)
  7882–7887.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter
open MathlibExt.Biology.PopulationGenetics.Diffusion
open scoped Topology NNReal ENNReal

namespace MathlibExt.Biology.PopulationGenetics.DistributionOfFitnessEffects

/-! ### A bound on the expected spectrum -/

private theorem sampling_bound (θ σ : ℝ) {n i : ℕ} (hi : 0 < i) (hin : i < n)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖(n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i) * prfDensity θ σ x‖ ≤
      |θ| * n.choose i := by
  have hc : 0 ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
  have hbound : 0 ≤ |θ| * (n.choose i : ℝ) := mul_nonneg (abs_nonneg _) hc
  by_cases hx0 : x = 0
  · simp [hx0, prfDensity, hbound]
  by_cases hx1 : x = 1
  · simp [hx1, prfDensity, hbound]
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
  have hsub : 0 < 1 - x := sub_pos.mpr hxlt
  have hpowi : x ^ i = x ^ (i - 1) * x := by
    rw [← pow_succ]; congr 1; omega
  have hpown : (1 - x) ^ (n - i) = (1 - x) ^ (n - i - 1) * (1 - x) := by
    rw [← pow_succ]; congr 1; omega
  have heq : (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i) * prfDensity θ σ x =
      (n.choose i : ℝ) * θ * x ^ (i - 1) * (1 - x) ^ (n - i - 1) *
        kimuraFixation σ (1 - x) := by
    rw [prfDensity, hpowi, hpown]
    field_simp
  have hk0 := kimuraFixation_nonneg σ (le_of_lt hsub)
  have hk1 := kimuraFixation_le_one σ (show 1 - x ≤ 1 by linarith)
  rw [heq, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hc, abs_of_nonneg (pow_nonneg hx.1 _),
    abs_of_nonneg (pow_nonneg (le_of_lt hsub) _), abs_of_nonneg hk0]
  calc
    (n.choose i : ℝ) * |θ| * x ^ (i - 1) * (1 - x) ^ (n - i - 1) *
        kimuraFixation σ (1 - x) ≤ (n.choose i : ℝ) * |θ| * 1 * 1 * 1 := by
      gcongr
      · exact pow_le_one₀ hx.1 hx.2
      · exact pow_le_one₀ (le_of_lt hsub) (by linarith)
    _ = |θ| * n.choose i := by ring

/-- The expected number of sites with `i` derived copies in a sample of `n`, `1 ≤ i < n`, is
bounded uniformly in the selection coefficient: `|E ξ_i(σ)| ≤ |θ| C(n, i)`. -/
theorem abs_expectedSFS_le (θ σ : ℝ) {n i : ℕ} (hi : 0 < i) (hin : i < n) :
    |expectedSFS θ σ n i| ≤ |θ| * n.choose i := by
  simpa [expectedSFS, Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := 1) (C := |θ| * (n.choose i : ℝ))
      (fun x hx => sampling_bound θ σ hi hin
        (Ioc_subset_Icc_self (by simpa using hx)))

/-! ### Spectra under a distribution of fitness effects -/

/-- The expected unfolded site-frequency spectrum under the distribution of fitness effects
`μ` (a law on the scaled selection coefficient `σ = 2Ns`): `∫ E ξ_i(σ) dμ(σ)`, where each new
mutation draws its own `σ` from `μ`. -/
noncomputable def dfeSFS (μ : Measure ℝ) (θ : ℝ) (n i : ℕ) : ℝ :=
  ∫ σ, expectedSFS θ σ n i ∂μ

/-- The Poisson-random-field frequency density averaged over the distribution of fitness
effects `μ`: `∫ φ_σ(x) dμ(σ)`. -/
noncomputable def dfeDensity (μ : Measure ℝ) (θ x : ℝ) : ℝ :=
  ∫ σ, prfDensity θ σ x ∂μ

private theorem sampling_measurable (θ : ℝ) (n i : ℕ) :
    Measurable (fun p : ℝ × ℝ =>
      (n.choose i : ℝ) * p.2 ^ i * (1 - p.2) ^ (n - i) * prfDensity θ p.1 p.2) := by
  have hk : Measurable (fun p : ℝ × ℝ => kimuraFixation p.1 (1 - p.2)) := by
    unfold kimuraFixation
    apply Measurable.ite
    · exact measurable_fst (measurableSet_singleton (0 : ℝ))
    · fun_prop
    · fun_prop
  unfold prfDensity
  fun_prop

private theorem sampling_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (θ : ℝ)
    {n i : ℕ} (hi : 0 < i) (hin : i < n) :
    Integrable (fun p : ℝ × ℝ =>
      (n.choose i : ℝ) * p.2 ^ i * (1 - p.2) ^ (n - i) * prfDensity θ p.1 p.2)
      (μ.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  apply Integrable.of_bound (sampling_measurable θ n i).aestronglyMeasurable
    (|θ| * (n.choose i : ℝ))
  have hx : ∀ᵐ p : ℝ × ℝ ∂μ.prod (volume.restrict (Ioc (0 : ℝ) 1)),
      p.2 ∈ Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioc)).mpr
    exact Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hx] with p hp
  exact sampling_bound θ p.1 hi hin (Ioc_subset_Icc_self hp)

/-- For `1 ≤ i < n`, the expected spectrum `E ξ_i(σ)` is integrable in `σ` against every
finite measure. -/
theorem integrable_expectedSFS (μ : Measure ℝ) [IsFiniteMeasure μ] (θ : ℝ) {n i : ℕ}
    (hi : 0 < i) (hin : i < n) : Integrable (fun σ => expectedSFS θ σ n i) μ := by
  have hm : StronglyMeasurable (fun σ => expectedSFS θ σ n i) := by
    unfold expectedSFS
    simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact (sampling_measurable θ n i).stronglyMeasurable.integral_prod_right'
  apply Integrable.of_bound hm.aestronglyMeasurable (|θ| * (n.choose i : ℝ))
  exact Eventually.of_forall (fun σ => by
    simpa only [Real.norm_eq_abs] using abs_expectedSFS_le θ σ hi hin)

/-- **Mixture identity.** For a finite measure `μ` of selection coefficients and a segregating
class `1 ≤ i < n`, the DFE-averaged spectrum is the binomial sampling integral of the
DFE-averaged frequency density:
`∫ E ξ_i(σ) dμ(σ) = ∫₀¹ C(n, i) x ^ i (1 - x) ^ (n - i) (∫ φ_σ(x) dμ(σ)) dx`. -/
theorem dfeSFS_eq_integral_dfeDensity (μ : Measure ℝ) [IsFiniteMeasure μ] (θ : ℝ) {n i : ℕ}
    (hi : 0 < i) (hin : i < n) :
    dfeSFS μ θ n i =
      ∫ x in (0 : ℝ)..1, (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i) * dfeDensity μ θ x := by
  unfold dfeSFS expectedSFS dfeDensity
  simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [integral_integral_swap (sampling_integrable μ θ hi hin)]
  congr 1 with x
  exact integral_const_mul ((n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i))
    (fun σ => prfDensity θ σ x)

/-- A DFE concentrated on one selection coefficient gives the single-`σ` spectrum. -/
theorem dfeSFS_dirac (σ θ : ℝ) (n i : ℕ) :
    dfeSFS (Measure.dirac σ) θ n i = expectedSFS θ σ n i := by
  simp [dfeSFS, integral_dirac]

/-- The spectrum is additive in the (finite) DFE. -/
theorem dfeSFS_add_measure (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (θ : ℝ)
    {n i : ℕ} (hi : 0 < i) (hin : i < n) :
    dfeSFS (μ + ν) θ n i = dfeSFS μ θ n i + dfeSFS ν θ n i :=
  integral_add_measure (integrable_expectedSFS μ θ hi hin) (integrable_expectedSFS ν θ hi hin)

/-- The spectrum is homogeneous in the DFE. -/
theorem dfeSFS_smul_measure (c : ℝ≥0∞) (μ : Measure ℝ) (θ : ℝ) (n i : ℕ) :
    dfeSFS (c • μ) θ n i = c.toReal * dfeSFS μ θ n i := by
  simp [dfeSFS, integral_smul_measure, smul_eq_mul]

/-! ### The gamma DFE -/

/-- The gamma distribution of fitness effects (Boyko et al. 2008): the scaled selection
coefficient is `σ = -T` with `T ~ Gamma(a, r)`, shape `a > 0` and rate `r > 0` (scale `1 / r`),
so new mutations are deleterious with mean strength `a / r`. -/
noncomputable def gammaDFE (a r : ℝ) : Measure ℝ :=
  (gammaMeasure a r).map Neg.neg

/-- The gamma DFE is a probability law. -/
theorem isProbabilityMeasure_gammaDFE {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (gammaDFE a r) := by
  have := isProbabilityMeasure_gammaMeasure ha hr
  unfold gammaDFE
  infer_instance

/-- Under the gamma DFE no mutation is beneficial. -/
theorem gammaDFE_Ioi_zero (a r : ℝ) : gammaDFE a r (Ioi 0) = 0 := by
  have h : Neg.neg ⁻¹' Ioi (0 : ℝ) = Iio 0 := by ext; simp
  rw [gammaDFE, Measure.map_apply measurable_neg measurableSet_Ioi, h, gammaMeasure,
    withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

/-- The mean scaled selection coefficient under the gamma DFE is `-a / r`. -/
theorem integral_id_gammaDFE {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ σ, σ ∂gammaDFE a r = -(a / r) := by
  rw [gammaDFE, integral_map measurable_neg.aemeasurable (by fun_prop), integral_neg,
    integral_id_gammaMeasure ha hr]

/-- The variance of the scaled selection coefficient under the gamma DFE is `a / r ^ 2`. -/
theorem variance_id_gammaDFE {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    variance id (gammaDFE a r) = a / r ^ 2 := by
  rw [gammaDFE, variance_id_map measurable_neg.aemeasurable]
  change variance (-id) (gammaMeasure a r) = a / r ^ 2
  rw [variance_neg, variance_id_gammaMeasure ha hr]

/-- Rescaling a gamma DFE by `c > 0` (for example from `s` to `σ = 2Ns`, `c = 2N`) keeps the
shape and divides the rate by `c`. -/
theorem gammaDFE_map_const_mul {a r c : ℝ} (ha : 0 < a) (hr : 0 < r) (hc : 0 < c) :
    (gammaDFE a r).map (fun σ => c * σ) = gammaDFE a (r / c) := by
  rw [gammaDFE, gammaDFE, ← gammaMeasure_map_const_mul ha hr hc,
    Measure.map_map (measurable_const_mul c) measurable_neg,
    Measure.map_map measurable_neg (measurable_const_mul c)]
  congr 1
  funext t
  simp

/-- **Fraction of strongly deleterious mutations.** Under the gamma DFE the fraction of new
mutations with `σ < -c`, `c ≥ 0`, is the gamma tail `Γ(a, r c) / Γ(a)`. -/
theorem gammaDFE_real_Iio {a r c : ℝ} (ha : 0 < a) (hr : 0 < r) (hc : 0 ≤ c) :
    (gammaDFE a r).real (Iio (-c)) = upperIncompleteGamma a (r * c) / Gamma a := by
  have h : Neg.neg ⁻¹' Iio (-c) = Ioi c := by ext; simp
  rw [measureReal_def, gammaDFE, Measure.map_apply measurable_neg measurableSet_Iio, h,
    ← measureReal_def, gammaMeasure_real_Ioi ha hr hc]

/-- The fraction of new mutations whose strength `-σ` lies in `(c₁, c₂]`, `0 ≤ c₁ ≤ c₂`, is
`(Γ(a, r c₁) - Γ(a, r c₂)) / Γ(a)`. -/
theorem gammaDFE_real_Ico {a r c₁ c₂ : ℝ} (ha : 0 < a) (hr : 0 < r) (hc₁ : 0 ≤ c₁)
    (hc : c₁ ≤ c₂) :
    (gammaDFE a r).real (Ico (-c₂) (-c₁)) =
      (upperIncompleteGamma a (r * c₁) - upperIncompleteGamma a (r * c₂)) / Gamma a := by
  have := isProbabilityMeasure_gammaMeasure ha hr
  have h : Neg.neg ⁻¹' Ico (-c₂) (-c₁) = Ioc c₁ c₂ := by
    ext; simp [and_comm]
  rw [measureReal_def, gammaDFE, Measure.map_apply measurable_neg measurableSet_Ico, h,
    ← measureReal_def, ← Set.Ioi_sdiff_Ioi,
    measureReal_sdiff (Set.Ioi_subset_Ioi hc) measurableSet_Ioi,
    gammaMeasure_real_Ioi ha hr hc₁, gammaMeasure_real_Ioi ha hr (hc₁.trans hc), sub_div]

/-- The spectrum under the gamma DFE as an integral against the gamma law of the strength. -/
theorem dfeSFS_gammaDFE (a r θ : ℝ) (n i : ℕ) :
    dfeSFS (gammaDFE a r) θ n i = ∫ t, expectedSFS θ (-t) n i ∂gammaMeasure a r :=
  integral_map_equiv (MeasurableEquiv.neg ℝ) (fun σ => expectedSFS θ σ n i)

/-! ### The Poisson likelihood of the spectrum -/

section Likelihood

variable {ι : Type*} [Fintype ι]

/-- The Poisson log-likelihood `∑ (k_i log E_i - E_i - log k_i!)` of counts `k_i` with means
`E_i`. Meaningful for `E_i > 0`; at `E_i = 0` Lean's `log 0 = 0` gives a junk value. -/
noncomputable def poissonLogLik (E : ι → ℝ) (k : ι → ℕ) : ℝ :=
  ∑ i, ((k i : ℝ) * log (E i) - E i - log (Nat.factorial (k i)))

/-- The joint law of independent Poisson counts with means `E_i` gives the count vector `k`
the probability `∏ e^{-E_i} E_i ^ {k_i} / (k_i!)`. -/
theorem pi_poissonMeasure_real_singleton (E : ι → ℝ≥0) (k : ι → ℕ) :
    (Measure.pi fun i => poissonMeasure (E i)).real {k} =
      ∏ i, exp (-(E i : ℝ)) * (E i : ℝ) ^ k i / Nat.factorial (k i) := by
  classical
  rw [measureReal_def, ← Set.univ_pi_singleton k, Measure.pi_pi, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun i _ => poissonMeasure_real_singleton (E i) (k i)

/-- **The Poisson-random-field log-likelihood.** For independent Poisson counts with positive
means `E_i`, the log-probability of the observed counts `k` is `poissonLogLik E k`. -/
theorem log_pi_poissonMeasure_real_singleton (E : ι → ℝ≥0) (hE : ∀ i, 0 < E i) (k : ι → ℕ) :
    log ((Measure.pi fun i => poissonMeasure (E i)).real {k}) =
      poissonLogLik (fun i => (E i : ℝ)) k := by
  classical
  have hpos (i : ι) : 0 < (E i : ℝ) := hE i
  have hfac (i : ι) : 0 < (Nat.factorial (k i) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [pi_poissonMeasure_real_singleton, Real.log_prod]
  · unfold poissonLogLik
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.log_div (ne_of_gt (mul_pos (exp_pos _) (pow_pos (hpos i) _)))
        (ne_of_gt (hfac i)),
      Real.log_mul (ne_of_gt (exp_pos _)) (ne_of_gt (pow_pos (hpos i) _)),
      Real.log_exp, Real.log_pow]
    ring
  · intro i _
    exact ne_of_gt (div_pos (mul_pos (exp_pos _) (pow_pos (hpos i) _)) (hfac i))

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The derivative of the log-likelihood in the parameter `ψ`, when the means `E_i(ψ)` are
positive and differentiable at `ψ`: `∑ (k_i / E_i(ψ) - 1) · DE_i(ψ)`. -/
theorem hasFDerivAt_poissonLogLik {E : ι → V → ℝ} {ψ : V}
    (hE : ∀ i, DifferentiableAt ℝ (E i) ψ) (hpos : ∀ i, 0 < E i ψ) (k : ι → ℕ) :
    HasFDerivAt (fun φ => poissonLogLik (fun i => E i φ) k)
      (∑ i, ((k i : ℝ) / E i ψ - 1) • fderiv ℝ (E i) ψ) ψ := by
  classical
  unfold poissonLogLik
  have hterm (i : ι) :=
    ((((hE i).hasFDerivAt.log (ne_of_gt (hpos i))).const_mul (k i : ℝ)).sub
      (hE i).hasFDerivAt).sub_const (log (Nat.factorial (k i)))
  have hsum := HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv, sub_smul, smul_smul, one_smul]

/-- **Score equations.** If `ψ` maximizes the Poisson log-likelihood over a parameter set `S`
that is a neighborhood of `ψ`, and the means are positive and differentiable at `ψ`, then
`∑ (k_i / E_i(ψ) - 1) · DE_i(ψ) = 0`. -/
theorem score_eq_zero_of_isMaxOn {E : ι → V → ℝ} {ψ : V} {S : Set V} (k : ι → ℕ)
    (hS : S ∈ 𝓝 ψ) (hmax : IsMaxOn (fun φ => poissonLogLik (fun i => E i φ) k) S ψ)
    (hE : ∀ i, DifferentiableAt ℝ (E i) ψ) (hpos : ∀ i, 0 < E i ψ) :
    ∑ i, ((k i : ℝ) / E i ψ - 1) • fderiv ℝ (E i) ψ = 0 := by
  exact (hmax.isLocalMax hS).hasFDerivAt_eq_zero (hasFDerivAt_poissonLogLik hE hpos k)

/-- **Profile maximum in `θ`.** With means `E_i = θ f_i` linear in the mutation parameter,
positive `f_i` and at least one count, every `θ > 0` has likelihood at most that of
`θ̂ = ∑ k_i / ∑ f_i`. -/
theorem poissonLogLik_le_profile {f : ι → ℝ} (hf : ∀ i, 0 < f i) (k : ι → ℕ)
    (hk : 0 < ∑ i, k i) {θ : ℝ} (hθ : 0 < θ) :
    poissonLogLik (fun i => θ * f i) k ≤
      poissonLogLik (fun i => (∑ j, (k j : ℝ)) / (∑ j, f j) * f i) k := by
  classical
  let K : ℝ := ∑ i, (k i : ℝ)
  let F : ℝ := ∑ i, f i
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast hk
  obtain ⟨i, hi, _⟩ := Finset.sum_pos_iff.mp hk
  have hF : 0 < F := Finset.sum_pos (fun j _ => hf j) ⟨i, hi⟩
  have hhat : 0 < K / F := div_pos hK hF
  have hform (t : ℝ) (ht : 0 < t) :
      poissonLogLik (fun i => t * f i) k =
        K * log t - t * F +
          ∑ i, ((k i : ℝ) * log (f i) - log (Nat.factorial (k i))) := by
    unfold poissonLogLik
    simp_rw [Real.log_mul (ne_of_gt ht) (ne_of_gt (hf _))]
    calc
      ∑ i, ((k i : ℝ) * (log t + log (f i)) - t * f i -
          log (Nat.factorial (k i))) =
          ∑ i, (((k i : ℝ) * log t - t * f i) +
            ((k i : ℝ) * log (f i) - log (Nat.factorial (k i)))) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_mul, Finset.mul_sum]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hθ hhat)
  rw [Real.log_div (ne_of_gt hθ) (ne_of_gt hhat)] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog (le_of_lt hK)
  have hratio : K * (θ / (K / F) - 1) = θ * F - K := by
    field_simp
  rw [hratio] at hscaled
  change poissonLogLik (fun i => θ * f i) k ≤
    poissonLogLik (fun i => K / F * f i) k
  rw [hform θ hθ, hform (K / F) hhat, div_mul_cancel₀ K (ne_of_gt hF)]
  nlinarith

end Likelihood

end MathlibExt.Biology.PopulationGenetics.DistributionOfFitnessEffects
