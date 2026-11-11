/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import MathlibExt.Probability.Distributions.NegativeBinomial
public import MathlibExt.Probability.Statistics.GLM.NegativeBinomial

/-!
# Count-matrix observation model

The observation model behind count-based differential expression (RNA-seq, single-cell
pseudobulk). A count matrix has genes `G` as rows and samples `J` as columns; sample `j` is a
biological replicate of the condition `condition j : C` and has library size (size factor)
`sⱼ`. Gene `g` has normalized expression `q_{g,c}` in condition `c`, and its count in sample `j`
has mean

`μ_{g,j} = sⱼ · q_{g, condition j}`,

that is, log link with linear predictor `log q_{g,c}` and offset `log sⱼ`. Each gene follows a
selected count law (`CountLaw`): Poisson, or negative binomial with shape `θ` (dispersion
`α = 1 / θ`), with mean–variance law `V(μ) = μ + α μ²`.

No new distribution is defined. The Poisson law is Mathlib's `poissonMeasure`; the negative
binomial law is `negBinomialReal θ μ` from `MathlibExt.Probability.Distributions.NegativeBinomial`,
with its bridges to the success-probability form `negBinomialPMF` and to the Gamma–Poisson
mixture. The log-likelihood of one negative binomial gene is the regression log-likelihood
`nbLogLik` of `MathlibExt.Probability.Statistics.GLM.NegativeBinomial`.

## Main definitions

* `CountLaw`, `CountLaw.pmf`, `CountLaw.dispersion`, `CountLaw.varianceFn`: the selected law,
  its mass function at a given mean, its dispersion and its variance function;
  `CountLaw.ofDispersion`: the law with a given dispersion `α ≥ 0`.
* `CountModel`: laws, replicate-to-condition index, library sizes and rates;
  `CountModel.Valid`: its parameter domain, which allows a library size of `0`.
* `CountModel.mean`, `CountModel.countPMF`, `CountModel.likelihood`: entry means, entry laws, and
  the likelihood of a count matrix with entries independent (a product of entry masses; that
  it sums to `1` over all count matrices is not proved here, and no theorem relies on it).
* `CountModel.conditionDesign`: the replicate-to-condition design matrix.

## Main results

* `CountLaw.hasSum_pmf`, `CountLaw.hasSum_mul_pmf`, `CountLaw.variance_pmf`: normalization,
  mean `μ`, variance `μ + α μ²`.
* `CountLaw.pmf_poisson_eq_poissonMixtureReal`, `CountLaw.pmf_negBinomial_eq_poissonMixtureReal`,
  `CountLaw.pmf_negBinomial_eq_negBinomialPMF`: parametrization bridges.
* Zero counts: `CountLaw.pmf_mean_zero` (mean `0` is the point mass at `0`),
  `CountLaw.exp_neg_le_pmf_zero` (`P(0) ≥ e^{-μ}`), `CountLaw.pmf_zero_lt_one` and
  `CountLaw.pmf_pos` (for `μ > 0` every count, `0` included, has probability in `(0, 1)`).
* `CountModel.mean_eq_exp`: the log link with offset `log sⱼ`;
  `CountModel.mean_div_librarySize`: normalization by the library size;
  `CountModel.rate_eq_of_countPMF_eq`: **identifiability**, the count law of a sample with
  nonzero library size determines the rate of its condition.
* `CountModel.countPMF_eq_of_replicate`: replicates of a condition with equal library sizes have
  the same count law.
* Zero library size: `CountModel.countPMF_of_librarySize_eq_zero` (all counts are `0`),
  `CountModel.countPMF_eq_of_librarySize_eq_zero` (the sample carries no information on the
  parameters), `CountModel.likelihood_eq_zero` (a nonzero count there is impossible); with all
  library sizes positive every count matrix has positive likelihood (`CountModel.likelihood_pos`).
* `CountModel.sum_log_countPMF_eq_nbLogLik`: the log-likelihood of a negative binomial gene is
  `nbLogLik` with the condition design, offsets `log sⱼ` and coefficients `log q_{g,c}`, up to a
  rate-free constant.

Dispersion estimation, the likelihood-ratio and exact tests, and donor-level dependence between
cells are out of scope.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.GLM.CountData

open MeasureTheory Real Finset Matrix ProbabilityTheory
open MathlibExt.Probability.Statistics.GLM.NegativeBinomial
open scoped Nat NNReal

/-! ### The selected count law -/

/-- The count law of one gene: Poisson, or negative binomial with shape (size) `θ`, i.e.
dispersion `1 / θ`. -/
inductive CountLaw
  /-- The Poisson law: variance equal to the mean. -/
  | poisson
  /-- The negative binomial law `negBinomialReal θ` with shape `θ`: variance `μ + μ² / θ`. -/
  | negBinomial (θ : ℝ)

namespace CountLaw

/-- The parameter domain of a count law: always for Poisson, `θ > 0` for the negative
binomial. -/
def Valid : CountLaw → Prop
  | poisson => True
  | negBinomial θ => 0 < θ

/-- The mass function at mean `μ`: the Mathlib Poisson measure `Po(μ)` of `{k}` (with
`μ` truncated to `ℝ≥0`), or `negBinomialReal θ μ k`. Meaningful for `μ ≥ 0`. -/
noncomputable def pmf : CountLaw → ℝ → ℕ → ℝ
  | poisson, μ, k => (poissonMeasure μ.toNNReal).real {k}
  | negBinomial θ, μ, k => negBinomialReal θ μ k

/-- The dispersion `α` of the mean–variance law `V(μ) = μ + α μ²`: `0` for Poisson, `1 / θ`
for the negative binomial. -/
noncomputable def dispersion : CountLaw → ℝ
  | poisson => 0
  | negBinomial θ => θ⁻¹

/-- The variance function `V(μ) = μ + α μ²` of the law. -/
noncomputable def varianceFn (L : CountLaw) (μ : ℝ) : ℝ := μ + L.dispersion * μ ^ 2

/-- The law with dispersion `α`, as parametrized in count-data software: Poisson at `α = 0`,
otherwise negative binomial with shape `θ = 1 / α`. Meaningful for `α ≥ 0`. -/
noncomputable def ofDispersion (α : ℝ) : CountLaw :=
  open Classical in if α = 0 then poisson else negBinomial α⁻¹

/-- The Poisson mass function at mean `μ ≥ 0` is `e^{-μ} μᵏ / k!`. -/
theorem pmf_poisson {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    poisson.pmf μ k = exp (-μ) * μ ^ k / k ! := by
  simp [pmf, poissonMeasure_real_singleton, Real.coe_toNNReal _ hμ]

/-- The negative binomial mass function is `negBinomialReal θ μ`. -/
@[simp] theorem pmf_negBinomial (θ μ : ℝ) (k : ℕ) :
    (negBinomial θ).pmf μ k = negBinomialReal θ μ k := rfl

@[simp] theorem dispersion_poisson : poisson.dispersion = 0 := rfl

@[simp] theorem dispersion_negBinomial (θ : ℝ) : (negBinomial θ).dispersion = θ⁻¹ := rfl

/-- The Poisson law is the Poisson mixture over the point mass at its mean. -/
theorem pmf_poisson_eq_poissonMixtureReal {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    poisson.pmf μ k = poissonMixtureReal (Measure.dirac μ) k := by
  rw [pmf_poisson hμ, poissonMixtureReal_dirac]

/-- **Gamma–Poisson bridge.** For `θ > 0` and `μ > 0`, the negative binomial law is the
Poisson mixture over `Gamma(θ, θ / μ)`. -/
theorem pmf_negBinomial_eq_poissonMixtureReal {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 < μ) (k : ℕ) :
    (negBinomial θ).pmf μ k = poissonMixtureReal (gammaMeasure θ (θ / μ)) k :=
  (poissonMixtureReal_gammaMeasure_mean hθ hμ k).symm

/-- **Success-probability bridge.** For `θ > 0` and `μ ≥ 0`, the negative binomial law at mean
`μ` is `negBinomialPMF θ p` with `p = θ / (θ + μ)`. -/
theorem pmf_negBinomial_eq_negBinomialPMF {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 ≤ μ) (k : ℕ) :
    (negBinomial θ).pmf μ k = negBinomialPMF θ (θ / (θ + μ)) k :=
  negBinomialReal_eq_negBinomialPMF hθ hμ k

private lemma ae_dirac_nonneg {μ : ℝ} (hμ : 0 ≤ μ) : ∀ᵐ r ∂(Measure.dirac μ), 0 ≤ r := by
  rw [ae_dirac_eq]
  exact hμ

private lemma integrable_dirac_pow (μ : ℝ) (n : ℕ) :
    Integrable (fun r : ℝ => r ^ n) (Measure.dirac μ) :=
  integrable_dirac (by simp)

/-- The mass function is nonnegative on the parameter domain. -/
theorem pmf_nonneg {L : CountLaw} (hL : L.Valid) {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    0 ≤ L.pmf μ k := by
  cases L with
  | poisson => rw [pmf_poisson hμ]; positivity
  | negBinomial θ => exact negBinomialReal_nonneg hL hμ k

/-- **Normalization.** On the parameter domain the masses sum to one. -/
theorem hasSum_pmf {L : CountLaw} (hL : L.Valid) {μ : ℝ} (hμ : 0 ≤ μ) :
    HasSum (L.pmf μ) 1 := by
  cases L with
  | poisson =>
    rw [funext (pmf_poisson_eq_poissonMixtureReal hμ)]
    exact hasSum_poissonMixtureReal (ae_dirac_nonneg hμ)
  | negBinomial θ => exact hasSum_negBinomialReal hL hμ

/-- **Mean.** On the parameter domain the law has mean `μ`. -/
theorem hasSum_mul_pmf {L : CountLaw} (hL : L.Valid) {μ : ℝ} (hμ : 0 ≤ μ) :
    HasSum (fun k : ℕ => (k : ℝ) * L.pmf μ k) μ := by
  cases L with
  | poisson =>
    have h := hasSum_mul_poissonMixtureReal (ae_dirac_nonneg hμ)
      (integrable_dirac (f := id) (by simp))
    simpa [funext (pmf_poisson_eq_poissonMixtureReal hμ)] using h
  | negBinomial θ => exact hasSum_mul_negBinomialReal hL hμ

/-- **Second moment.** On the parameter domain `E N² = V(μ) + μ²`. -/
theorem hasSum_sq_pmf {L : CountLaw} (hL : L.Valid) {μ : ℝ} (hμ : 0 ≤ μ) :
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * L.pmf μ k) (L.varianceFn μ + μ ^ 2) := by
  cases L with
  | poisson =>
    have h := hasSum_sq_poissonMixtureReal (ae_dirac_nonneg hμ) (integrable_dirac_pow μ 2)
    simp only [integral_dirac] at h
    rw [funext (pmf_poisson_eq_poissonMixtureReal hμ)]
    convert h using 1
    simp [varianceFn]
    ring
  | negBinomial θ =>
    have h : (negBinomial θ).varianceFn μ + μ ^ 2 = μ + μ ^ 2 / θ + μ ^ 2 := by
      change μ + θ⁻¹ * μ ^ 2 + μ ^ 2 = _
      ring
    rw [h]
    exact hasSum_sq_negBinomialReal hL hμ

/-- **Mean–variance law.** On the parameter domain the variance is `V(μ) = μ + α μ²` with the
law's dispersion `α`: `α = 0` for Poisson, `α = 1 / θ` for the negative binomial. -/
theorem variance_pmf {L : CountLaw} (hL : L.Valid) {μ : ℝ} (hμ : 0 ≤ μ) :
    ∑' k : ℕ, (k : ℝ) ^ 2 * L.pmf μ k - (∑' k : ℕ, (k : ℝ) * L.pmf μ k) ^ 2 =
      L.varianceFn μ := by
  rw [(hasSum_sq_pmf hL hμ).tsum_eq, (hasSum_mul_pmf hL hμ).tsum_eq]
  ring

/-! ### Zero counts -/

/-- **Zero mean is the point mass at zero.** For a valid law, mean `0` puts all mass on the
count `0`. -/
theorem pmf_mean_zero {L : CountLaw} (hL : L.Valid) (k : ℕ) :
    L.pmf 0 k = if k = 0 then 1 else 0 := by
  cases L with
  | poisson =>
    rw [pmf_poisson le_rfl]
    rcases k with _ | k <;> simp
  | negBinomial θ => exact negBinomialReal_mean_zero hL k

/-- The zero class of the Poisson law at mean `μ ≥ 0` is `e^{-μ}`. -/
theorem pmf_poisson_zero {μ : ℝ} (hμ : 0 ≤ μ) : poisson.pmf μ 0 = exp (-μ) := by
  simp [pmf_poisson hμ]

/-- The zero class of the negative binomial law is `(θ / (θ + μ)) ^ θ`. -/
theorem pmf_negBinomial_zero (θ μ : ℝ) : (negBinomial θ).pmf μ 0 = (θ / (θ + μ)) ^ θ :=
  negBinomialReal_zero θ μ

/-- **Zero counts are at least as likely as under Poisson.** For a valid law and `μ ≥ 0`,
`P(N = 0) ≥ e^{-μ}`, with equality for the Poisson law. -/
theorem exp_neg_le_pmf_zero {L : CountLaw} (hL : L.Valid) {μ : ℝ} (hμ : 0 ≤ μ) :
    exp (-μ) ≤ L.pmf μ 0 := by
  cases L with
  | poisson => rw [pmf_poisson_zero hμ]
  | negBinomial θ => exact exp_neg_le_negBinomialReal_zero hL hμ

/-- For a positive mean every count has positive probability, the count `0` included. -/
theorem pmf_pos {L : CountLaw} (hL : L.Valid) {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    0 < L.pmf μ k := by
  cases L with
  | poisson => rw [pmf_poisson hμ.le]; positivity
  | negBinomial θ =>
    have hθ : 0 < θ := hL
    have h := ascPochhammer_pos k θ hθ
    simp only [pmf_negBinomial, negBinomialReal]
    positivity

/-- **A positive mean does not force zero counts.** For a valid law and `μ > 0`,
`P(N = 0) < 1`. -/
theorem pmf_zero_lt_one {L : CountLaw} (hL : L.Valid) {μ : ℝ} (hμ : 0 < μ) :
    L.pmf μ 0 < 1 := by
  have h1 := pmf_pos hL hμ 1
  have hs := hasSum_pmf hL hμ.le
  have hle : L.pmf μ 0 + L.pmf μ 1 ≤ 1 := by
    have := sum_le_hasSum (Finset.range 2) (fun k _ => pmf_nonneg hL hμ.le k) hs
    simpa [Finset.sum_range_succ] using this
  linarith

/-! ### The dispersion parametrization -/

@[simp] theorem ofDispersion_zero : ofDispersion 0 = poisson := by simp [ofDispersion]

theorem ofDispersion_of_ne_zero {α : ℝ} (hα : α ≠ 0) : ofDispersion α = negBinomial α⁻¹ := by
  simp [ofDispersion, hα]

/-- `ofDispersion α` is valid for `α ≥ 0`. -/
theorem valid_ofDispersion {α : ℝ} (hα : 0 ≤ α) : (ofDispersion α).Valid := by
  rcases hα.eq_or_lt with rfl | hα
  · simp [Valid]
  · rw [ofDispersion_of_ne_zero hα.ne']
    exact inv_pos.2 hα

/-- `ofDispersion α` has dispersion `α`. -/
@[simp] theorem dispersion_ofDispersion (α : ℝ) : (ofDispersion α).dispersion = α := by
  by_cases hα : α = 0
  · simp [hα]
  · simp [ofDispersion_of_ne_zero hα]

end CountLaw

/-! ### The count-matrix model -/

open CountLaw

/-- A count-matrix observation model for genes `G`, samples `J` and conditions `C`. Sample `j` is
a biological replicate of condition `condition j` with library size (size factor)
`librarySize j`; gene `g` has the count law `law g` and normalized expression `rate g c` in
condition `c`. The count of gene `g` in sample `j` has law `(law g).pmf (mean g j)` with mean
`librarySize j * rate g (condition j)`. -/
structure CountModel (G J C : Type*) where
  /-- The selected count law of each gene (Poisson or negative binomial with its shape). -/
  law : G → CountLaw
  /-- The condition of which each sample is a biological replicate. -/
  condition : J → C
  /-- The library size (size factor) of each sample. -/
  librarySize : J → ℝ
  /-- The normalized expression of each gene in each condition. -/
  rate : G → C → ℝ

namespace CountModel

variable {G J C : Type*} (M : CountModel G J C)

/-- The parameter domain: valid laws, nonnegative library sizes and positive rates. A library
size of `0` is allowed; the corresponding sample carries no information
(`countPMF_of_librarySize_eq_zero`). -/
structure Valid : Prop where
  law_valid : ∀ g, (M.law g).Valid
  librarySize_nonneg : ∀ j, 0 ≤ M.librarySize j
  rate_pos : ∀ g c, 0 < M.rate g c

/-- The mean count of gene `g` in sample `j`: library size times normalized expression. -/
noncomputable def mean (g : G) (j : J) : ℝ := M.librarySize j * M.rate g (M.condition j)

/-- The probability that gene `g` has count `k` in sample `j`. -/
noncomputable def countPMF (g : G) (j : J) (k : ℕ) : ℝ := (M.law g).pmf (M.mean g j) k

/-- The likelihood of a count matrix `Y`, the counts being independent across genes and
samples: the product of the entry masses. That it sums to `1` over all count matrices is not
proved in this file, and no theorem here relies on it. -/
noncomputable def likelihood [Fintype G] [Fintype J] (Y : G → J → ℕ) : ℝ :=
  ∏ g, ∏ j, M.countPMF g j (Y g j)

variable {M}

theorem mean_nonneg (hM : M.Valid) (g : G) (j : J) : 0 ≤ M.mean g j :=
  mul_nonneg (hM.librarySize_nonneg j) (hM.rate_pos g _).le

theorem mean_pos (hM : M.Valid) (g : G) {j : J} (hj : 0 < M.librarySize j) :
    0 < M.mean g j :=
  mul_pos hj (hM.rate_pos g _)

/-- **Normalization** of each entry's law. -/
theorem hasSum_countPMF (hM : M.Valid) (g : G) (j : J) : HasSum (M.countPMF g j) 1 :=
  hasSum_pmf (hM.law_valid g) (mean_nonneg hM g j)

/-- **Mean** of each entry: library size times normalized expression. -/
theorem hasSum_mul_countPMF (hM : M.Valid) (g : G) (j : J) :
    HasSum (fun k : ℕ => (k : ℝ) * M.countPMF g j k)
      (M.librarySize j * M.rate g (M.condition j)) :=
  hasSum_mul_pmf (hM.law_valid g) (mean_nonneg hM g j)

/-- **Mean–variance law** of each entry: `V(μ) = μ + α μ²` with the gene's dispersion `α`. -/
theorem variance_countPMF (hM : M.Valid) (g : G) (j : J) :
    ∑' k : ℕ, (k : ℝ) ^ 2 * M.countPMF g j k - (∑' k : ℕ, (k : ℝ) * M.countPMF g j k) ^ 2 =
      M.mean g j + (M.law g).dispersion * M.mean g j ^ 2 :=
  variance_pmf (hM.law_valid g) (mean_nonneg hM g j)

/-- **Library-size normalization.** For a nonzero library size, the mean divided by the
library size is the normalized expression of the sample's condition. -/
theorem mean_div_librarySize (g : G) {j : J} (hj : M.librarySize j ≠ 0) :
    M.mean g j / M.librarySize j = M.rate g (M.condition j) := by
  rw [mean, mul_div_cancel_left₀ _ hj]

/-- **Log link with library-size offset.** For a positive library size and rate, the mean is
`exp (log (rate g c) + log (librarySize j))`: linear predictor `log (rate g c)` plus offset
`log (librarySize j)`. -/
theorem mean_eq_exp (hM : M.Valid) (g : G) {j : J} (hj : 0 < M.librarySize j) :
    M.mean g j = exp (log (M.rate g (M.condition j)) + log (M.librarySize j)) := by
  rw [exp_add, exp_log (hM.rate_pos g _), exp_log hj, mean, mul_comm]

/-- **Replicates are exchangeable.** Two biological replicates of the same condition with the
same library size have the same count law for every gene. -/
theorem countPMF_eq_of_replicate (g : G) {j j' : J} (hc : M.condition j = M.condition j')
    (hs : M.librarySize j = M.librarySize j') : M.countPMF g j = M.countPMF g j' := by
  funext k
  rw [countPMF, countPMF, mean, mean, hc, hs]

/-- In a sample with nonzero library size the mean determines the normalized expression of the
sample's condition. The statistical form, from the count law, is `rate_eq_of_countPMF_eq`. -/
theorem rate_eq_of_mean_eq {M' : CountModel G J C} (g : G) {j : J}
    (hs : M.librarySize j = M'.librarySize j)
    (hj : M.librarySize j ≠ 0) (h : M.mean g j = M'.mean g j) :
    M.rate g (M.condition j) = M'.rate g (M'.condition j) := by
  rw [← mean_div_librarySize g hj, h, hs, mean_div_librarySize g (hs ▸ hj)]

/-- **Identifiability.** In a sample with nonzero library size, equal library sizes and equal
count laws in two valid models force equal rates of the sample's condition: the law determines
its mean, and the mean determines the rate. -/
theorem rate_eq_of_countPMF_eq {M' : CountModel G J C} (hM : M.Valid) (hM' : M'.Valid) (g : G)
    {j : J} (hs : M.librarySize j = M'.librarySize j) (hj : M.librarySize j ≠ 0)
    (h : M.countPMF g j = M'.countPMF g j) :
    M.rate g (M.condition j) = M'.rate g (M'.condition j) := by
  refine rate_eq_of_mean_eq g hs hj ?_
  have h1 := hasSum_mul_countPMF hM g j
  have h2 := hasSum_mul_countPMF hM' g j
  rw [h] at h1
  exact h1.unique h2

/-! ### Zero library size and zero counts -/

/-- **Zero library size.** A sample with library size `0` has mean `0`, so every count in it is
`0` almost surely, whatever the rates. -/
theorem countPMF_of_librarySize_eq_zero (hM : M.Valid) (g : G) {j : J}
    (hj : M.librarySize j = 0) (k : ℕ) : M.countPMF g j k = if k = 0 then 1 else 0 := by
  rw [countPMF, mean, hj, zero_mul, pmf_mean_zero (hM.law_valid g)]

/-- **A zero-library sample carries no information**: if sample `j` has library size `0` in two
valid models, its count law is the same in both, whatever their laws, conditions and rates. -/
theorem countPMF_eq_of_librarySize_eq_zero {M' : CountModel G J C} (hM : M.Valid)
    (hM' : M'.Valid) (g : G) {j : J} (hj : M.librarySize j = 0) (hj' : M'.librarySize j = 0) :
    M.countPMF g j = M'.countPMF g j := by
  funext k
  rw [countPMF_of_librarySize_eq_zero hM g hj, countPMF_of_librarySize_eq_zero hM' g hj']

/-- **Zero counts under positive library size.** For a positive library size a zero count has
probability strictly between `0` and `1`, and at least the Poisson zero class `e^{-μ}`. -/
theorem countPMF_zero_mem (hM : M.Valid) (g : G) {j : J} (hj : 0 < M.librarySize j) :
    exp (-M.mean g j) ≤ M.countPMF g j 0 ∧ M.countPMF g j 0 < 1 :=
  ⟨exp_neg_le_pmf_zero (hM.law_valid g) (mean_nonneg hM g j),
    pmf_zero_lt_one (hM.law_valid g) (mean_pos hM g hj)⟩

theorem likelihood_nonneg [Fintype G] [Fintype J] (hM : M.Valid) (Y : G → J → ℕ) :
    0 ≤ M.likelihood Y :=
  prod_nonneg fun g _ => prod_nonneg fun j _ =>
    pmf_nonneg (hM.law_valid g) (mean_nonneg hM g j) _

/-- **Every count matrix is possible** when all library sizes are positive, the all-zero matrix
included. -/
theorem likelihood_pos [Fintype G] [Fintype J] (hM : M.Valid)
    (hs : ∀ j, 0 < M.librarySize j) (Y : G → J → ℕ) : 0 < M.likelihood Y :=
  prod_pos fun g _ => prod_pos fun j _ => pmf_pos (hM.law_valid g) (mean_pos hM g (hs j)) _

/-- **A nonzero count in a zero-library sample is impossible.** -/
theorem likelihood_eq_zero [Fintype G] [Fintype J] (hM : M.Valid) {Y : G → J → ℕ} {g : G}
    {j : J} (hj : M.librarySize j = 0) (hY : Y g j ≠ 0) : M.likelihood Y = 0 :=
  prod_eq_zero (mem_univ g) (prod_eq_zero (mem_univ j)
    (by simp [countPMF_of_librarySize_eq_zero hM g hj, hY]))

/-! ### Bridge to negative binomial regression -/

/-- The condition design matrix: entry `(j, c)` is `1` if sample `j` is a replicate of
condition `c` and `0` otherwise. -/
def conditionDesign [DecidableEq C] (condition : J → C) : Matrix J C ℝ :=
  fun j c => if condition j = c then 1 else 0

/-- The condition design picks out the coefficient of the sample's condition. -/
theorem conditionDesign_mulVec [DecidableEq C] [Fintype C] (condition : J → C) (β : C → ℝ)
    (j : J) : (conditionDesign condition *ᵥ β) j = β (condition j) := by
  simp [conditionDesign, mulVec, dotProduct]

/-- **Per-entry log-likelihood.** For a negative binomial gene and a positive library size, the
log mass function is a rate-free constant plus `nbKernel θ k η` at the linear predictor
`η = log (rate g c) + log (librarySize j)`. -/
theorem log_countPMF_negBinomial (hM : M.Valid) {g : G} {θ : ℝ}
    (hg : M.law g = negBinomial θ) {j : J} (hj : 0 < M.librarySize j) (k : ℕ) :
    log (M.countPMF g j k) = log ((ascPochhammer ℝ k).eval θ / k !) + θ * log θ +
      nbKernel θ k (log (M.rate g (M.condition j)) + log (M.librarySize j)) := by
  have hθ : 0 < θ := by
    have h := hM.law_valid g
    rw [hg] at h
    exact h
  rw [countPMF, hg, pmf_negBinomial, mean_eq_exp hM g hj, log_negBinomialReal_exp hθ]

/-- **The gene-wise likelihood is a negative binomial regression.** For a negative binomial
gene with shape `θ` and positive library sizes, the log-likelihood of the gene's counts is a
rate-free constant plus `nbLogLik θ X o y β` with the condition design `X`, offsets
`oⱼ = log (librarySize j)`, responses `yⱼ = Y g j` and coefficients `β c = log (rate g c)`. -/
theorem sum_log_countPMF_eq_nbLogLik [Fintype J] [Fintype C] [DecidableEq C] (hM : M.Valid)
    {g : G} {θ : ℝ} (hg : M.law g = negBinomial θ) (hs : ∀ j, 0 < M.librarySize j)
    (Y : G → J → ℕ) :
    ∑ j, log (M.countPMF g j (Y g j)) =
      ∑ j, (log ((ascPochhammer ℝ (Y g j)).eval θ / (Y g j)!) + θ * log θ) +
        nbLogLik θ (conditionDesign M.condition) (fun j => log (M.librarySize j))
          (fun j => (Y g j : ℝ)) (fun c => log (M.rate g c)) := by
  simp only [nbLogLik, conditionDesign_mulVec, log_countPMF_negBinomial hM hg (hs _),
    ← sum_add_distrib]

end CountModel

end MathlibExt.Probability.Statistics.GLM.CountData
