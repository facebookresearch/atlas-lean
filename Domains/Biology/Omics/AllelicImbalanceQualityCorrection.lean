/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Probability.Distributions.BetaBinomial
public import MathlibExt.Probability.Distributions.BetaMoments
public import MathlibExt.Probability.Quantile
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import MathlibExt.Analysis.SpecialFunctions.Gamma.AscPochhammer

/-!
# The quality correction constant for allelic imbalance

Mendelevich et al. (2021) measure how much more two replicate RNA-seq libraries of the same
sample disagree on the allelic imbalance (AI) of genes than binomial sampling of reads predicts.
The AI of a gene with `M` maternal and `P` paternal reads is `M / (M + P)`. Genes are binned by
coverage, the pooled AI of each bin is fitted by a two-component mixture of symmetric
beta-binomial laws, and pairs of replicates are drawn from the fitted mixture with pure binomial
sampling of reads. The **quality correction constant** (QCC) is the constant that best fits the
ratios `Q^obs_{q,i} / Q^exp_{q,i}` of the observed to the expected quantiles of the replicate
difference `ΔAI`, over the bins `i` and a fixed set of quantile levels `q`; with `M ≥ 3`
replicates it is the mean of the `C(M, 2)` pairwise constants. Confidence intervals for AI then
treat the AI of a gene of coverage `C` as a binomial proportion of effective coverage
`C / QCC ^ 2`.

## Conventions

* **Bins.** For a base `b` (the source takes `b = 1.05`) the bin boundaries are
  `C̄_k = ⌈b ^ k⌉` and the bins are `B_i = (C̄_{i-1}, C̄_i]`, `i ≥ 1`, with representative
  coverage `Ĉ_i = √(C̄_{i-1} C̄_i)`. As in the source (Methods, Eq. (3)), the genes of a pair of
  replicates are binned by their mean coverage `(C_{1g} + C_{2g}) / 2`; a gene with no reads in
  one of the two replicates has no AI estimate there and is left out.
* **Whole reads.** Beta-binomial and binomial laws need a whole number of trials, while `Ĉ_i` is
  in general irrational. Bin `i` is modelled with `c_i = ⌈Ĉ_i⌉` reads per replicate
  (`binReadCoverage`), so `2 c_i` pooled reads. The reference implementation (Qllelic) likewise
  models a bin with a whole number of reads, `⌈b ^ (i - 1/2)⌉`, the geometric mean of the
  unrounded boundaries rounded up.
* **Fitted parameters.** The mixture of each bin is the output of the source's EM fit, which
  depends on starting values and a stopping rule; it is an input here (`AIMixture`), with the
  source's constraints `0 ≤ ω₁ ≤ 1`, `α₁ > 1` and `α₂ ∈ (0, 1)`. The M-step's shape update
  (`mStepShape`, `momentMatchingShape`) is defined, and shown to match the variance of the
  symmetric beta-binomial law.
* **Expected law.** Instead of simulating `5000` genes, the expected law of `ΔAI` is the exact
  law that the simulation samples: a success probability `p` drawn from the mixture of
  `Beta(α_k, α_k)` laws, then two independent `Bin(c_i, p)` read counts `X₁, X₂`
  (`replicatePairMass_eq_integral`), and `ΔAI = |X₁ - X₂| / c_i` (`expectedDeltaAILaw`). It is
  defined from the fitted mixture of `BetaBin(2 c_i, α_k, α_k)` laws, which the pooled count
  `X₁ + X₂` follows (`sum_antidiagonal_replicatePairMass`), split hypergeometrically between the
  replicates (`replicatePairMass`).
* **Absolute differences.** `ΔAI` is the absolute difference `|AI₁ - AI₂|` of the two replicates'
  AI estimates, as in the reference implementation; the source's quantile levels are
  `0.2, 0.35, 0.5, 0.65, 0.8, 0.9, 0.95`.
* **Quantiles.** Both quantiles are the lower quantile `inf {x | q ≤ F(x)}` of the law
  (`ProbabilityTheory.cdfQuantile`): of the empirical law of the bin's genes for `Q^obs`, and of
  the expected law for `Q^exp`.
* **The fit.** "Linearly fitted with a constant" is the least-squares constant, the mean of the
  ratios (`sum_sq_sub_quantileRatioFit`). A ratio with `Q^exp_{q,i} = 0`, or in a bin with no
  genes, is undefined and left out of the fit, as the reference implementation drops non-finite
  ratios; the fit of no ratio is `0`.
* **More replicates.** With replicates `0, …, M - 1`, the QCC is the mean, over the `C(M, 2)`
  pairs `r < r'`, of the pairwise QCCs, each pair with its own fitted mixtures
  (`card_replicatePairs`). For `M = 2` it is the QCC of the one pair
  (`qualityCorrectionConstant_two`).

## Main definitions

* `coverageBinBoundary`, `InCoverageBin`, `representativeCoverage`, `binReadCoverage`: the bins.
* `AIMixture`, `pooledMass`: the fitted two-component symmetric beta-binomial mixture of a bin.
* `momentMatchingShape`, `mStepShape`: the moment-matching M-step for a shape parameter.
* `replicatePairMass`, `expectedDeltaAILaw`: the expected law of a pair of replicates and of
  their AI difference.
* `allelicImbalance`, `binGenes`, `observedDeltaAILaw`: the observed AI differences of a bin.
* `quantileRatioFit`: the least-squares constant fitted to the ratios of observed to expected
  quantiles.
* `pairQualityCorrectionConstant`, `qualityCorrectionConstant`: the QCC of two replicates and of
  `M` replicates.
* `effectiveCoverage`: the coverage `C / QCC ^ 2` of the corrected binomial proportion.

## Main results

* `existsUnique_inCoverageBin`, `representativeCoverage_mem_Icc`: for `b > 1` the bins partition
  the coverages above `1`, and `Ĉ_i` lies in the closure of `B_i`.
* `sum_pooledMass`, `pooledMass_symm`, `sum_mul_pooledMass`: the pooled AI law is a symmetric
  probability law with mean count `c`.
* `momentMatchingShape_eq_iff`: the moment-matching shape inverts the variance
  `n (2 α + n) / (4 (2 α + 1))` of `BetaBin(n, α, α)`, `n = 2 c`, for `α`; and
  `mStepShape_betaBinomialPMF`: the M-step recovers `α` from the exact law.
* `replicatePairMass_eq_integral`: the replicate-pair law is that of two independent `Bin(c, p)`
  counts with `p` drawn from the mixture of `Beta(α_k, α_k)` laws;
  `sum_antidiagonal_replicatePairMass`: the pooled count follows the fitted mixture;
  `isProbabilityMeasure_expectedDeltaAILaw`.
* `sum_sq_sub_quantileRatioFit`, `quantileRatioFit_eq_of_forall`: the fit is the least-squares
  constant, and it is `κ` when every observed quantile is `κ` times the expected one.
* `sqrt_div_effectiveCoverage`: deflating the coverage to `C / QCC ^ 2` widens the standard
  deviation of a binomial proportion by the factor `QCC`.

## References

* A. Mendelevich, S. Vinogradova, S. Gupta, A. A. Mironov, S. R. Sunyaev and A. A. Gimelbrant,
  "Replicate sequencing libraries are important for quantification of allelic imbalance",
  Nat. Commun. 12 (2021), 3370, <https://doi.org/10.1038/s41467-021-23544-8>: Methods,
  "Calculation of quality correction constant for 2 replicates" to "Adjusting AI confidence
  intervals", Eqs. (3)–(11); reference implementation Qllelic,
  <https://github.com/gimelbrantlab/Qllelic> (`ComputeCorrConstantFor2Reps`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal

namespace Domains.Biology.Omics.AllelicImbalance

/-! ### Coverage bins -/

/-- The `k`-th **coverage bin boundary** `C̄_k = ⌈b ^ k⌉` for a base `b` (Mendelevich et al. 2021
take `b = 1.05`). The coverage bins are `B_i = (C̄_{i-1}, C̄_i]` for `i ≥ 1` (`InCoverageBin`);
`C̄_0 = 1`. -/
noncomputable def coverageBinBoundary (b : ℝ) (k : ℕ) : ℕ :=
  ⌈b ^ k⌉₊

/-- A mean coverage `x` lies in the **coverage bin** `B_i = (C̄_{i-1}, C̄_i]`, `i ≥ 1`, of base `b`,
where `C̄_k = ⌈b ^ k⌉` (`coverageBinBoundary`). For `b > 1`, every `x > 1` lies in exactly one bin
(`existsUnique_inCoverageBin`). -/
def InCoverageBin (b : ℝ) (i : ℕ) (x : ℝ) : Prop :=
  1 ≤ i ∧ (coverageBinBoundary b (i - 1) : ℝ) < x ∧ x ≤ coverageBinBoundary b i

noncomputable instance (b : ℝ) (i : ℕ) (x : ℝ) : Decidable (InCoverageBin b i x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The **representative coverage** `Ĉ_i = √(C̄_{i-1} C̄_i)` of the coverage bin
`B_i = (C̄_{i-1}, C̄_i]` of base `b`, where `C̄_k = ⌈b ^ k⌉` (`coverageBinBoundary`); for `b ≥ 1`
it lies in `[C̄_{i-1}, C̄_i]` (`representativeCoverage_mem_Icc`). -/
noncomputable def representativeCoverage (b : ℝ) (i : ℕ) : ℝ :=
  √((coverageBinBoundary b (i - 1) : ℝ) * coverageBinBoundary b i)

/-- The **read coverage of a bin**: the number `c_i = ⌈Ĉ_i⌉` of reads per replicate with which the
bin `B_i` of base `b` is modelled, the representative coverage `Ĉ_i = √(C̄_{i-1} C̄_i)`
(`representativeCoverage`) rounded up to a whole number of reads, as binomial and beta-binomial
laws need. The pooled replicate then has `2 c_i` reads. The reference implementation (Qllelic)
likewise uses a whole number of reads, `⌈b ^ (i - 1/2)⌉`. -/
noncomputable def binReadCoverage (b : ℝ) (i : ℕ) : ℕ :=
  ⌈representativeCoverage b i⌉₊

@[simp]
theorem coverageBinBoundary_zero (b : ℝ) : coverageBinBoundary b 0 = 1 := by
  simp [coverageBinBoundary]

/-- For `b ≥ 1` the bin boundaries `⌈b ^ k⌉` are nondecreasing in `k`. -/
theorem coverageBinBoundary_mono {b : ℝ} (hb : 1 ≤ b) : Monotone (coverageBinBoundary b) :=
  fun _ _ hkl => Nat.ceil_mono (pow_le_pow_right₀ hb hkl)

/-- For `b ≥ 1`, the representative coverage `Ĉ_i = √(C̄_{i-1} C̄_i)` lies between the
boundaries `C̄_{i-1} = ⌈b ^ (i - 1)⌉` and `C̄_i = ⌈b ^ i⌉` of its bin. -/
theorem representativeCoverage_mem_Icc {b : ℝ} (hb : 1 ≤ b) (i : ℕ) :
    representativeCoverage b i ∈
      Set.Icc (coverageBinBoundary b (i - 1) : ℝ) (coverageBinBoundary b i) := by
  have hle : (coverageBinBoundary b (i - 1) : ℝ) ≤ coverageBinBoundary b i := by
    exact_mod_cast coverageBinBoundary_mono hb (Nat.sub_le i 1)
  have h0 : (0 : ℝ) ≤ coverageBinBoundary b (i - 1) := Nat.cast_nonneg _
  constructor
  · calc (coverageBinBoundary b (i - 1) : ℝ)
        = √((coverageBinBoundary b (i - 1) : ℝ) * coverageBinBoundary b (i - 1)) :=
          (Real.sqrt_mul_self h0).symm
      _ ≤ representativeCoverage b i :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle h0)
  · calc representativeCoverage b i
        ≤ √((coverageBinBoundary b i : ℝ) * coverageBinBoundary b i) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _))
      _ = coverageBinBoundary b i := Real.sqrt_mul_self (Nat.cast_nonneg _)

/-- For a base `b > 1`, every mean coverage `x > 1` lies in exactly one coverage bin
`B_i = (⌈b ^ (i - 1)⌉, ⌈b ^ i⌉]`, `i ≥ 1`. -/
theorem existsUnique_inCoverageBin {b x : ℝ} (hb : 1 < b) (hx : 1 < x) :
    ∃! i, InCoverageBin b i x := by
  have hex : ∃ k, x ≤ coverageBinBoundary b k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt x hb
    exact ⟨k, hk.le.trans (Nat.le_ceil _)⟩
  classical
  refine ⟨Nat.find hex, ⟨?_, ?_, Nat.find_spec hex⟩, ?_⟩
  · rw [Nat.one_le_iff_ne_zero]
    intro h0
    have := Nat.find_spec hex
    rw [h0, coverageBinBoundary_zero, Nat.cast_one] at this
    linarith
  · have hpos : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, coverageBinBoundary_zero, Nat.cast_one] at this
      linarith
    exact lt_of_not_ge (Nat.find_min hex (by omega))
  · rintro j ⟨hj1, hjlo, hjhi⟩
    apply le_antisymm
    · by_contra hlt'
      have hlt := lt_of_not_ge hlt'
      have hmono := coverageBinBoundary_mono hb.le (show Nat.find hex ≤ j - 1 by omega)
      have := Nat.find_spec hex
      have hcast : (coverageBinBoundary b (Nat.find hex) : ℝ) ≤ coverageBinBoundary b (j - 1) := by
        exact_mod_cast hmono
      linarith
    · exact Nat.find_min' hex hjhi

/-! ### The fitted mixture -/

/-- The fitted parameters of the **two-component symmetric beta-binomial mixture** of one coverage
bin (Mendelevich et al. 2021, Eq. (4)): with probability `ω₁ = weight` the pooled AI of a gene
follows `BetaBin(2 c, α₁, α₁) / (2 c)` with `α₁ = shape₁ > 1` (mostly biallelic genes), and with
probability `ω₂ = 1 - ω₁` it follows `BetaBin(2 c, α₂, α₂) / (2 c)` with `α₂ = shape₂ ∈ (0, 1)`
(strongly imbalanced genes); see `pooledMass`. -/
structure AIMixture where
  /-- The weight `ω₁` of the first component; the second has weight `ω₂ = 1 - ω₁`. -/
  weight : ℝ
  /-- The shape `α₁` of the first component, `BetaBin(2 c, α₁, α₁)`. -/
  shape₁ : ℝ
  /-- The shape `α₂` of the second component, `BetaBin(2 c, α₂, α₂)`. -/
  shape₂ : ℝ
  weight_nonneg : 0 ≤ weight
  weight_le_one : weight ≤ 1
  one_lt_shape₁ : 1 < shape₁
  shape₂_pos : 0 < shape₂
  shape₂_lt_one : shape₂ < 1

namespace AIMixture

variable (θ : AIMixture)

theorem shape₁_pos : 0 < θ.shape₁ := zero_lt_one.trans θ.one_lt_shape₁

theorem one_sub_weight_nonneg : 0 ≤ 1 - θ.weight := sub_nonneg.mpr θ.weight_le_one

end AIMixture

/-- The **pooled AI law of a bin** (Mendelevich et al. 2021, Eq. (4)): the probability that `k` of
the `2 c` reads of the pooled replicate come from the maternal allele, under the fitted mixture
`θ`,

  `ω₁ BB(2 c; α₁, α₁)(k) + ω₂ BB(2 c; α₂, α₂)(k)`,

with `BB` the beta-binomial mass function (`ProbabilityTheory.betaBinomialPMF`) and
`ω₂ = 1 - ω₁`; the pooled AI is `k / (2 c)`. It is a probability law on `{0, …, 2 c}`
(`sum_pooledMass`), symmetric about `c` (`pooledMass_symm`) with mean `c`
(`sum_mul_pooledMass`). -/
noncomputable def pooledMass (θ : AIMixture) (c k : ℕ) : ℝ :=
  θ.weight * betaBinomialPMF (2 * c) θ.shape₁ θ.shape₁ k +
    (1 - θ.weight) * betaBinomialPMF (2 * c) θ.shape₂ θ.shape₂ k

private theorem betaBinomialPMF_nonneg {n : ℕ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) :
    0 ≤ betaBinomialPMF n α β k := by
  unfold betaBinomialPMF
  have h1 := ascPochhammer_pos k α hα
  have h2 := ascPochhammer_pos (n - k) β hβ
  have h3 := ascPochhammer_pos n (α + β) (add_pos hα hβ)
  positivity

theorem pooledMass_nonneg (θ : AIMixture) (c k : ℕ) : 0 ≤ pooledMass θ c k :=
  add_nonneg
    (mul_nonneg θ.weight_nonneg (betaBinomialPMF_nonneg θ.shape₁_pos θ.shape₁_pos k))
    (mul_nonneg θ.one_sub_weight_nonneg (betaBinomialPMF_nonneg θ.shape₂_pos θ.shape₂_pos k))

/-- The pooled AI law of a bin is a probability law on `{0, …, 2 c}`. -/
theorem sum_pooledMass (θ : AIMixture) (c : ℕ) :
    ∑ k ∈ range (2 * c + 1), pooledMass θ c k = 1 := by
  simp only [pooledMass, sum_add_distrib, ← mul_sum,
    sum_betaBinomialPMF _ θ.shape₁_pos θ.shape₁_pos,
    sum_betaBinomialPMF _ θ.shape₂_pos θ.shape₂_pos]
  ring

/-- A symmetric beta-binomial mass is symmetric: `BB(n; α, α)(n - k) = BB(n; α, α)(k)`. -/
private theorem betaBinomialPMF_self_symm {n k : ℕ} (hk : k ≤ n) (α : ℝ) :
    betaBinomialPMF n α α (n - k) = betaBinomialPMF n α α k := by
  unfold betaBinomialPMF
  rw [Nat.choose_symm hk, Nat.sub_sub_self hk]
  ring

/-- The pooled AI law of a bin is symmetric about `c`: the counts `k` and `2 c - k` are equally
likely. -/
theorem pooledMass_symm (θ : AIMixture) {c k : ℕ} (hk : k ≤ 2 * c) :
    pooledMass θ c (2 * c - k) = pooledMass θ c k := by
  simp only [pooledMass, betaBinomialPMF_self_symm hk]

/-- The mean maternal count of the pooled replicate is `c`, so the mean pooled AI is `1 / 2`. -/
theorem sum_mul_pooledMass (θ : AIMixture) (c : ℕ) :
    ∑ k ∈ range (2 * c + 1), (k : ℝ) * pooledMass θ c k = c := by
  have h₁ := sum_mul_betaBinomialPMF (n := 2 * c) θ.shape₁_pos θ.shape₁_pos
  have h₂ := sum_mul_betaBinomialPMF (n := 2 * c) θ.shape₂_pos θ.shape₂_pos
  have e₁ : ((2 * c : ℕ) : ℝ) * θ.shape₁ / (θ.shape₁ + θ.shape₁) = c := by
    have := θ.shape₁_pos.ne'
    push_cast
    field_simp
    ring
  have e₂ : ((2 * c : ℕ) : ℝ) * θ.shape₂ / (θ.shape₂ + θ.shape₂) = c := by
    have := θ.shape₂_pos.ne'
    push_cast
    field_simp
    ring
  have hsplit : ∀ k : ℕ, (k : ℝ) * pooledMass θ c k =
      θ.weight * ((k : ℝ) * betaBinomialPMF (2 * c) θ.shape₁ θ.shape₁ k) +
        (1 - θ.weight) * ((k : ℝ) * betaBinomialPMF (2 * c) θ.shape₂ θ.shape₂ k) := fun k => by
    unfold pooledMass
    ring
  simp_rw [hsplit]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, h₁, h₂, e₁, e₂]
  ring

/-! ### The moment-matching M-step -/

/-- **Variance of the symmetric beta-binomial law.** For `α > 0`, the law `BetaBin(n, α, α)` has
mean `n / 2` and variance

  `∑ₖ (k - n / 2) ^ 2 BB(n; α, α)(k) = n (2 α + n) / (4 (2 α + 1))`. -/
private theorem sum_sub_sq_mul_betaBinomialPMF_self (n : ℕ) {α : ℝ} (hα : 0 < α) :
    ∑ k ∈ range (n + 1), ((k : ℝ) - n / 2) ^ 2 * betaBinomialPMF n α α k =
      n * (2 * α + n) / (4 * (2 * α + 1)) := by
  have hvar := variance_betaBinomial (n := n) hα hα
  have hmean := sum_mul_betaBinomialPMF (n := n) hα hα
  have hsum := sum_betaBinomialPMF n hα hα
  have hexp : ∑ k ∈ range (n + 1), ((k : ℝ) - n / 2) ^ 2 * betaBinomialPMF n α α k =
      ∑ k ∈ range (n + 1), (k : ℝ) ^ 2 * betaBinomialPMF n α α k -
        n * ∑ k ∈ range (n + 1), (k : ℝ) * betaBinomialPMF n α α k +
        (n / 2) ^ 2 * ∑ k ∈ range (n + 1), betaBinomialPMF n α α k := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  have hα' : α + α ≠ 0 := by positivity
  have hα'' : α + α + 1 ≠ 0 := by positivity
  have h2 : 2 * α + 1 ≠ 0 := by positivity
  rw [hexp, hsum, hmean]
  rw [hmean] at hvar
  have hsq : ∑ k ∈ range (n + 1), (k : ℝ) ^ 2 * betaBinomialPMF n α α k =
      n * (α / (α + α)) * (1 - α / (α + α)) * (1 + (n - 1) * (1 / (α + α + 1))) +
        (n * α / (α + α)) ^ 2 := by linarith
  rw [hsq]
  field_simp
  ring

/-- The **moment-matching shape** of the M-step (Mendelevich et al. 2021, Eq. (7)): the shape `α`
for which `BetaBin(2 c, α, α)` has variance `v`,

  `α = ((2 c) ^ 2 - 4 v) / (8 v - 4 c)`,

obtained by inverting `v = 2 c (2 α + 2 c) / (4 (2 α + 1))` (`momentMatchingShape_eq_iff`); it
is `0` when `8 v = 4 c`. -/
noncomputable def momentMatchingShape (c : ℕ) (v : ℝ) : ℝ :=
  ((2 * c) ^ 2 - 4 * v) / (8 * v - 4 * c)

/-- For `c ≥ 1` and `α > 0`, the moment-matching shape of `v` is `α` exactly when `v` is the
variance `2 c (2 α + 2 c) / (4 (2 α + 1))` of `BetaBin(2 c, α, α)`. -/
theorem momentMatchingShape_eq_iff {c : ℕ} (hc : 1 ≤ c) {α v : ℝ} (hα : 0 < α) :
    momentMatchingShape c v = α ↔
      v = ((2 * c : ℕ) : ℝ) * (2 * α + (2 * c : ℕ)) / (4 * (2 * α + 1)) := by
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have h2 : 2 * α + 1 ≠ 0 := by positivity
  unfold momentMatchingShape
  push_cast
  constructor
  · intro h
    have hden : 8 * v - 4 * c ≠ 0 := by
      intro h0
      rw [h0, div_zero] at h
      exact hα.ne' h.symm
    rw [div_eq_iff hden] at h
    field_simp
    linarith
  · intro h
    subst h
    have hden : 8 * ((2 * c : ℝ) * (2 * α + 2 * c) / (4 * (2 * α + 1))) - 4 * c ≠ 0 := by
      have : 8 * ((2 * c : ℝ) * (2 * α + 2 * c) / (4 * (2 * α + 1))) - 4 * c =
          4 * c * (2 * c - 1) / (2 * α + 1) := by
        field_simp
        ring
      rw [this]
      have : (0 : ℝ) < 2 * c - 1 := by linarith
      positivity
    rw [div_eq_iff hden]
    field_simp
    ring

/-- The **M-step for a shape parameter** (Mendelevich et al. 2021, Eq. (7)): given the
responsibilities `γ n ≥ 0` of one mixture component for the observations `n ∈ s`, whose maternal
counts out of the `2 c` pooled reads are `x n`, the new shape is the moment-matching shape
(`momentMatchingShape`) of the responsibility-weighted variance about the mean count `c`,

  `Σ = ∑ₙ γₙ (xₙ - c) ^ 2 / ∑ₙ γₙ`. -/
noncomputable def mStepShape {ι : Type*} (c : ℕ) (s : Finset ι) (γ : ι → ℝ) (x : ι → ℕ) : ℝ :=
  momentMatchingShape c ((∑ n ∈ s, γ n * ((x n : ℝ) - c) ^ 2) / ∑ n ∈ s, γ n)

/-- The M-step is consistent: for `c ≥ 1` and `α > 0`, weighting each count `k ∈ {0, …, 2 c}` by
its probability under `BetaBin(2 c, α, α)` returns the shape `α`. -/
theorem mStepShape_betaBinomialPMF {c : ℕ} (hc : 1 ≤ c) {α : ℝ} (hα : 0 < α) :
    mStepShape c (range (2 * c + 1)) (betaBinomialPMF (2 * c) α α) (fun k => k) = α := by
  unfold mStepShape
  rw [momentMatchingShape_eq_iff hc hα, sum_betaBinomialPMF _ hα hα, div_one]
  have h := sum_sub_sq_mul_betaBinomialPMF_self (2 * c) hα
  have hc2 : ((2 * c : ℕ) : ℝ) / 2 = c := by push_cast; ring
  rw [hc2] at h
  rw [← h]
  exact sum_congr rfl fun k _ => mul_comm _ _

/-! ### The expected law of a pair of replicates -/

/-- The **expected law of a pair of replicates** of a bin with `c` reads per replicate and fitted
mixture `θ` (Mendelevich et al. 2021, Eqs. (8)–(9)): the probability that the two replicates have
`j₁` and `j₂` maternal reads,

  `C(c, j₁) C(c, j₂) / C(2 c, j₁ + j₂) · pooledMass θ c (j₁ + j₂)`.

The pooled count `j₁ + j₂` of the `2 c` reads follows the fitted mixture (`pooledMass`), and given
it the reads are split between the two replicates hypergeometrically, as binomial sampling with a
common success probability splits them. This is the law the source simulates: a success
probability `p` drawn from the mixture `ω₁ Beta(α₁, α₁) + ω₂ Beta(α₂, α₂)`, then two independent
`Bin(c, p)` counts (`replicatePairMass_eq_integral`). It vanishes when `j₁ > c` or `j₂ > c`, and
it is a probability law on `{0, …, c} × {0, …, c}` (`sum_replicatePairMass`). -/
noncomputable def replicatePairMass (θ : AIMixture) (c j₁ j₂ : ℕ) : ℝ :=
  c.choose j₁ * c.choose j₂ / (2 * c).choose (j₁ + j₂) * pooledMass θ c (j₁ + j₂)

/-- `B(α + s, α + t) / B(α, α) = α⁽ˢ⁾ α⁽ᵗ⁾ / (2 α)⁽ˢ⁺ᵗ⁾` for `α > 0`. -/
private theorem beta_add_nat_div_beta {α : ℝ} (hα : 0 < α) (s t : ℕ) :
    beta (α + s) (α + t) / beta α α =
      (ascPochhammer ℝ s).eval α * (ascPochhammer ℝ t).eval α /
        (ascPochhammer ℝ (s + t)).eval (α + α) := by
  have hne : ∀ (a : ℝ), 0 < a → ∀ (k : ℕ), ∀ j < k, a + j ≠ 0 :=
    fun a ha k j _ => by positivity
  have hs := Real.Gamma_add_nat_eq s (hne α hα s)
  have ht := Real.Gamma_add_nat_eq t (hne α hα t)
  have hst := Real.Gamma_add_nat_eq (s + t) (hne (α + α) (by positivity) (s + t))
  have hG := Real.Gamma_pos_of_pos hα
  have hG2 := Real.Gamma_pos_of_pos (show 0 < α + α by positivity)
  have hP := ascPochhammer_pos (s + t) (α + α) (by positivity)
  unfold beta
  rw [show α + s + (α + t) = α + α + ((s + t : ℕ) : ℝ) by push_cast; ring, hs, ht, hst]
  field_simp

/-- One component of the replicate-pair law in closed form. -/
private theorem integral_pair_betaMeasure {α : ℝ} (hα : 0 < α) {c j₁ j₂ : ℕ} (h₁ : j₁ ≤ c)
    (h₂ : j₂ ≤ c) :
    ∫ p, (c.choose j₁ * p ^ j₁ * (1 - p) ^ (c - j₁)) * (c.choose j₂ * p ^ j₂ * (1 - p) ^ (c - j₂))
        ∂betaMeasure α α =
      c.choose j₁ * c.choose j₂ / (2 * c).choose (j₁ + j₂) *
        betaBinomialPMF (2 * c) α α (j₁ + j₂) := by
  have hsplit : ∀ p : ℝ,
      (c.choose j₁ * p ^ j₁ * (1 - p) ^ (c - j₁)) * (c.choose j₂ * p ^ j₂ * (1 - p) ^ (c - j₂)) =
        (c.choose j₁ * c.choose j₂ : ℝ) * (p ^ (j₁ + j₂) * (1 - p) ^ (2 * c - (j₁ + j₂))) := by
    intro p
    rw [show 2 * c - (j₁ + j₂) = (c - j₁) + (c - j₂) by omega, pow_add, pow_add]
    ring
  simp_rw [hsplit]
  rw [integral_const_mul, integral_pow_mul_one_sub_pow_betaMeasure hα hα,
    beta_add_nat_div_beta hα, show j₁ + j₂ + (2 * c - (j₁ + j₂)) = 2 * c by omega]
  have hC : ((2 * c).choose (j₁ + j₂) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  unfold betaBinomialPMF
  field_simp

/-- **The replicate-pair law is the simulated law.** The probability that the two replicates have
`j₁` and `j₂` maternal reads is that of drawing a success probability `p` from the mixture
`ω₁ Beta(α₁, α₁) + ω₂ Beta(α₂, α₂)` and then two independent `Bin(c, p)` counts `j₁` and `j₂`,

  `∑ₖ ωₖ ∫ b(j₁, p) b(j₂, p) dBeta(αₖ, αₖ)(p)`,

where `b(j, p) = C(c, j) p ^ j (1 - p) ^ (c - j)` is the binomial mass. -/
theorem replicatePairMass_eq_integral (θ : AIMixture) (c j₁ j₂ : ℕ) :
    replicatePairMass θ c j₁ j₂ =
      θ.weight * ∫ p, (c.choose j₁ * p ^ j₁ * (1 - p) ^ (c - j₁)) *
          (c.choose j₂ * p ^ j₂ * (1 - p) ^ (c - j₂)) ∂betaMeasure θ.shape₁ θ.shape₁ +
        (1 - θ.weight) * ∫ p, (c.choose j₁ * p ^ j₁ * (1 - p) ^ (c - j₁)) *
          (c.choose j₂ * p ^ j₂ * (1 - p) ^ (c - j₂)) ∂betaMeasure θ.shape₂ θ.shape₂ := by
  by_cases h : j₁ ≤ c ∧ j₂ ≤ c
  · rw [integral_pair_betaMeasure θ.shape₁_pos h.1 h.2,
      integral_pair_betaMeasure θ.shape₂_pos h.1 h.2, replicatePairMass, pooledMass]
    ring
  · have hz : (c.choose j₁ : ℝ) * c.choose j₂ = 0 := by
      rcases not_and_or.mp h with h | h
      · rw [Nat.choose_eq_zero_of_lt (show c < j₁ by omega)]
        simp
      · rw [Nat.choose_eq_zero_of_lt (show c < j₂ by omega)]
        simp
    have hz' : ∀ p : ℝ, (c.choose j₁ * p ^ j₁ * (1 - p) ^ (c - j₁)) *
        (c.choose j₂ * p ^ j₂ * (1 - p) ^ (c - j₂)) = 0 := by
      intro p
      linear_combination (p ^ j₁ * (1 - p) ^ (c - j₁) * p ^ j₂ * (1 - p) ^ (c - j₂)) * hz
    simp only [replicatePairMass, hz', integral_zero, mul_zero, add_zero, hz, zero_div, zero_mul]

theorem replicatePairMass_nonneg (θ : AIMixture) (c j₁ j₂ : ℕ) :
    0 ≤ replicatePairMass θ c j₁ j₂ := by
  rw [replicatePairMass]
  have := pooledMass_nonneg θ c (j₁ + j₂)
  positivity

/-- **The pooled count follows the fitted mixture.** Under the replicate-pair law, the
probability that the two replicates together have `k` maternal reads is
`pooledMass θ c k`. -/
theorem sum_antidiagonal_replicatePairMass (θ : AIMixture) (c k : ℕ) :
    ∑ ij ∈ antidiagonal k, replicatePairMass θ c ij.1 ij.2 = pooledMass θ c k := by
  simp only [replicatePairMass]
  have hk : ∀ ij ∈ antidiagonal k, ij.1 + ij.2 = k := fun ij hij => mem_antidiagonal.mp hij
  rw [sum_congr rfl fun ij hij => by rw [hk ij hij]]
  rw [← sum_mul, ← sum_div]
  have hV : (∑ ij ∈ antidiagonal k, (c.choose ij.1 * c.choose ij.2 : ℝ)) = (2 * c).choose k := by
    rw [two_mul, Nat.add_choose_eq]
    push_cast
    rfl
  rw [hV]
  by_cases hk2 : k ≤ 2 * c
  · have hC : ((2 * c).choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk2).ne'
    rw [div_self hC, one_mul]
  · have hz : (2 * c).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hz, pooledMass, betaBinomialPMF]

/-- The replicate-pair law is a probability law on `{0, …, c} × {0, …, c}`. -/
theorem sum_replicatePairMass (θ : AIMixture) (c : ℕ) :
    ∑ j ∈ range (c + 1) ×ˢ range (c + 1), replicatePairMass θ c j.1 j.2 = 1 := by
  rw [← sum_fiberwise_of_maps_to (g := fun j : ℕ × ℕ => j.1 + j.2) (t := range (2 * c + 1))
    (fun j hj => by
      simp only [mem_product, mem_range] at hj ⊢
      omega)]
  rw [← sum_pooledMass θ c]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_antidiagonal_replicatePairMass θ c k]
  refine sum_subset (fun j hj => ?_) (fun j hj hj' => ?_)
  · simp only [mem_filter, mem_product, mem_range] at hj
    exact mem_antidiagonal.mpr hj.2
  · simp only [mem_filter, mem_product, mem_range, mem_antidiagonal] at hj hj'
    rw [replicatePairMass]
    have : c < j.1 ∨ c < j.2 := by omega
    rcases this with h | h
    · simp [Nat.choose_eq_zero_of_lt h]
    · simp [Nat.choose_eq_zero_of_lt h]

/-- The **expected law of the AI difference** `ΔAI` of a bin with `c` reads per replicate and
fitted mixture `θ` (Mendelevich et al. 2021, Eqs. (8)–(9)): the law of `|X₁ - X₂| / c` when the
maternal counts `(X₁, X₂)` of the two replicates follow the replicate-pair law
`replicatePairMass θ c`, so that the replicates' AIs are `X₁ / c` and `X₂ / c`. It is a
probability measure (`isProbabilityMeasure_expectedDeltaAILaw`). -/
noncomputable def expectedDeltaAILaw (θ : AIMixture) (c : ℕ) : Measure ℝ :=
  ∑ j ∈ range (c + 1) ×ˢ range (c + 1),
    ENNReal.ofReal (replicatePairMass θ c j.1 j.2) • Measure.dirac (|(j.1 : ℝ) - j.2| / c)

theorem isProbabilityMeasure_expectedDeltaAILaw (θ : AIMixture) (c : ℕ) :
    IsProbabilityMeasure (expectedDeltaAILaw θ c) := by
  constructor
  rw [expectedDeltaAILaw, FunLike.coe_sum, Finset.sum_apply]
  simp only [smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => replicatePairMass_nonneg θ c j.1 j.2),
    sum_replicatePairMass, ENNReal.ofReal_one]

/-! ### The observed AI differences -/

/-- The **allelic imbalance estimate** `AI = M / (M + P)` of a gene with `M` maternal and `P`
paternal reads (Mendelevich et al. 2021, Eq. (2)); it is `0` when the gene has no reads. -/
noncomputable def allelicImbalance (m p : ℕ) : ℝ :=
  m / (m + p : ℕ)

variable {γ ρ : Type*} [Fintype γ]

/-- The **genes of a coverage bin** for the replicates `r` and `r'`, given the maternal and
paternal read counts `mat r g` and `pat r g` of each gene `g` in each replicate `r`: the genes with
reads in both replicates whose mean coverage `(C_{r g} + C_{r' g}) / 2`, with
`C_{r g} = mat r g + pat r g`, lies in the bin `B_i` of base `b` (`InCoverageBin`;
Mendelevich et al. 2021, Eq. (3)). -/
noncomputable def binGenes (b : ℝ) (i : ℕ) (mat pat : ρ → γ → ℕ) (r r' : ρ) : Finset γ :=
  univ.filter fun g => 0 < mat r g + pat r g ∧ 0 < mat r' g + pat r' g ∧
    InCoverageBin b i (((mat r g + pat r g : ℕ) + (mat r' g + pat r' g : ℕ) : ℝ) / 2)

/-- The **observed law of the AI difference** `ΔAI` in the coverage bin `B_i` of base `b` for the
replicates `r` and `r'`: the empirical law, over the genes `g` of the bin (`binGenes`), of
`|AI_{r g} - AI_{r' g}|`, where `AI_{r g} = mat r g / (mat r g + pat r g)` (`allelicImbalance`).
It is a probability measure when the bin has genes
(`isProbabilityMeasure_observedDeltaAILaw`). -/
noncomputable def observedDeltaAILaw (b : ℝ) (i : ℕ) (mat pat : ρ → γ → ℕ) (r r' : ρ) :
    Measure ℝ :=
  ((binGenes b i mat pat r r').card : ℝ≥0∞)⁻¹ •
    ∑ g ∈ binGenes b i mat pat r r',
      Measure.dirac |allelicImbalance (mat r g) (pat r g) - allelicImbalance (mat r' g) (pat r' g)|

theorem isProbabilityMeasure_observedDeltaAILaw {b : ℝ} {i : ℕ} {mat pat : ρ → γ → ℕ} {r r' : ρ}
    (h : (binGenes b i mat pat r r').Nonempty) :
    IsProbabilityMeasure (observedDeltaAILaw b i mat pat r r') := by
  constructor
  rw [observedDeltaAILaw, smul_apply, FunLike.coe_sum, Finset.sum_apply]
  simp only [measure_univ, sum_const, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast h.card_pos.ne') (ENNReal.natCast_ne_top _)

/-! ### The quality correction constant -/

/-- The **least-squares constant fitted to the quantile ratios** (Mendelevich et al. 2021,
"Quantile analysis and QCC value"): given observed and expected quantiles `Qobs i q` and
`Qexp i q` of bins `i ∈ bins` at levels `q ∈ levels`, the mean of the ratios
`Qobs i q / Qexp i q` over the pairs `(i, q)` with `Qexp i q ≠ 0`, where the ratio is defined. It
is the constant `x` that minimizes `∑ (Qobs i q / Qexp i q - x) ^ 2` over those pairs
(`sum_sq_sub_quantileRatioFit`), and `0` when there is no such pair. -/
noncomputable def quantileRatioFit {ι : Type*} (bins : Finset ι) (levels : Finset ℝ)
    (Qobs Qexp : ι → ℝ → ℝ) : ℝ :=
  𝔼 iq ∈ (bins ×ˢ levels).filter (fun iq => Qexp iq.1 iq.2 ≠ 0), Qobs iq.1 iq.2 / Qexp iq.1 iq.2

section quantileRatioFit

variable {ι : Type*} (bins : Finset ι) (levels : Finset ℝ) (Qobs Qexp : ι → ℝ → ℝ)

/-- **The fit is the least-squares constant.** For every constant `x`, the squared error of `x` on
the defined ratios is that of the fit plus `N (fit - x) ^ 2`, where `N` is the number of defined
ratios; so the fit is the unique minimizer when there is a defined ratio. -/
theorem sum_sq_sub_quantileRatioFit (x : ℝ) :
    ∑ iq ∈ (bins ×ˢ levels).filter (fun iq => Qexp iq.1 iq.2 ≠ 0),
        (Qobs iq.1 iq.2 / Qexp iq.1 iq.2 - x) ^ 2 =
      ∑ iq ∈ (bins ×ˢ levels).filter (fun iq => Qexp iq.1 iq.2 ≠ 0),
          (Qobs iq.1 iq.2 / Qexp iq.1 iq.2 - quantileRatioFit bins levels Qobs Qexp) ^ 2 +
        ((bins ×ˢ levels).filter (fun iq => Qexp iq.1 iq.2 ≠ 0)).card *
          (quantileRatioFit bins levels Qobs Qexp - x) ^ 2 := by
  set S := (bins ×ˢ levels).filter (fun iq => Qexp iq.1 iq.2 ≠ 0)
  set f : ι × ℝ → ℝ := fun iq => Qobs iq.1 iq.2 / Qexp iq.1 iq.2
  set m := quantileRatioFit bins levels Qobs Qexp
  have hm : (S.card : ℝ) * m = ∑ iq ∈ S, f iq := by
    by_cases hS : S = ∅
    · simp [hS]
    · have hc : (S.card : ℝ) ≠ 0 := by
        exact_mod_cast (nonempty_iff_ne_empty.mpr hS).card_pos.ne'
      have hm' : m = (∑ iq ∈ S, f iq) / S.card := expect_eq_sum_div_card S f
      rw [hm']
      field_simp
  have hexp : ∀ iq ∈ S, (f iq - x) ^ 2 = (f iq - m) ^ 2 + 2 * (m - x) * (f iq - m) + (m - x) ^ 2 :=
    fun _ _ => by ring
  rw [sum_congr rfl hexp, sum_add_distrib, sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_const,
    nsmul_eq_mul, sum_const, nsmul_eq_mul, ← hm]
  ring

/-- The fit has no larger squared error on the defined ratios than any other constant. -/
theorem sum_sq_sub_quantileRatioFit_le (x : ℝ) :
    ∑ iq ∈ (bins ×ˢ levels).filter (fun iq => Qexp iq.1 iq.2 ≠ 0),
        (Qobs iq.1 iq.2 / Qexp iq.1 iq.2 - quantileRatioFit bins levels Qobs Qexp) ^ 2 ≤
      ∑ iq ∈ (bins ×ˢ levels).filter (fun iq => Qexp iq.1 iq.2 ≠ 0),
        (Qobs iq.1 iq.2 / Qexp iq.1 iq.2 - x) ^ 2 := by
  rw [sum_sq_sub_quantileRatioFit bins levels Qobs Qexp x]
  have := sq_nonneg (quantileRatioFit bins levels Qobs Qexp - x)
  have := (Nat.cast_nonneg ((bins ×ˢ levels).filter (fun iq => Qexp iq.1 iq.2 ≠ 0)).card :
    (0 : ℝ) ≤ _)
  nlinarith

/-- If every defined observed quantile is `κ` times the expected one, and some ratio is defined,
the fit is `κ`. In particular it is `1` when the observed quantiles are the expected ones. -/
theorem quantileRatioFit_eq_of_forall {κ : ℝ}
    (hS : ((bins ×ˢ levels).filter (fun iq => Qexp iq.1 iq.2 ≠ 0)).Nonempty)
    (h : ∀ i ∈ bins, ∀ q ∈ levels, Qexp i q ≠ 0 → Qobs i q = κ * Qexp i q) :
    quantileRatioFit bins levels Qobs Qexp = κ := by
  unfold quantileRatioFit
  rw [expect_congr rfl (g := fun _ => κ) fun iq hiq => ?_, expect_const hS]
  simp only [mem_filter, mem_product] at hiq
  rw [h iq.1 hiq.1.1 iq.2 hiq.1.2 hiq.2, mul_div_cancel_right₀ _ hiq.2]

end quantileRatioFit

/-- The **quality correction constant of two replicates** `r` and `r'` (Mendelevich et al. 2021,
"Calculation of quality correction constant for 2 replicates" to "Quantile analysis and QCC
value"). The data are the maternal and paternal read counts `mat r g` and `pat r g` of each gene
`g` in each replicate `r`; `b` is the base of the coverage bins, `bins` the bins used, `levels`
the quantile levels (the source's are `0.2, 0.35, 0.5, 0.65, 0.8, 0.9, 0.95`), and `fit i` the
two-component symmetric beta-binomial mixture fitted to the pooled AI of the genes of bin `i`
(the output of the source's EM algorithm). The QCC is the least-squares constant
(`quantileRatioFit`) fitted to the ratios `Q^obs_{q,i} / Q^exp_{q,i}`, over the bins of `bins`
that have genes and the levels `q` with `Q^exp_{q,i} ≠ 0`, of

* the observed quantile `Q^obs_{q,i}`: the lower `q`-quantile (`cdfQuantile`) of the empirical
  law of `ΔAI = |AI_{r g} - AI_{r' g}|` over the genes of bin `i` (`observedDeltaAILaw`), to
* the expected quantile `Q^exp_{q,i}`: the lower `q`-quantile of the law of `ΔAI` when two
  replicates of `c_i = ⌈Ĉ_i⌉` reads (`binReadCoverage`) are drawn from the fitted mixture with
  pure binomial sampling of reads (`expectedDeltaAILaw`).

A QCC of `1` means the replicates agree as well as binomial sampling of reads predicts. -/
noncomputable def pairQualityCorrectionConstant (b : ℝ) (bins : Finset ℕ) (levels : Finset ℝ)
    (fit : ℕ → AIMixture) (mat pat : ρ → γ → ℕ) (r r' : ρ) : ℝ :=
  quantileRatioFit (bins.filter fun i => (binGenes b i mat pat r r').Nonempty) levels
    (fun i q => cdfQuantile (observedDeltaAILaw b i mat pat r r') q)
    (fun i q => cdfQuantile (expectedDeltaAILaw (fit i) (binReadCoverage b i)) q)

/-- The pairs `r < r'` of replicates among `0, …, M - 1`; there are `C(M, 2)` of them
(`card_replicatePairs`). -/
def replicatePairs (M : ℕ) : Finset (Fin M × Fin M) :=
  univ.filter fun rr => rr.1 < rr.2

/-- There are `C(M, 2)` pairs of replicates. -/
theorem card_replicatePairs (M : ℕ) : (replicatePairs M).card = M.choose 2 := by
  set T := univ.filter fun rr : Fin M × Fin M => rr.2 < rr.1
  have hswap : T.card = (replicatePairs M).card :=
    card_nbij' Prod.swap Prod.swap (fun rr h => by simpa [T, replicatePairs] using h)
      (fun rr h => by simpa [T, replicatePairs] using h) (fun rr _ => rr.swap_swap)
      (fun rr _ => rr.swap_swap)
  have hoff : (univ : Finset (Fin M)).offDiag = replicatePairs M ∪ T := by
    ext rr
    simp only [mem_offDiag, mem_univ, true_and, mem_union, replicatePairs, T, mem_filter]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt ne_of_gt⟩
  have hdisj : Disjoint (replicatePairs M) T := by
    rw [disjoint_left]
    intro rr h h'
    simp only [replicatePairs, T, mem_filter] at h h'
    exact lt_asymm h.2 h'.2
  have hcard := congrArg card hoff
  rw [offDiag_card, card_union_of_disjoint hdisj, hswap, card_univ, Fintype.card_fin,
    show M * M - M = M * (M - 1) by rw [Nat.mul_sub, mul_one]] at hcard
  rw [Nat.choose_two_right, hcard]
  omega

/-- The **quality correction constant** (QCC) of `M` replicates `0, …, M - 1` (Mendelevich et al.
2021, Methods, Eqs. (3)–(10)): the mean, over the `C(M, 2)` pairs of replicates `r < r'`
(`replicatePairs`), of the pairwise constants `pairQualityCorrectionConstant` of `r` and `r'`,
each with the mixtures `fit r r' i` fitted to the pooled AI of the pair's genes in bin `i`. The
data are the maternal and paternal read counts `mat r g` and `pat r g` of each gene `g` in each
replicate `r`, `b` is the base of the coverage bins, `bins` the bins used and `levels` the
quantile levels. With two replicates it is the QCC of the one pair
(`qualityCorrectionConstant_two`). Confidence intervals for the AI of a gene of coverage `C` then
treat it as a binomial proportion of effective coverage `C / QCC ^ 2` (`effectiveCoverage`). -/
noncomputable def qualityCorrectionConstant {M : ℕ} (b : ℝ) (bins : Finset ℕ) (levels : Finset ℝ)
    (fit : Fin M → Fin M → ℕ → AIMixture) (mat pat : Fin M → γ → ℕ) : ℝ :=
  𝔼 rr ∈ replicatePairs M, pairQualityCorrectionConstant b bins levels (fit rr.1 rr.2) mat pat
    rr.1 rr.2

/-- With two replicates, the QCC is the QCC of the one pair. -/
theorem qualityCorrectionConstant_two (b : ℝ) (bins : Finset ℕ) (levels : Finset ℝ)
    (fit : Fin 2 → Fin 2 → ℕ → AIMixture) (mat pat : Fin 2 → γ → ℕ) :
    qualityCorrectionConstant b bins levels fit mat pat =
      pairQualityCorrectionConstant b bins levels (fit 0 1) mat pat 0 1 := by
  have : replicatePairs 2 = {(0, 1)} := by decide
  rw [qualityCorrectionConstant, this, expect_singleton]

/-! ### Corrected confidence intervals -/

/-- The **effective coverage** `C / QCC ^ 2` of a gene of coverage `C` after quality correction
(Mendelevich et al. 2021, Eq. (11)): confidence intervals treat the gene's AI as a binomial
proportion with this many trials, so that its standard deviation is `QCC` times the uncorrected
one (`sqrt_div_effectiveCoverage`). -/
noncomputable def effectiveCoverage (C : ℕ) (qcc : ℝ) : ℝ :=
  C / qcc ^ 2

@[simp]
theorem effectiveCoverage_one (C : ℕ) : effectiveCoverage C 1 = C := by
  simp [effectiveCoverage]

/-- Deflating the coverage to `C / QCC ^ 2` multiplies the standard deviation
`√(a (1 - a) / C)` of a binomial proportion `a` by `QCC`. -/
theorem sqrt_div_effectiveCoverage (C : ℕ) {qcc : ℝ} (hq : 0 ≤ qcc) (a : ℝ) :
    √(a * (1 - a) / effectiveCoverage C qcc) = qcc * √(a * (1 - a) / C) := by
  unfold effectiveCoverage
  rw [div_div_eq_mul_div, mul_comm _ (qcc ^ 2), mul_div_assoc, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq hq]

end Domains.Biology.Omics.AllelicImbalance
