/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Wilcoxon signed-rank test: exact null law and moments

For paired differences `D_1, …, D_n`, rank the absolute values `|D_i|` from `1` to `n` and let
`W⁺` be the sum of the ranks of the positive differences. Wilcoxon's null hypothesis is that the
differences are normally distributed about zero. More generally, if the differences are
independent, each with a continuous law symmetric about `0`, then the signs are independent fair
coins independent of the absolute values, so `W⁺` has the law of `∑_{j = 1}^n j B_j` for
independent fair Bernoulli `B_j`: `P(W⁺ = t) = c_n(t) / 2ⁿ`, where `c_n(t)` is the number of subsets
of `{1, …, n}` with sum `t` (partitions of `t` into distinct parts at most `n`). The law does not
depend on the distribution of the differences, has mean `n(n + 1)/4` and variance
`n(n + 1)(2n + 1)/24`, and is symmetric about its mean. For `15` pairs,
`P(W⁺ ≤ 24) = 676 / 32768`, in Wilcoxon's tabulated range `[0.019, 0.054]`.

The continuous symmetric null generalizes Wilcoxon's normal null; ties and the unpaired test are
not treated.

Sources: F. Wilcoxon, "Individual comparisons by ranking methods", Biometrics Bull. 1 (1945)
80–83.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import MathlibExt.Probability.Statistics.Measurement.Scales
public import MathlibExt.Probability.Statistics.WilcoxonSignedRank

@[expose] public section

namespace WantedExt.Probability.Statistics.WilcoxonSignedRankWanted

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.Measurement (sampleRank)

/-- **Signed-rank statistic.** The statistic `W⁺`, the sum over the positive `x_i` of the rank
`sampleRank (fun j => |x j|) i = 1 + #{j | |x_j| < |x_i|}` of `|x_i|`. -/
noncomputable def signedRankStatistic {n : ℕ} (x : Fin n → ℝ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => 0 < x i), sampleRank (fun j => |x j|) i

/-- **Exact null law of the signed-rank statistic.** Let `μ` be a probability
measure and `D_1, …, D_n : Ω → ℝ` independent measurable random variables, each with a law that
has no atoms and is symmetric about `0` (the law of `D_i` equals the law of `-D_i`). Then for
every `t`, `P(W⁺ = t) = c_n(t) / 2ⁿ`.

Sources: F. Wilcoxon, "Individual comparisons by ranking methods", Biometrics Bull. 1 (1945) 80–83;
the continuous symmetric null generalizes its normal null. -/
public theorem_wanted measureReal_signedRankStatistic_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (D : Fin n → Ω → ℝ)
    (hD : ∀ i, Measurable (D i)) (hind : iIndepFun D μ) (hcont : ∀ i, NoAtoms (μ.map (D i)))
    (hsymm : ∀ i, μ.map (D i) = μ.map (fun ω => -D i ω)) (t : ℕ) :
    μ.real {ω | signedRankStatistic (fun i => D i ω) = t} = subsetSumCount n t / (2 : ℝ) ^ n

/-- **Wilcoxon's normal null.** Let `μ` be a probability measure, `σ² > 0`, and
`D_1, …, D_n : Ω → ℝ` independent measurable random variables, each Gaussian with mean `0` and
variance `σ²`. Then for every `t`, `P(W⁺ = t) = c_n(t) / 2ⁿ`.

Sources: F. Wilcoxon, "Individual comparisons by ranking methods", Biometrics Bull. 1 (1945) 80–83.
-/
public theorem_wanted measureReal_signedRankStatistic_eq_of_gaussian {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (D : Fin n → Ω → ℝ)
    (hD : ∀ i, Measurable (D i)) (hind : iIndepFun D μ) (σsq : NNReal) (hσ : 0 < σsq)
    (hlaw : ∀ i, μ.map (D i) = gaussianReal 0 σsq) (t : ℕ) :
    μ.real {ω | signedRankStatistic (fun i => D i ω) = t} = subsetSumCount n t / (2 : ℝ) ^ n

/-- **Moments and symmetry of the null law.** For every `n`, the law
`t ↦ c_n(t) / 2ⁿ` of `∑_{j = 1}^n j B_j` has mean `n(n + 1)/4`, variance `n(n + 1)(2n + 1)/24`,
and is symmetric about its mean: `c_n(t) = c_n(n(n + 1)/2 - t)` for `t ≤ n(n + 1)/2`. Means and
variances are taken over the subsets `S` of `{1, …, n}`, each with probability `1 / 2ⁿ`.

Sources: F. Wilcoxon, "Individual comparisons by ranking methods", Biometrics Bull. 1 (1945) 80–83;
the moments are derived. -/
public theorem_wanted subsetSum_moments_symm (n : ℕ) :
    (∑ S : Finset (Fin n), ((∑ j ∈ S, ((j : ℕ) + 1) : ℕ) : ℝ)) / (2 : ℝ) ^ n = n * (n + 1) / 4 ∧
      (∑ S : Finset (Fin n), (((∑ j ∈ S, ((j : ℕ) + 1) : ℕ) : ℝ) - n * (n + 1) / 4) ^ 2) /
          (2 : ℝ) ^ n = n * (n + 1) * (2 * n + 1) / 24 ∧
      ∀ t, t ≤ n * (n + 1) / 2 → subsetSumCount n t = subsetSumCount n (n * (n + 1) / 2 - t)

end WantedExt.Probability.Statistics.WilcoxonSignedRankWanted
