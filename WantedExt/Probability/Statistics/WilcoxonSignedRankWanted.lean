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

@[expose] public section

namespace WantedExt.Probability.Statistics.WilcoxonSignedRankWanted

open MeasureTheory ProbabilityTheory

/-- The rank of `|x_i|` among `|x_1|, …, |x_n|`: the number of `j` with `|x_j| ≤ |x_i|`. -/
noncomputable def absRank {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => |x j| ≤ |x i|).card

/-- The signed-rank statistic `W⁺`, the sum of the ranks of `|x_i|` over the positive `x_i`. -/
noncomputable def signedRankStatistic {n : ℕ} (x : Fin n → ℝ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => 0 < x i), absRank x i

/-- The number `c_n(t)` of subsets of `{1, …, n}` with sum `t`. -/
def subsetSumCount (n t : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter
    fun S : Finset (Fin n) => (∑ j ∈ S, ((j : ℕ) + 1)) = t).card

/-- **Exact null law of the signed-rank statistic** (Wilcoxon 1945). Let `μ` be a probability
measure and `D_1, …, D_n : Ω → ℝ` independent measurable random variables, each with a law that
has no atoms and is symmetric about `0` (the law of `D_i` equals the law of `-D_i`). Then for
every `t`, `P(W⁺ = t) = c_n(t) / 2ⁿ`.

Sources: Wilcoxon (1945), with the continuous symmetric null as a generalization of its normal
null. -/
public theorem_wanted measureReal_signedRankStatistic_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (D : Fin n → Ω → ℝ)
    (hD : ∀ i, Measurable (D i)) (hind : iIndepFun D μ) (hcont : ∀ i, NoAtoms (μ.map (D i)))
    (hsymm : ∀ i, μ.map (D i) = μ.map (fun ω => -D i ω)) (t : ℕ) :
    μ.real {ω | signedRankStatistic (fun i => D i ω) = t} = subsetSumCount n t / (2 : ℝ) ^ n

/-- **Wilcoxon's normal null** (Wilcoxon 1945). Let `μ` be a probability measure, `σ² > 0`, and
`D_1, …, D_n : Ω → ℝ` independent measurable random variables, each Gaussian with mean `0` and
variance `σ²`. Then for every `t`, `P(W⁺ = t) = c_n(t) / 2ⁿ`.

Sources: Wilcoxon (1945). -/
public theorem_wanted measureReal_signedRankStatistic_eq_of_gaussian {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (D : Fin n → Ω → ℝ)
    (hD : ∀ i, Measurable (D i)) (hind : iIndepFun D μ) (σsq : NNReal) (hσ : 0 < σsq)
    (hlaw : ∀ i, μ.map (D i) = gaussianReal 0 σsq) (t : ℕ) :
    μ.real {ω | signedRankStatistic (fun i => D i ω) = t} = subsetSumCount n t / (2 : ℝ) ^ n

/-- **Moments and symmetry of the null law** (Wilcoxon 1945; derived). For every `n`, the law
`t ↦ c_n(t) / 2ⁿ` of `∑_{j = 1}^n j B_j` has mean `n(n + 1)/4`, variance `n(n + 1)(2n + 1)/24`,
and is symmetric about its mean: `c_n(t) = c_n(n(n + 1)/2 - t)` for `t ≤ n(n + 1)/2`. Means and
variances are taken over the subsets `S` of `{1, …, n}`, each with probability `1 / 2ⁿ`.

Sources: Wilcoxon (1945); derived. -/
public theorem_wanted subsetSum_moments_symm (n : ℕ) :
    (∑ S : Finset (Fin n), ((∑ j ∈ S, ((j : ℕ) + 1) : ℕ) : ℝ)) / (2 : ℝ) ^ n = n * (n + 1) / 4 ∧
      (∑ S : Finset (Fin n), (((∑ j ∈ S, ((j : ℕ) + 1) : ℕ) : ℝ) - n * (n + 1) / 4) ^ 2) /
          (2 : ℝ) ^ n = n * (n + 1) * (2 * n + 1) / 24 ∧
      ∀ t, t ≤ n * (n + 1) / 2 → subsetSumCount n t = subsetSumCount n (n * (n + 1) / 2 - t)

/-- **Wilcoxon's worked cases** (Wilcoxon 1945). For `15` pairs, `∑_{t ≤ 24} c_15(t) = 676`, so
`P(W⁺ ≤ 24) = 676 / 32768 ≈ 0.0206`, inside the source's range `[0.019, 0.054]`; for `8` pairs,
`∑_{t ≤ 3} c_8(t) = 5`, so `P(W⁺ ≤ 3) = 5 / 256`.

Sources: Wilcoxon (1945), Table II and the worked examples. -/
public theorem_wanted subsetSumCount_examples :
    ∑ t ∈ Finset.range 25, subsetSumCount 15 t = 676 ∧
      ∑ t ∈ Finset.range 4, subsetSumCount 8 t = 5

end WantedExt.Probability.Statistics.WilcoxonSignedRankWanted
