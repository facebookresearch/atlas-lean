/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Kruskal–Wallis test: exact null moments, distribution-freeness and the chi-square limit

`C` samples of sizes `n_i ≥ 1`, `N = ∑ n_i`, are pooled and ranked `1, …, N`. With `R_i` the rank
sum of sample `i`, the Kruskal–Wallis statistic is
`H = 12 / (N (N + 1)) ∑ R_i² / n_i - 3 (N + 1) = 12 / (N (N + 1)) ∑ n_i (R_i / n_i - (N + 1)/2)²`.
Under the null hypothesis the rank vector is uniformly distributed over the `N!` permutations of
`(1, …, N)`. Then `E H = C - 1`,
`Var H = 2 (C - 1) - 2 (3C² - 6C + N (2C² - 6C + 1)) / (5 N (N + 1)) - (6/5) ∑ 1 / n_i`, and
`0 ≤ H ≤ (N³ - ∑ n_i³) / (N (N + 1))`, the maximum being attained when every sample occupies
consecutive ranks. For two samples `H = 12 (R_1 - n_1 (N + 1)/2)² / ((N + 1) n_1 (N - n_1))`. For
independent observations with a common continuous law the null law of `H` does not depend on
that law, and if `n_i / N → ν_i > 0` for every `i`, `H` converges in distribution to the
chi-square law with `C - 1` degrees of freedom.

Here the samples are given by an assignment `g` of the `N` positions to the `C` samples, and the
ranks by a permutation `σ` of the positions (`σ k + 1` is the rank at position `k`).

Sources: W. H. Kruskal and W. A. Wallis, "Use of ranks in one-criterion variance analysis",
J. Amer. Statist. Assoc. 47 (1952) 583–621; W. H. Kruskal, "A nonparametric test for the several
sample problem", Ann. Math. Statist. 23 (1952) 525–540, Sections 3, 4, 6 and 7.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import MathlibExt.Probability.Distributions.ChiSquare
public import MathlibExt.Probability.Statistics.KruskalWallis
public import MathlibExt.Probability.Statistics.Measurement.Scales

@[expose] public section

namespace WantedExt.Probability.Statistics.KruskalWallisWanted

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.Statistics.Measurement (sampleRank)

variable {C N : ℕ}

/-- **Average over rankings.** The average of `f` over all `N!` rankings (the null
distribution). -/
noncomputable def permAverage (f : Equiv.Perm (Fin N) → ℝ) : ℝ :=
  (∑ σ, f σ) / (N.factorial : ℝ)

/-- **Null moments of the rank sums.**
For an assignment `g` of `N ≥ 2` positions to `C` samples of sizes `n_i ≥ 1`, under the uniform
law on rankings, `E R_i = n_i (N + 1)/2`, `Var R_i = n_i (N - n_i)(N + 1)/12`, and for `i ≠ j`,
`Cov(R_i, R_j) = -n_i n_j (N + 1)/12`.

Sources: W. H. Kruskal and W. A. Wallis, "Use of ranks in one-criterion variance analysis", J. Amer.
Statist. Assoc. 47 (1952) 583–621, Section 3; W. H. Kruskal, "A nonparametric test for the several
sample problem", Ann. Math. Statist. 23 (1952) 525–540, p. 527. -/
public theorem_wanted rankSum_moments (g : Fin N → Fin C) (hN : 2 ≤ N)
    (hn : ∀ i, 0 < sampleSize g i) :
    (∀ i, permAverage (fun σ => (rankSum g σ i : ℝ)) = sampleSize g i * (N + 1) / 2) ∧
      (∀ i, permAverage (fun σ => ((rankSum g σ i : ℝ) - sampleSize g i * (N + 1) / 2) ^ 2) =
        sampleSize g i * (N - sampleSize g i) * (N + 1) / 12) ∧
      ∀ i j, i ≠ j → permAverage (fun σ =>
          ((rankSum g σ i : ℝ) - sampleSize g i * (N + 1) / 2) *
            ((rankSum g σ j : ℝ) - sampleSize g j * (N + 1) / 2)) =
        -(sampleSize g i * sampleSize g j * (N + 1) / 12)

/-- **Null mean and variance of `H`.** For an assignment `g` of
`N ≥ 2` positions to `C` samples of sizes `n_i ≥ 1`, under the uniform law on rankings,
`E H = C - 1` and
`Var H = 2 (C - 1) - 2 (3C² - 6C + N (2C² - 6C + 1)) / (5 N (N + 1)) - (6/5) ∑_i 1 / n_i`.

Sources: W. H. Kruskal, "A nonparametric test for the several sample problem", Ann. Math. Statist.
23 (1952) 525–540, p. 526 and p. 535, equations (6.2)–(6.5). -/
public theorem_wanted kruskalWallis_mean_variance (g : Fin N → Fin C) (hN : 2 ≤ N)
    (hn : ∀ i, 0 < sampleSize g i) :
    permAverage (kruskalWallis g) = C - 1 ∧
      permAverage (fun σ => (kruskalWallis g σ - (C - 1)) ^ 2) =
        2 * (C - 1) - 2 * (3 * C ^ 2 - 6 * C + N * (2 * C ^ 2 - 6 * C + 1)) / (5 * N * (N + 1)) -
          6 / 5 * ∑ i, 1 / (sampleSize g i : ℝ)

/-- **Range of `H`.** For an assignment `g` of `N ≥ 1`
positions to `C` samples of sizes `n_i ≥ 1` and every ranking `σ`,
`0 ≤ H ≤ (N³ - ∑ n_i³) / (N (N + 1))`, and some ranking attains the upper bound.

Sources: W. H. Kruskal, "A nonparametric test for the several sample problem", Ann. Math. Statist.
23 (1952) 525–540, p. 535, equations (7.1)–(7.2); the lower bound is derived. -/
public theorem_wanted kruskalWallis_bounds (g : Fin N → Fin C) (hN : 0 < N)
    (hn : ∀ i, 0 < sampleSize g i) :
    (∀ σ, 0 ≤ kruskalWallis g σ ∧
      kruskalWallis g σ ≤ ((N : ℝ) ^ 3 - ∑ i, (sampleSize g i : ℝ) ^ 3) / (N * (N + 1))) ∧
      ∃ σ, kruskalWallis g σ = ((N : ℝ) ^ 3 - ∑ i, (sampleSize g i : ℝ) ^ 3) / (N * (N + 1))

/-- **Distribution-freeness.** Let `μ`
be a probability measure, `X_1, …, X_N : Ω → ℝ` independent measurable random variables with a
common law (`X_k` and `X_l` have the same law for all `k, l`) that has no atoms, and `g` an
assignment of the `N` positions to `C` samples. For every real `h`, the probability that the
ranks `sampleRank (fun j => X_j) k = 1 + #{j | X_j < X_k}` are `σ k + 1` for a permutation `σ` of
`Fin N` whose Kruskal–Wallis statistic is
`h` equals the number of permutations `σ` with `H(σ) = h`, divided by `N!`. (The ranks form a
permutation almost surely, so this is the law of `H` of the sample ranks.)

Sources: W. H. Kruskal and W. A. Wallis, "Use of ranks in one-criterion variance analysis", J. Amer.
Statist. Assoc. 47 (1952) 583–621, Section 1; W. H. Kruskal, "A nonparametric test for the several
sample problem", Ann. Math. Statist. 23 (1952) 525–540, p. 525. -/
public theorem_wanted kruskalWallis_distributionFree {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin N → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hid : ∀ k l, μ.map (X k) = μ.map (X l))
    (hcont : ∀ k, NoAtoms (μ.map (X k))) (g : Fin N → Fin C) (h : ℝ) :
    μ.real {ω | ∃ σ : Equiv.Perm (Fin N), (∀ k, (σ k : ℕ) + 1 = sampleRank (fun j => X j ω) k) ∧
        kruskalWallis g σ = h} =
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => kruskalWallis g σ = h).card : ℝ) /
        N.factorial

/-- **The chi-square limit.** Let `C ≥ 2`, and for each `m` let `g m` be
an assignment of `N_m` positions to `C` samples of sizes `n_i(m)`, with `N_m → ∞` and
`n_i(m) / N_m → ν_i > 0` for every `i`. Then under the uniform law on rankings, the Kruskal–Wallis
statistic converges in distribution to the chi-square law with `C - 1` degrees of freedom: for
every bounded continuous `f : ℝ → ℝ`, the null mean of `f(H)` tends to `∫ f dχ²_{C-1}`.

Sources: W. H. Kruskal, "A nonparametric test for the several sample problem", Ann. Math. Statist.
23 (1952) 525–540, pp. 527–528, Section 4 (via the Wald–Wolfowitz permutation central limit
theorem). -/
public theorem_wanted tendsto_kruskalWallis_chiSquare (hC : 2 ≤ C) (Nm : ℕ → ℕ)
    (g : (m : ℕ) → Fin (Nm m) → Fin C) (ν : Fin C → ℝ) (hν : ∀ i, 0 < ν i)
    (hNm : Tendsto Nm atTop atTop)
    (hfrac : ∀ i, Tendsto (fun m => (sampleSize (g m) i : ℝ) / Nm m) atTop (𝓝 (ν i)))
    (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun m => permAverage (fun σ => f (kruskalWallis (g m) σ))) atTop
      (𝓝 (∫ x, f x ∂(chiSquareMeasure (C - 1))))

end WantedExt.Probability.Statistics.KruskalWallisWanted
