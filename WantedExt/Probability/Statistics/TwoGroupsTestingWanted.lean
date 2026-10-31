/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Statistics.MetaAnalysis
public import MathlibExt.Probability.Statistics.MultipleTesting.PermutationPValue
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.UniformOn

/-!
# Wanted: Cochran's Q and Monte Carlo permutation p-values

Two classical results that complete the proved files
`MathlibExt/Probability/Statistics/MetaAnalysis.lean` and
`MathlibExt/Probability/Statistics/MultipleTesting/PermutationPValue.lean`.

* `hasLaw_cochranQ`: for `k ≥ 2` independent estimates `Xᵢ ~ N(θ, vᵢ)` of a common `θ` with
  known variances `vᵢ > 0`, Cochran's heterogeneity statistic
  `Q = ∑ vᵢ⁻¹ (Xᵢ - X̄)²`, with `X̄` the inverse-variance-weighted mean, is chi-square with
  `k - 1` degrees of freedom (Cochran 1954). The proof needs Cochran's theorem on Gaussian
  quadratic forms, which is not yet available.
* `isValidPValue_monteCarloPermutationPValue`: with `B` group elements drawn independently and
  uniformly from a finite group `G` that leaves the null law invariant, the Monte Carlo
  permutation p-value `(1 + #{b | T(g_b • ω) ≥ T(ω)}) / (B + 1)` is valid (Phipson and Smyth
  2010; Hemerik and Goeman 2018).

## References

* W. G. Cochran, *The combination of estimates from different experiments*, Biometrics 10
  (1954), 101–129.
* B. Phipson and G. K. Smyth, *Permutation p-values should never be zero*, Stat. Appl. Genet.
  Mol. Biol. 9 (2010), Article 39.
* J. Hemerik and J. Goeman, *Exact testing with random permutations*, TEST 27 (2018),
  811–825.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.TwoGroupsTestingWanted

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.MetaAnalysis
open MathlibExt.Probability.Statistics.MultipleTesting

open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cochran (1954): for `k ≥ 2` independent Gaussian estimates `Xᵢ ~ N(θ, vᵢ)` with positive
known variances, `Q = ∑ vᵢ⁻¹ (Xᵢ - ∑ⱼ wⱼ Xⱼ)²` with inverse-variance weights `w` has the
chi-square law with `k - 1` degrees of freedom. -/
theorem_wanted hasLaw_cochranQ {k : ℕ} (hk : 2 ≤ k) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ : ℝ} {v : Fin k → ℝ≥0} (hv : ∀ i, v i ≠ 0) {X : Fin k → Ω → ℝ}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal θ (v i)) μ) (hind : iIndepFun X μ) :
    HasLaw (fun ω => ∑ i, ((v i : ℝ))⁻¹ *
        (X i ω - ∑ j, inverseVarianceWeights (fun j => (v j : ℝ)) j * X j ω) ^ 2)
      (chiSquareMeasure (k - 1)) μ

/-- Phipson and Smyth (2010); Hemerik and Goeman (2018): if the null law `μ` is invariant under
a finite group `G` and `g₁, …, g_B` are drawn independently and uniformly from `G`,
independently of the data, then `(1 + #{b | T(g_b • ω) ≥ T(ω)}) / (B + 1)` is a valid p-value
under the joint law. -/
theorem_wanted isValidPValue_monteCarloPermutationPValue {G : Type*} [Group G] [Fintype G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G] [MulAction G Ω] (B : ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [SMulInvariantMeasure G Ω μ]
    (hsmul : ∀ g : G, Measurable fun ω : Ω => g • ω) {T : Ω → ℝ} (hT : Measurable T) :
    IsValidPValue (μ.prod (Measure.pi fun _ : Fin B => uniformOn (Set.univ : Set G)))
      (fun x => (1 + ((Finset.univ.filter fun b => T x.1 ≤ T (x.2 b • x.1)).card : ℝ)) /
        (B + 1))

end MathlibExt.Probability.Statistics.TwoGroupsTestingWanted
