/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Segregation ratio under complete ascertainment: the Li–Mantel estimator

Sibships of size `s` are ascertained through at least one affected child (complete
ascertainment), and each child is affected independently with probability `p` (the segregation
ratio). The number of affected children in an ascertained sibship then follows the zero-truncated
binomial law `P(k) = C(s, k) pᵏ (1 - p)^(s - k) / (1 - (1 - p)ˢ)` for `1 ≤ k ≤ s`, whose mean is
`s p / (1 - (1 - p)ˢ)` (Fisher 1934). Li and Mantel (1968) proposed the estimator
`(R - J) / (T - J)` of `p`, where over the first `n` ascertained sibships `R` counts affected
children, `T` counts all children and `J` counts sibships with exactly one affected child; it is
consistent for `p`.

Recorded here: the zero-truncated binomial law and its mean (the law itself is defined in
`Domains.Biology.StatisticalGenetics.LiMantelSegregationLiMantelTendstoAe`). The almost-sure
consistency of the Li–Mantel estimator for independent ascertained sibships of a common size
`s ≥ 2` (for `s = 1` the denominator `T - J` vanishes identically) is proved in
`Domains.Biology.StatisticalGenetics.LiMantelSegregationLiMantelTendstoAe`, where the estimator
and its counts are defined. The statements are derived from the model
as stated; the scanned primary text was not available locally, so section and equation numbers
of Li and Mantel (1968) are not cited. Variable sibship sizes and the variance of the estimator
are not formalized.

Sources: C. C. Li and N. Mantel, "A simple method of estimating the segregation ratio under
complete ascertainment", Am. J. Hum. Genet. 20 (1968) 61–81; R. A. Fisher, "The effect of
methods of ascertainment upon the estimation of frequencies", Ann. Eugen. 6 (1934) 13–25.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Instances.Real.Lemmas
public import Domains.Biology.StatisticalGenetics.LiMantelSegregationLiMantelTendstoAe

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.LiMantelSegregationWanted

open MeasureTheory ProbabilityTheory Filter Topology Finset

/-- **The zero-truncated binomial law and its mean** (Fisher 1934): for `s ≥ 1` and
`0 < p < 1`, the truncated probabilities are nonnegative, sum to `1` over `k ∈ {0, …, s}`, and
have mean `s p / (1 - (1 - p)ˢ)`.

Sources: Fisher (1934); Li and Mantel (1968). -/
public theorem_wanted truncBinom_law_mean (s : ℕ) (hs : 1 ≤ s) (p : ℝ) (hp₀ : 0 < p)
    (hp₁ : p < 1) :
    (∀ k, 0 ≤ truncBinom s p k) ∧
      ∑ k ∈ range (s + 1), truncBinom s p k = 1 ∧
      ∑ k ∈ range (s + 1), (k : ℝ) * truncBinom s p k = s * p / (1 - (1 - p) ^ s)

end WantedExt.Biology.StatisticalGenetics.LiMantelSegregationWanted
