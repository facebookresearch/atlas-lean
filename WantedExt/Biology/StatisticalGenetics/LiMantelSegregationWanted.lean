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

Recorded here: the zero-truncated binomial law and its mean, and the almost-sure consistency of
the Li–Mantel estimator for independent ascertained sibships of a common size `s ≥ 2` (for
`s = 1` the denominator `T - J` vanishes identically). The statements are derived from the model
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

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.LiMantelSegregationWanted

open MeasureTheory ProbabilityTheory Filter Topology Finset

/-- The **zero-truncated binomial law**: the probability that an ascertained sibship of size `s`
has exactly `k` affected children, when each child is affected independently with probability
`p` and the sibship is ascertained if and only if `k ≥ 1`. It vanishes for `k = 0` and `k > s`.
For `1 ≤ k ≤ s` it is `C(s, k) p^k (1 - p)^(s - k) / (1 - (1 - p)^s)`. The intended domain is
`s ≥ 1` and `0 < p < 1`, where the denominator `1 - (1 - p)^s` is positive. Outside it the
denominator can vanish (e.g. `p = 0`), and then the value is `0`, since Lean's division is total
(`x / 0 = 0`). -/
noncomputable def truncBinom (s : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  if 1 ≤ k ∧ k ≤ s then
    (s.choose k : ℝ) * p ^ k * (1 - p) ^ (s - k) / (1 - (1 - p) ^ s)
  else 0

/-- Number `R` of affected children in the first `n` sibships, given the affected counts `x`. -/
def affectedCount (x : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, x i

/-- Number `J` of sibships with exactly one affected child among the first `n`. -/
def singletonCount (x : ℕ → ℕ) (n : ℕ) : ℕ := #{i ∈ range n | x i = 1}

/-- The **Li–Mantel estimator** `(R - J) / (T - J)` of the segregation ratio from the first `n`
ascertained sibships of size `s`, where `T = n s` is the number of children. Since `J ≤ n`, the
denominator satisfies `T - J ≥ n (s - 1) > 0` whenever `n ≥ 1` and `s ≥ 2`, the intended domain.
Otherwise it can vanish (for `n = 0`, or for `s = 1`, where every sibship is a singleton), and
then the value is `0` because Lean's division is total (`x / 0 = 0`). -/
noncomputable def liMantel (s : ℕ) (x : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((affectedCount x n : ℝ) - singletonCount x n) / ((n * s : ℕ) - (singletonCount x n : ℝ))

/-- **The zero-truncated binomial law and its mean** (Fisher 1934): for `s ≥ 1` and
`0 < p < 1`, the truncated probabilities are nonnegative, sum to `1` over `k ∈ {0, …, s}`, and
have mean `s p / (1 - (1 - p)ˢ)`.

Sources: Fisher (1934); Li and Mantel (1968). -/
public theorem_wanted truncBinom_law_mean (s : ℕ) (hs : 1 ≤ s) (p : ℝ) (hp₀ : 0 < p)
    (hp₁ : p < 1) :
    (∀ k, 0 ≤ truncBinom s p k) ∧
      ∑ k ∈ range (s + 1), truncBinom s p k = 1 ∧
      ∑ k ∈ range (s + 1), (k : ℝ) * truncBinom s p k = s * p / (1 - (1 - p) ^ s)

/-- **Consistency of the Li–Mantel estimator** (Li and Mantel 1968): let the affected counts
`X i` of ascertained sibships of a common size `s ≥ 2` be independent random variables, each with
the zero-truncated binomial law for a segregation ratio `0 < p < 1`. Then, almost surely, the
estimator `(R - J) / (T - J)` computed from the first `n` sibships converges to `p` as
`n → ∞`.

Source: Li and Mantel (1968). -/
public theorem_wanted liMantel_tendsto_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : ℕ) (hs : 2 ≤ s) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (X : ℕ → Ω → ℕ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hlaw : ∀ i k, μ.real (X i ⁻¹' {k}) = truncBinom s p k) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => liMantel s (fun i => X i ω) n) atTop (𝓝 p)

end WantedExt.Biology.StatisticalGenetics.LiMantelSegregationWanted
