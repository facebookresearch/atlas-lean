/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kong–Cox allele-sharing LOD scores

For a pedigree, let `V` be the finite set of inheritance vectors, `P₀` their null distribution
(no linkage), and `S` an allele-sharing score with null mean `μ`, null variance `σ² > 0` and
normalized form `Z = (S - μ) / σ`. Kong and Cox's linear model
`P_δ(v) = P₀(v) (1 + δ γ Z(v))`, with a weight `γ > 0`, is a probability distribution exactly
for `0 ≤ δ ≤ σ / (γ (μ - a))`, where `a` is the smallest possible score. Whatever part of the
marker data is missing, if `ℓ(v)` is the probability of the observed data given `v`, the
likelihood is `L(δ) = L(0) (1 + δ γ Z̄)`, with `Z̄` the posterior mean of `Z` given the data
under the null. Over independent pedigrees the log-likelihood ratio is
`∑ᵢ log (1 + δ γᵢ Z̄ᵢ)`; it is concave in `δ`, strictly so unless every `γᵢ Z̄ᵢ` vanishes, and
its derivative at `δ = 0` is the score statistic `∑ᵢ γᵢ Z̄ᵢ`. The LOD score is this ratio
divided by `log 10`, at its maximizer. The exponential model of the same paper and the
asymptotics of the tests are not stated here.

Sources: A. Kong and N. J. Cox, "Allele-sharing models: LOD scores and accurate linkage tests",
Am. J. Hum. Genet. 61 (1997) 1179–1188, model (1) and Appendix A.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.StatisticalGenetics.AssociationTests.KongCoxAlleleSharing
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.KongCoxAlleleSharingWanted

variable {V : Type*} [Fintype V]

/-- **The linear model has total mass one** (Kong and Cox 1997, model (1)). Let `V` be a finite
set and `P₀ : V → ℝ` with `∑_v P₀(v) = 1`, and let `S : V → ℝ` be a score with positive null
variance `σ² > 0`. Then for every weight `γ` and every `δ`, `∑_v P₀(v) (1 + δ γ Z(v)) = 1`.

Source: Kong and Cox (1997), model (1). -/
public theorem_wanted sum_linearModel (P₀ S : V → ℝ) (hsum : ∑ v, P₀ v = 1)
    (hvar : 0 < nullVariance P₀ S) (γ δ : ℝ) :
    ∑ v, linearModel P₀ S γ δ v = 1

/-- **Admissible range of `δ`** (Kong and Cox 1997, bound on `δ`). Let `V` be a finite set, let
`P₀ : V → ℝ` be nonnegative with `∑_v P₀(v) = 1`, and let the score `S : V → ℝ` have positive null
variance `σ² > 0` and null mean `μ`. Let `a` be a lower bound for `S` on the support of `P₀`
(`a ≤ S(v)` whenever `P₀(v) > 0`), and let `γ > 0` and `δ ≥ 0` satisfy `δ γ (μ - a) ≤ σ`. Then
`P₀(v) (1 + δ γ Z(v)) ≥ 0` for every `v`.

Source: Kong and Cox (1997), the bound `δ ≤ σ / (γ (μ - a))`. -/
public theorem_wanted linearModel_nonneg (P₀ S : V → ℝ) (hP₀ : ∀ v, 0 ≤ P₀ v)
    (hsum : ∑ v, P₀ v = 1) (hvar : 0 < nullVariance P₀ S) (a γ δ : ℝ)
    (ha : ∀ v, 0 < P₀ v → a ≤ S v) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hb : δ * γ * (nullMean P₀ S - a) ≤ Real.sqrt (nullVariance P₀ S)) (v : V) :
    0 ≤ linearModel P₀ S γ δ v

/-- **The bound on `δ` is sharp** (Kong and Cox 1997). Let `V` be a finite set, let `P₀ : V → ℝ`
be nonnegative with `∑_v P₀(v) = 1`, let the score `S : V → ℝ` have positive null variance
`σ² > 0` and null mean `μ`, and let `v₀` be an inheritance vector with `P₀(v₀) > 0` and
`S(v₀) = a < μ`. If `γ > 0` and `δ γ (μ - a) > σ`, then `P₀(v₀) (1 + δ γ Z(v₀)) < 0`, so the
linear model is not a probability distribution.

Source: Kong and Cox (1997), the bound `δ ≤ σ / (γ (μ - a))`. -/
public theorem_wanted linearModel_neg_of_gt (P₀ S : V → ℝ) (hP₀ : ∀ v, 0 ≤ P₀ v)
    (hsum : ∑ v, P₀ v = 1) (hvar : 0 < nullVariance P₀ S) (v₀ : V) (hv₀ : 0 < P₀ v₀)
    (hlt : S v₀ < nullMean P₀ S) (γ δ : ℝ) (hγ : 0 < γ)
    (hb : Real.sqrt (nullVariance P₀ S) < δ * γ * (nullMean P₀ S - S v₀)) :
    linearModel P₀ S γ δ v₀ < 0

/-- **Concavity of the pedigree-summed log-likelihood ratio** (Kong and Cox 1997). Let `ι` be a
finite set of independent pedigrees with weights `γᵢ` and null posterior mean scores `Z̄ᵢ`
(real numbers), and let `D = {δ | 1 + δ γᵢ Z̄ᵢ > 0 for every i}`. Then
`δ ↦ ∑ᵢ log (1 + δ γᵢ Z̄ᵢ)` is concave on `D`, and strictly concave on `D` if `γᵢ Z̄ᵢ ≠ 0` for
some `i`; so it has at most one maximizer in `D` in that case.

Source: Kong and Cox (1997). -/
public theorem_wanted concaveOn_sum_log {ι : Type*} [Fintype ι] (γ Zbar : ι → ℝ) :
    ConcaveOn ℝ {δ : ℝ | ∀ i, 0 < 1 + δ * (γ i * Zbar i)}
        (fun δ => ∑ i, Real.log (1 + δ * (γ i * Zbar i))) ∧
      ((∃ i, γ i * Zbar i ≠ 0) →
        StrictConcaveOn ℝ {δ : ℝ | ∀ i, 0 < 1 + δ * (γ i * Zbar i)}
          (fun δ => ∑ i, Real.log (1 + δ * (γ i * Zbar i))))

end WantedExt.Biology.StatisticalGenetics.KongCoxAlleleSharingWanted
