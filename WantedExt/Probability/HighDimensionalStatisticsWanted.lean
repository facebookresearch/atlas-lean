/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.HighDimensionalStatistics
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concentration results of non-asymptotic high-dimensional statistics: wishlist

Central tail bounds of Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*
(Cambridge University Press, 2019), Chapter 2, whose Lean proofs are deferred.
`MathlibExt.Probability.SubExponential` proves the sub-exponential tail bound (§2.1.3)
and Bernstein's inequality for bounded variables, and
`MathlibExt.Probability.HighDimensionalStatistics` proves Bernstein's inequality under the
Bernstein moment condition, the sub-exponential parameters `(2, 4)` of a centred `χ²₁` variable
and the resulting `χ²_n` tail bound (§2.1.3). The entry below records concentration of
Lipschitz functions of a standard Gaussian vector (§2.3), which needs the Gaussian log-Sobolev
or interpolation argument.
-/

namespace MathlibExt.Probability.HighDimensionalStatisticsWanted

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- **Concentration of Lipschitz functions of Gaussian variables** (Wainwright,
*High-Dimensional Statistics*, 2019, §2.3; R. Vershynin, arXiv:1011.3027, Proposition 5.34 for the
one-sided tail). Let `X` be a standard Gaussian vector in
`ℝⁿ` and `f : ℝⁿ → ℝ` be `L`-Lipschitz for the Euclidean norm. Then `f(X) - E[f(X)]` is
sub-Gaussian with parameter `L` (variance proxy `L²`), and hence
`P(|f(X) - E[f(X)]| ≥ t) ≤ 2 exp (-t² / (2 L²))` for every `t ≥ 0`. -/
public theorem_wanted lipschitz_concentration_stdGaussian {n : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n))) (L ^ 2)
        (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      ∀ t : ℝ, 0 ≤ t →
        (stdGaussian (EuclideanSpace ℝ (Fin n))).real
            {x | t ≤ |f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n))|} ≤
          2 * exp (-t ^ 2 / (2 * L ^ 2))

end

end MathlibExt.Probability.HighDimensionalStatisticsWanted
