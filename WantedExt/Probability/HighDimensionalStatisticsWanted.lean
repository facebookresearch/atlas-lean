/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.SubExponential
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concentration results of non-asymptotic high-dimensional statistics: wishlist

Central tail bounds of Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*
(Cambridge University Press, 2019), Chapter 2, whose Lean proofs are deferred.
`MathlibExt.Probability.SubExponential` proves the sub-exponential tail bound (§2.1.3)
and Bernstein's inequality for bounded variables; the entries below record:

* Bernstein's inequality under the Bernstein moment condition (§2.1.3), which needs a
  termwise integration of the exponential series;
* the sub-exponential parameters `(2, 4)` of a centred `χ²₁` variable and the resulting `χ²_n`
  tail bound (§2.1.3);
* concentration of Lipschitz functions of a standard Gaussian vector (§2.3), which needs
  the Gaussian log-Sobolev or interpolation argument.

"Rinaldo 2017" is A. Rinaldo, *36-755 Advanced Statistics Theory I*, Lecture 3 (Carnegie Mellon,
2017), an open account of the same statements with the same constants.
-/

namespace MathlibExt.Probability.HighDimensionalStatisticsWanted

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- **Bernstein's moment generating function bound** (Wainwright, *High-Dimensional Statistics*,
2019, §2.1.3; Rinaldo 2017, Definition 3.3 and Theorem 3.4). Let `X` be a centred real random
variable with all moments finite and
variance `σ² = E[X²]`, satisfying the Bernstein condition with parameter `b ≥ 0`:
`|E[X^k]| ≤ k! σ² b^(k-2) / 2` for every `k ≥ 3`. Then for every `t` with `b |t| < 1`,
`exp (t X)` is integrable and `E[exp (t X)] ≤ exp (t² σ² / (2 (1 - b |t|)))`. The source states
the condition for `k = 2, 3, …` about the mean `μ`; it holds with equality at `k = 2`. -/
public theorem_wanted mgf_le_of_bernsteinCondition {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {b σ : ℝ} (hb : 0 ≤ b)
    (hint : ∀ k : ℕ, Integrable (fun ω ↦ X ω ^ k) μ) (hmean : μ[X] = 0)
    (hvar : ∫ ω, X ω ^ 2 ∂μ = σ ^ 2)
    (hbern : ∀ k : ℕ, 3 ≤ k → |∫ ω, X ω ^ k ∂μ| ≤ k.factorial * σ ^ 2 * b ^ (k - 2) / 2)
    {t : ℝ} (ht : b * |t| < 1) :
    Integrable (fun ω ↦ exp (t * X ω)) μ ∧
      mgf X μ t ≤ exp (t ^ 2 * σ ^ 2 / (2 * (1 - b * |t|)))

/-- **Bernstein's inequality under the Bernstein condition** (Wainwright, *High-Dimensional
Statistics*, 2019, §2.1.3; Rinaldo 2017, Theorem 3.5). Under the hypotheses of
`mgf_le_of_bernsteinCondition`, for every `t ≥ 0`,
`P(|X| ≥ t) ≤ 2 exp (-t² / (2 (σ² + b t)))`. -/
public theorem_wanted measureReal_abs_ge_le_of_bernsteinCondition {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {b σ : ℝ}
    (hb : 0 ≤ b) (hint : ∀ k : ℕ, Integrable (fun ω ↦ X ω ^ k) μ) (hmean : μ[X] = 0)
    (hvar : ∫ ω, X ω ^ 2 ∂μ = σ ^ 2)
    (hbern : ∀ k : ℕ, 3 ≤ k → |∫ ω, X ω ^ k ∂μ| ≤ k.factorial * σ ^ 2 * b ^ (k - 2) / 2)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * exp (-t ^ 2 / (2 * (σ ^ 2 + b * t)))

/-- **A centred `χ²₁` variable is sub-exponential with parameters `(2, 4)`** (Wainwright,
*High-Dimensional Statistics*, 2019, §2.1.3, the `χ²` example): if `Z` is standard normal, then
`Z² - 1`
satisfies `E[exp (t (Z² - 1))] ≤ exp (4 t² / 2)` for `|t| < 1 / 4`. Here `Z` is the identity on
`ℝ` under `gaussianReal 0 1`. -/
public theorem_wanted hasSubexponentialMGF_sq_sub_one_gaussianReal :
    HasSubexponentialMGF (fun x : ℝ ↦ x ^ 2 - 1) 2 4 (gaussianReal 0 1)

/-- **Tail bound for the `χ²_n` distribution** (Wainwright, *High-Dimensional Statistics*, 2019,
§2.1.3, the `χ²` tail example; Rinaldo 2017, Example 3.8): if `Z₁, …, Zₙ` are independent standard
normal variables, then
`P(|(1/n) ∑ Zₖ² - 1| ≥ t) ≤ 2 exp (-n t² / 8)` for every `t ∈ (0, 1)`. Here the `Zₖ` are the
coordinates on `Fin n → ℝ` under the product measure. -/
public theorem_wanted measureReal_abs_chiSq_mean_sub_one_ge_le (n : ℕ) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).real
        {z | t ≤ |(1 / (n : ℝ)) * ∑ k, z k ^ 2 - 1|} ≤ 2 * exp (-(n : ℝ) * t ^ 2 / 8)

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
