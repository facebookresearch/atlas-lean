/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GaussianProcessRegression
public import MathlibExt.Probability.Distributions.GaussianMLE

/-!
# Gaussian-process regression: the marginal likelihood

The evidence of a Gaussian-process regression model (Rasmussen and Williams, *Gaussian Processes
for Machine Learning*, MIT Press 2006, Section 2.2, Equations 2.28–2.30). With a zero-mean prior
`f ~ GP(0, k)`, the function values on the training inputs `x` are `f ~ N(0, K)`, `K = K(x, x)`,
and the targets are `y = f + ε` with independent noise `ε ~ N(0, σ² I)`. Marginalising `f`
(Equation 2.28) gives `y ~ N(0, K + σ² I)`, so the marginal likelihood is the Gaussian density of
`y` and its logarithm is Equation 2.30:

  `log p(y | x) = -½ yᵀ (K + σ² I)⁻¹ y - ½ log |K + σ² I| - (n/2) log 2π`.

The three terms are the data fit, the complexity penalty and the normalisation; maximising this
evidence over kernel hyperparameters is type-II maximum likelihood, the Bayesian model selection
of Rasmussen and Ghahramani, *Occam's razor* (NIPS 13, 2001).

Main results:

* `posDef_kernelMatrix_add`: `K + σ² I` is positive definite for a covariance kernel and `σ² > 0`.
* `map_targets_eq`: **the marginal law of the targets**, `f + ε ~ N(0, K + σ² I)` (Equation 2.28).
* `map_targets_eq_withDensity`: that law has the density `N(y | 0, K + σ² I)`.
* `log_marginalLikelihood`: **the log marginal likelihood** (Equation 2.30).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.GaussianProcessRegression

open MeasureTheory ProbabilityTheory Matrix WithLp MetaMathlibExt
open scoped MatrixOrder

variable {X : Type*} {ν : Type*} [Fintype ν] [DecidableEq ν]

omit [Fintype ν] in
/-- **Regularized kernel matrices are positive definite.** For a positive semidefinite kernel
matrix `K` on the training inputs and a noise variance `σ² > 0`, `K + σ² I` is positive definite
(Rasmussen and Williams 2006, Section 2.2). -/
theorem posDef_kernelMatrix_add (k : X → X → ℝ) (xs : ν → X)
    (hK : (kernelMatrix k xs xs).PosSemidef) {σ2 : ℝ} (hσ : 0 < σ2) :
    (kernelMatrix k xs xs + σ2 • 1).PosDef :=
  PosDef.posSemidef_add hK (PosDef.one.smul hσ)

/-- **Log marginal likelihood of Gaussian-process regression.** For a kernel `k`, a noise
variance `σ²`, training inputs `x` and targets `y`,
`log p(y | x) = -½ yᵀ (K + σ² I)⁻¹ y - ½ log |K + σ² I| - (n/2) log 2π` with `K = K(x, x)` and
`n` the number of training points (Rasmussen and Williams 2006, Equation 2.30). -/
noncomputable def logMarginalLikelihood (k : X → X → ℝ) (σ2 : ℝ) (xs : ν → X)
    (y : EuclideanSpace ℝ ν) : ℝ :=
  -(ofLp y ⬝ᵥ (kernelMatrix k xs xs + σ2 • 1)⁻¹ *ᵥ ofLp y) / 2 -
    Real.log (kernelMatrix k xs xs + σ2 • 1).det / 2 -
      (Fintype.card ν / 2) * Real.log (2 * Real.pi)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Marginal law of the targets in Gaussian-process regression** (Rasmussen and Williams 2006,
Equation 2.28 and the remark after Equation 2.30). If the function values on the training inputs
are `f ~ N(0, K)` with `K = K(x, x)` positive semidefinite, and the noise `ε ~ N(0, σ² I)`,
`σ² ≥ 0`, is independent of `f`, then the targets `y = f + ε` satisfy `y ~ N(0, K + σ² I)`. -/
theorem map_targets_eq (k : X → X → ℝ) (xs : ν → X) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    (hK : (kernelMatrix k xs xs).PosSemidef) {f ε : Ω → EuclideanSpace ℝ ν}
    (hf : Measurable f) (hε : Measurable ε) (hind : IndepFun f ε P)
    (hfl : P.map f = multivariateGaussian 0 (kernelMatrix k xs xs))
    (hεl : P.map ε = multivariateGaussian 0 (σ2 • 1)) :
    P.map (fun ω => f ω + ε ω) = multivariateGaussian 0 (kernelMatrix k xs xs + σ2 • 1) := by
  have h := map_linear_add_of_indepFun hf hε hind hK (PosSemidef.one.smul hσ) hfl hεl 1
  simpa [toEuclideanLin_one_apply] using h

/-- **Density of the targets in Gaussian-process regression.** Under the hypotheses of
`map_targets_eq` with `σ² > 0`, the targets `y = f + ε` have the density
`N(y | 0, K + σ² I) = (2π)^(-n/2) |K + σ² I|^(-1/2) exp (-yᵀ (K + σ² I)⁻¹ y / 2)` with respect to
Lebesgue measure: this density, as a function of the hyperparameters, is the marginal likelihood
`p(y | x)` (Rasmussen and Williams 2006, Equation 2.28). -/
theorem map_targets_eq_withDensity (k : X → X → ℝ) (xs : ν → X) {σ2 : ℝ} (hσ : 0 < σ2)
    (hK : (kernelMatrix k xs xs).PosSemidef) {f ε : Ω → EuclideanSpace ℝ ν}
    (hf : Measurable f) (hε : Measurable ε) (hind : IndepFun f ε P)
    (hfl : P.map f = multivariateGaussian 0 (kernelMatrix k xs xs))
    (hεl : P.map ε = multivariateGaussian 0 (σ2 • 1)) :
    P.map (fun ω => f ω + ε ω) = volume.withDensity fun y =>
      ENNReal.ofReal (multivariateGaussianPDFReal 0 (kernelMatrix k xs xs + σ2 • 1) y) := by
  rw [map_targets_eq k xs hσ.le hK hf hε hind hfl hεl,
    multivariateGaussian_eq_withDensity _ (posDef_kernelMatrix_add k xs hK hσ)]

/-- **The log marginal likelihood of Gaussian-process regression** (Rasmussen and Williams 2006,
Equation 2.30). For a positive semidefinite kernel matrix `K = K(x, x)` and `σ² > 0`, the
logarithm of the marginal density `N(y | 0, K + σ² I)` of the targets is
`-½ yᵀ (K + σ² I)⁻¹ y - ½ log |K + σ² I| - (n/2) log 2π`. -/
theorem log_marginalLikelihood (k : X → X → ℝ) (xs : ν → X) {σ2 : ℝ} (hσ : 0 < σ2)
    (hK : (kernelMatrix k xs xs).PosSemidef) (y : EuclideanSpace ℝ ν) :
    Real.log (multivariateGaussianPDFReal 0 (kernelMatrix k xs xs + σ2 • 1) y) =
      logMarginalLikelihood k σ2 xs y := by
  rw [log_multivariateGaussianPDFReal _ (posDef_kernelMatrix_add k xs hK hσ), sub_zero,
    logMarginalLikelihood]
  ring

end Cslib.MachineLearning.GaussianProcessRegression
