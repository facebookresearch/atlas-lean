/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

namespace MathlibExt.Probability.SheppardArcsineWanted

/--
**Sheppard's formula (Gaussian arcsine law).** Let $\rho$ be a real number with $-1 < \rho < 1$,
and let $\gamma$ be the multivariate Gaussian measure on $\mathbb{R}^2$ with mean $0$ and
covariance matrix whose diagonal entries are $1$ and whose off-diagonal entries are $\rho$ (the
law of a standard bivariate normal vector with correlation $\rho$). Then the open first quadrant
$\{x \in \mathbb{R}^2 : x_1 > 0,\ x_2 > 0\}$ has $\gamma$-probability
$\frac{1}{4} + \frac{\arcsin \rho}{2\pi}$.

Sources: Y. L. Tong, The Multivariate Normal Distribution, Springer, 1990, Ch. 3;
W. F. Sheppard, "On the application of the theory of error to cases of normal distribution
and normal correlation", Phil. Trans. R. Soc. Lond. A 192 (1899), 101–167;
https://en.wikipedia.org/wiki/Multivariate_normal_distribution
-/
public theorem_wanted sheppard_quadrant_probability_arcsine (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1) 1) :
    let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of (fun i j => if i = j then 1 else ρ);
    (ProbabilityTheory.multivariateGaussian 0 S).real {x | 0 < x 0 ∧ 0 < x 1}
      = 1 / 4 + Real.arcsin ρ / (2 * Real.pi)

end MathlibExt.Probability.SheppardArcsineWanted
