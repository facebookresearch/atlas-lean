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
Sheppard's formula (Gaussian arcsine law): for a standard bivariate normal vector with
correlation `ρ ∈ (-1, 1)`, the first-quadrant probability is `1/4 + arcsin ρ / (2π)`.

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
