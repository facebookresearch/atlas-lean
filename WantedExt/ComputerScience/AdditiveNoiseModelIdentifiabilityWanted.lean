/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Identifiability of bivariate nonlinear additive noise models

In a bivariate additive noise model `Y = f(X) + N`, with `N` independent of `X` and both with
strictly positive densities, the joint density is `p(x, y) = p_N(y - f(x)) p_X(x)`. If the
model is *reversible*, that is, the same joint density also has the form
`p̃_N(x - g(y)) p_Y(y)` of an additive noise model from `Y` to `X`, then the logarithms
`ν = log p_N` and `ξ = log p_X` and the function `f` satisfy a third-order differential equation
at every point where `ν''(y - f(x)) f'(x) ≠ 0` (equation (7) of Peters et al.). A generic triple
`(f, p_X, p_N)` does not satisfy it (their Proposition 21), so the causal direction of a
generic nonlinear additive noise model is identifiable from the joint distribution (their
Theorem 20, after Hoyer, Janzing, Mooij, Peters and Schölkopf 2009); linear `f` with Gaussian
`X` and `N` is the classical exception, see `LinearGaussianBackwardModel`.

The proof (Peters et al., Appendix A.5) compares the two expressions of
`π(x, y) = log p(x, y)`: from the backward model, `∂²π/∂x²` divided by `∂²π/∂x∂y` equals
`-1 / g'(y)` and does not depend on `x`; computing the same ratio from the forward model and
differentiating in `x` gives equation (7). It is a calculus computation not yet carried out
in Lean.

The statement below is written for the logarithms of the densities: `ν`, `ξ`, `ν̃ = log p̃_N`
and `η = log p_Y`, with the reversibility hypothesis
`ν(y - f(x)) + ξ(x) = ν̃(x - g(y)) + η(y)` (the logarithm of their equation (10)). All six
functions are assumed three times continuously differentiable.

Reference: J. Peters, J. M. Mooij, D. Janzing and B. Schölkopf, "Causal discovery with
continuous additive noise models", *J. Mach. Learn. Res.* **15** (2014), 2009–2053, Condition 19,
Theorem 20 and its proof in Appendix A.5 (after P. O. Hoyer, D. Janzing, J. M. Mooij, J. Peters
and B. Schölkopf, "Nonlinear causal discovery with additive noise models", *NIPS 21*, 2009).
-/

@[expose] public section

namespace MathlibExt.ComputerScience.AdditiveNoiseModelIdentifiabilityWanted

/-- **Reversible additive noise models satisfy the identifiability differential equation**
(Peters, Mooij, Janzing and Schölkopf, *Causal discovery with continuous additive noise models*,
JMLR 15 (2014), equation (7), Condition 19 and the proof of Theorem 20 in Appendix A.5, after
Hoyer et al. 2009). Let `f, g, ν, ξ, ν̃, η : ℝ → ℝ` be three times continuously differentiable,
where `ν, ξ` are the log-densities of the noise and of the cause of the model `Y = f(X) + N` and
`ν̃, η` those of a backward model `X = g(Y) + Ñ`, and suppose both models give the same joint
log-density, `ν(y - f(x)) + ξ(x) = ν̃(x - g(y)) + η(y)` for all `x, y`. Then at every point with
`ν''(y - f(x)) f'(x) ≠ 0`,
`ξ''' = ξ'' (-ν''' f' / ν'' + f'' / f') - 2 ν'' f'' f' + ν' f''' + ν' ν''' f'' f' / ν''
- ν' (f'')² / f'`,
where `ν` and its derivatives are evaluated at `y - f(x)` and `ξ`, `f` and their derivatives
at `x`. -/
theorem_wanted identifiability_ode_of_reversible {f g ν ξ νt η : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (hν : ContDiff ℝ 3 ν) (hξ : ContDiff ℝ 3 ξ)
    (hνt : ContDiff ℝ 3 νt) (hη : ContDiff ℝ 3 η)
    (hrev : ∀ x y, ν (y - f x) + ξ x = νt (x - g y) + η y) {x y : ℝ}
    (hxy : iteratedDeriv 2 ν (y - f x) * deriv f x ≠ 0) :
    iteratedDeriv 3 ξ x =
      iteratedDeriv 2 ξ x * (-(iteratedDeriv 3 ν (y - f x)) * deriv f x /
          iteratedDeriv 2 ν (y - f x) + iteratedDeriv 2 f x / deriv f x) -
        2 * iteratedDeriv 2 ν (y - f x) * iteratedDeriv 2 f x * deriv f x +
        deriv ν (y - f x) * iteratedDeriv 3 f x +
        deriv ν (y - f x) * iteratedDeriv 3 ν (y - f x) * iteratedDeriv 2 f x * deriv f x /
          iteratedDeriv 2 ν (y - f x) -
        deriv ν (y - f x) * iteratedDeriv 2 f x ^ 2 / deriv f x

end MathlibExt.ComputerScience.AdditiveNoiseModelIdentifiabilityWanted
