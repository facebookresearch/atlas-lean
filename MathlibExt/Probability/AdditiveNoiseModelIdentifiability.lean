/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Identifiability of bivariate nonlinear additive noise models

In a bivariate additive noise model `Y = f(X) + N`, with `N` independent of `X` and both with
strictly positive densities, the joint density is `p(x, y) = p_N(y - f(x)) p_X(x)`. If the
model is *reversible*, that is, the same joint density also has the form
`p̃_N(x - g(y)) p_Y(y)` of an additive noise model from `Y` to `X`, then the logarithms
`ν = log p_N` and `ξ = log p_X` and the function `f` satisfy a third-order differential equation
at every point where `ν''(y - f(x)) f'(x) ≠ 0`, equation (7) of Peters, Mooij, Janzing and
Schölkopf. They call the model identifiable when equation (7) fails at some point where
`ν''(y - f(x)) f'(x) ≠ 0` (their Condition 18). By the theorem below such a model has no
backward model; this is the core of their proof that its causal direction can be read off the
joint distribution (their Theorem 19, after Hoyer, Janzing, Mooij, Peters and Schölkopf). Under
a mild condition on `f` and the noise, the laws of `X` for which the model is not identifiable
lie in a three-dimensional family (their Proposition 20); linear `f` with Gaussian `X` and `N`
is the classical exception, see `MathlibExt.Probability.LinearGaussianBackwardModel`.

The statement is written for the logarithms of the densities: `ν`, `ξ`, `ν̃ = log p̃_N`
and `η = log p_Y`, with the reversibility hypothesis
`ν(y - f(x)) + ξ(x) = ν̃(x - g(y)) + η(y)`. All six functions are assumed three times
continuously differentiable.

## Main result

* `identifiability_ode_of_reversible`: a reversible model satisfies equation (7) at every point
  with `ν''(y - f(x)) f'(x) ≠ 0`.

## Proof

Write `π(x, y) = ν(y - f(x)) + ξ(x) = ν̃(x - g(y)) + η(y)` for the joint log-density. The
backward form gives `∂²π/∂x² = ν̃''(x - g(y))` and `∂²π/∂x∂y = -g'(y) ν̃''(x - g(y))`, so for
fixed `y`, `g'(y) ∂²π/∂x² + ∂²π/∂x∂y = 0` for every `x`. The forward form gives
`∂²π/∂x² = ν'' f'² - ν' f'' + ξ''` and `∂²π/∂x∂y = -ν'' f'`, which are differentiable in `x`, so
the derivative in `x` of the left side vanishes as well. Where
`∂²π/∂x∂y = -ν''(y - f(x)) f'(x) ≠ 0`, eliminating `g'(y)` between these two identities gives
`∂²π/∂x∂y · ∂/∂x (∂²π/∂x²) = ∂²π/∂x² · ∂/∂x (∂²π/∂x∂y)`. Here `ξ'''` occurs only in
`∂/∂x (∂²π/∂x²)`, so solving for it, that is dividing by `∂²π/∂x∂y`, gives equation (7).

Peters et al. (Appendix A.5) argue with the ratio `∂²π/∂x² / ∂²π/∂x∂y = -1 / g'(y)`, which does
not depend on `x`. The identity above is the same argument without dividing by `g'(y)` or `ν̃''`;
its cross-multiplied form is the one they use in Appendix A.7.

## Implementation notes

The theorem keeps the full name and the docstring it had in the former wanted module
`WantedExt.ComputerScience.AdditiveNoiseModelIdentifiabilityWanted`, so its namespace still reads
`AdditiveNoiseModelIdentifiabilityWanted`. Its hypothesis that `η` is three times continuously
differentiable is part of that statement but is not used: `η(y)` does not depend on `x` and drops
out of `∂π/∂x`, the first step of the proof. The `unusedVariables` linter is turned off for this
theorem only. Of the other regularity hypotheses, the proof uses that `f`, `ν` and `ξ` are three
times differentiable, `ν̃` twice and `g` once.

The docstring numbers the condition and the theorem of Peters et al. 19 and 20; the arXiv version
cited below numbers them Condition 18 and Theorem 19, with the same equation (7) and Appendix A.5.

## References

* J. Peters, J. M. Mooij, D. Janzing and B. Schölkopf, "Causal discovery with continuous additive
  noise models", *J. Mach. Learn. Res.* **15** (2014), 2009–2053; arXiv:1309.6779v4: equation
  (7), Condition 18, Theorem 19 and its proof in Appendix A.5 (equations (11)–(15)),
  Proposition 20, and the proof of Corollary 21 in Appendix A.7.
* P. Hoyer, D. Janzing, J. M. Mooij, J. Peters and B. Schölkopf, "Nonlinear causal discovery with
  additive noise models", *Advances in Neural Information Processing Systems 21 (NIPS)*, 2009;
  Peters et al. reproduce its proof in Appendix A.5.
-/

@[expose] public section

namespace MathlibExt.ComputerScience.AdditiveNoiseModelIdentifiabilityWanted

/-- A `C³` function has derivative `deriv φ z` at every point `z`. -/
private lemma hasDerivAt_of_contDiff_three {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) (z : ℝ) :
    HasDerivAt φ (deriv φ z) z :=
  ((hφ.differentiable (by norm_num)) z).hasDerivAt

/-- The derivative of a `C³` function has derivative `iteratedDeriv 2 φ z` at every point. -/
private lemma hasDerivAt_deriv_of_contDiff_three {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) (z : ℝ) :
    HasDerivAt (deriv φ) (iteratedDeriv 2 φ z) z := by
  have h := ((hφ.differentiable_iteratedDeriv 1 (by norm_num)) z).hasDerivAt
  rwa [← iteratedDeriv_succ, iteratedDeriv_one] at h

/-- The second derivative of a `C³` function has derivative `iteratedDeriv 3 φ z` at every
point. -/
private lemma hasDerivAt_iteratedDeriv_two_of_contDiff_three {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ)
    (z : ℝ) : HasDerivAt (iteratedDeriv 2 φ) (iteratedDeriv 3 φ z) z := by
  have h := ((hφ.differentiable_iteratedDeriv 2 (by norm_num)) z).hasDerivAt
  rwa [← iteratedDeriv_succ] at h

/-- The algebraic step of `identifiability_ode_of_reversible`: eliminate `G = g'(y)` between
`G ∂²π/∂x² + ∂²π/∂x∂y = 0` (`h₁`) and its derivative in `x` (`h₂`), written with
`a, b, c` for the first three derivatives of `ν`, `p, q, r` for those of `f`, and `s, t` for the
second and third derivatives of `ξ`. -/
private lemma eq_of_eliminate {a b c p q r s t G : ℝ} (hb : b ≠ 0) (hp : p ≠ 0)
    (h₁ : G * (b * -p * -p + a * -q + s) + b * -p = 0)
    (h₂ : G * ((c * -p * -p + b * -q) * -p + b * -p * -q + (b * -p * -q + a * -r) + t) +
      (c * -p * -p + b * -q) = 0) :
    t = s * (-c * p / b + q / p) - 2 * b * q * p + a * r + a * c * q * p / b -
      a * q ^ 2 / p := by
  field_simp
  linear_combination (c * p ^ 3 - 3 * b * p * q + a * r - t) * h₁ +
    (b * p ^ 2 - a * q + s) * h₂

set_option linter.unusedVariables false in
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
theorem identifiability_ode_of_reversible {f g ν ξ νt η : ℝ → ℝ}
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
        deriv ν (y - f x) * iteratedDeriv 2 f x ^ 2 / deriv f x := by
  have D0 := @hasDerivAt_of_contDiff_three
  have D1 := @hasDerivAt_deriv_of_contDiff_three
  have D2 := @hasDerivAt_iteratedDeriv_two_of_contDiff_three
  -- derivatives of the arguments `y - f x` and `x - g y` in each variable
  have hfx (x y : ℝ) : HasDerivAt (fun x => y - f x) (-deriv f x) x := (D0 hf x).const_sub y
  have hfy (x y : ℝ) : HasDerivAt (fun y => y - f x) 1 y := (hasDerivAt_id' y).sub_const (f x)
  have hgx (x y : ℝ) : HasDerivAt (fun x => x - g y) 1 x := (hasDerivAt_id' x).sub_const (g y)
  have hgy (x y : ℝ) : HasDerivAt (fun y => x - g y) (-deriv g y) y := (D0 hg y).const_sub x
  have hν1 (x y : ℝ) : HasDerivAt (fun x => deriv ν (y - f x))
      (iteratedDeriv 2 ν (y - f x) * -deriv f x) x :=
    HasDerivAt.comp (h₂ := deriv ν) x (D1 hν (y - f x)) (hfx x y)
  -- `∂π/∂x`, computed from both models
  have h1 (x y : ℝ) : deriv ν (y - f x) * -deriv f x + deriv ξ x = deriv νt (x - g y) := by
    have hl : HasDerivAt (fun x => ν (y - f x) + ξ x)
        (deriv ν (y - f x) * -deriv f x + deriv ξ x) x :=
      ((D0 hν (y - f x)).comp x (hfx x y)).add (D0 hξ x)
    have hr : HasDerivAt (fun x => νt (x - g y) + η y) (deriv νt (x - g y) * 1) x :=
      ((D0 hνt (x - g y)).comp x (hgx x y)).add_const (η y)
    rw [show (fun x => ν (y - f x) + ξ x) = fun x => νt (x - g y) + η y from
      funext fun x => hrev x y] at hl
    rw [hl.unique hr, mul_one]
  -- `∂²π/∂x²`, computed from both models
  have h2 (x y : ℝ) : iteratedDeriv 2 ν (y - f x) * -deriv f x * -deriv f x +
      deriv ν (y - f x) * -iteratedDeriv 2 f x + iteratedDeriv 2 ξ x =
        iteratedDeriv 2 νt (x - g y) := by
    have hl : HasDerivAt (fun x => deriv ν (y - f x) * -deriv f x + deriv ξ x)
        (iteratedDeriv 2 ν (y - f x) * -deriv f x * -deriv f x +
          deriv ν (y - f x) * -iteratedDeriv 2 f x + iteratedDeriv 2 ξ x) x :=
      ((hν1 x y).mul (D1 hf x).neg).add (D1 hξ x)
    have hr : HasDerivAt (fun x => deriv νt (x - g y)) (iteratedDeriv 2 νt (x - g y) * 1) x :=
      HasDerivAt.comp (h₂ := deriv νt) x (D1 hνt (x - g y)) (hgx x y)
    rw [show (fun x => deriv ν (y - f x) * -deriv f x + deriv ξ x) =
      fun x => deriv νt (x - g y) from funext fun x => h1 x y] at hl
    rw [hl.unique hr, mul_one]
  -- `∂²π/∂x∂y`, computed from both models
  have h3 (x y : ℝ) : iteratedDeriv 2 ν (y - f x) * -deriv f x =
      iteratedDeriv 2 νt (x - g y) * -deriv g y := by
    have hνy : HasDerivAt (fun y => deriv ν (y - f x)) (iteratedDeriv 2 ν (y - f x) * 1) y :=
      HasDerivAt.comp (h₂ := deriv ν) y (D1 hν (y - f x)) (hfy x y)
    have hl : HasDerivAt (fun y => deriv ν (y - f x) * -deriv f x + deriv ξ x)
        (iteratedDeriv 2 ν (y - f x) * 1 * -deriv f x) y :=
      (hνy.mul_const (-deriv f x)).add_const (deriv ξ x)
    have hr : HasDerivAt (fun y => deriv νt (x - g y))
        (iteratedDeriv 2 νt (x - g y) * -deriv g y) y :=
      HasDerivAt.comp (h₂ := deriv νt) y (D1 hνt (x - g y)) (hgy x y)
    rw [show (fun y => deriv ν (y - f x) * -deriv f x + deriv ξ x) =
      fun y => deriv νt (x - g y) from funext fun y => h1 x y] at hl
    rw [← hl.unique hr, mul_one]
  -- for the fixed `y`, `g'(y) ∂²π/∂x² + ∂²π/∂x∂y`, written with the forward model, vanishes
  -- identically in `x`
  have hF : (fun x => deriv g y * (iteratedDeriv 2 ν (y - f x) * -deriv f x * -deriv f x +
      deriv ν (y - f x) * -iteratedDeriv 2 f x + iteratedDeriv 2 ξ x) +
        iteratedDeriv 2 ν (y - f x) * -deriv f x) = fun _ => 0 := by
    funext x
    linear_combination deriv g y * h2 x y + h3 x y
  -- so does its derivative in `x`
  have hν2 : HasDerivAt (fun x => iteratedDeriv 2 ν (y - f x))
      (iteratedDeriv 3 ν (y - f x) * -deriv f x) x :=
    HasDerivAt.comp (h₂ := iteratedDeriv 2 ν) x (D2 hν (y - f x)) (hfx x y)
  have hf1 : HasDerivAt (fun x => -deriv f x) (-iteratedDeriv 2 f x) x := (D1 hf x).neg
  have hf2 : HasDerivAt (fun x => -iteratedDeriv 2 f x) (-iteratedDeriv 3 f x) x :=
    (D2 hf x).neg
  have hFd : HasDerivAt (fun x => deriv g y * (iteratedDeriv 2 ν (y - f x) * -deriv f x *
      -deriv f x + deriv ν (y - f x) * -iteratedDeriv 2 f x + iteratedDeriv 2 ξ x) +
        iteratedDeriv 2 ν (y - f x) * -deriv f x)
      (deriv g y * ((iteratedDeriv 3 ν (y - f x) * -deriv f x * -deriv f x +
            iteratedDeriv 2 ν (y - f x) * -iteratedDeriv 2 f x) * -deriv f x +
          iteratedDeriv 2 ν (y - f x) * -deriv f x * -iteratedDeriv 2 f x +
          (iteratedDeriv 2 ν (y - f x) * -deriv f x * -iteratedDeriv 2 f x +
            deriv ν (y - f x) * -iteratedDeriv 3 f x) + iteratedDeriv 3 ξ x) +
        (iteratedDeriv 3 ν (y - f x) * -deriv f x * -deriv f x +
          iteratedDeriv 2 ν (y - f x) * -iteratedDeriv 2 f x)) x := by
    have h := ((((hν2.mul hf1).mul hf1).add ((hν1 x y).mul hf2)).add (D2 hξ x)).const_mul
      (deriv g y) |>.add (hν2.mul hf1)
    exact h
  rw [hF] at hFd
  -- eliminate `g'(y)`
  exact eq_of_eliminate (left_ne_zero_of_mul hxy) (right_ne_zero_of_mul hxy) (congrFun hF x)
    (hFd.unique (hasDerivAt_const x 0))

end MathlibExt.ComputerScience.AdditiveNoiseModelIdentifiabilityWanted
