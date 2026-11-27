/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.AdditiveNoiseModelIdentifiability
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Tests for `MathlibExt.Probability.AdditiveNoiseModelIdentifiability`

Log-densities are written up to additive constants, which change none of their derivatives and
are absorbed in `η`.
-/

namespace MathlibExtTest.Probability.AdditiveNoiseModelIdentifiability

open MathlibExt.ComputerScience.AdditiveNoiseModelIdentifiabilityWanted

/-- Non-vacuity: the linear Gaussian model `Y = X + N` with standard Gaussian `X` and `N`
(`ξ(x) = -x² / 2`, `ν(n) = -n² / 2`) is reversible, with backward model `X = Y / 2 + Ñ`,
`Var Ñ = 1 / 2` (`ν̃(m) = -m²`) and `Var Y = 2` (`η(y) = -y² / 4`). These functions meet every
hypothesis of `identifiability_ode_of_reversible`, at every point. -/
example : ∃ f g ν ξ νt η : ℝ → ℝ, ContDiff ℝ 3 f ∧ ContDiff ℝ 3 g ∧ ContDiff ℝ 3 ν ∧
    ContDiff ℝ 3 ξ ∧ ContDiff ℝ 3 νt ∧ ContDiff ℝ 3 η ∧
    (∀ x y, ν (y - f x) + ξ x = νt (x - g y) + η y) ∧
    ∀ x y, iteratedDeriv 2 ν (y - f x) * deriv f x ≠ 0 :=
  ⟨fun x => x, fun y => y / 2, fun n => -n ^ 2 / 2, fun x => -x ^ 2 / 2, fun m => -m ^ 2,
    fun y => -y ^ 2 / 4, by fun_prop, by fun_prop, by fun_prop, by fun_prop, by fun_prop,
    by fun_prop, fun x y => by ring, fun x y => by simp⟩

/-- A nonlinear function identifies the causal direction even when the cause and the noise are
Gaussian: the model `Y = X³ + N` with standard Gaussian `X` and `N` has no backward model with
three times continuously differentiable ingredients. At `(x, y) = (1, 1)`, where `ν' = 0`,
`ν'' = -1` and `ν''' = 0` at `y - f(x) = 0`, `f' = 3`, `f'' = 6`, `ξ'' = -1` and `ξ''' = 0`,
equation (7) would read `0 = 34`. -/
example : ¬ ∃ g νt η : ℝ → ℝ, ContDiff ℝ 3 g ∧ ContDiff ℝ 3 νt ∧ ContDiff ℝ 3 η ∧
    ∀ x y : ℝ, -(y - x ^ 3) ^ 2 / 2 + -x ^ 2 / 2 = νt (x - g y) + η y := by
  rintro ⟨g, νt, η, hg, hνt, hη, hrev⟩
  have h := identifiability_ode_of_reversible (f := fun x => x ^ 3)
    (ν := fun n => -n ^ 2 / 2) (ξ := fun x => -x ^ 2 / 2) (x := 1) (y := 1) (by fun_prop) hg
    (by fun_prop) (by fun_prop) hνt hη hrev (by simp)
  norm_num at h

/-- A non-Gaussian cause identifies the causal direction of a linear model with Gaussian noise:
the model `Y = X + N` with standard Gaussian `N` and a cause of density proportional to
`exp (-x⁴ / 4)` has no backward model with three times continuously differentiable
ingredients. At `(x, y) = (1, 0)`, equation (7) would read `ξ'''(1) = 0`, while
`ξ'''(1) = -6`. -/
example : ¬ ∃ g νt η : ℝ → ℝ, ContDiff ℝ 3 g ∧ ContDiff ℝ 3 νt ∧ ContDiff ℝ 3 η ∧
    ∀ x y : ℝ, -(y - x) ^ 2 / 2 + -x ^ 4 / 4 = νt (x - g y) + η y := by
  rintro ⟨g, νt, η, hg, hνt, hη, hrev⟩
  have h := identifiability_ode_of_reversible (f := fun x => x) (ν := fun n => -n ^ 2 / 2)
    (ξ := fun x => -x ^ 4 / 4) (x := 1) (y := 0) (by fun_prop) hg (by fun_prop) (by fun_prop)
    hνt hη hrev (by simp)
  norm_num [iteratedDeriv_fun_id] at h

end MathlibExtTest.Probability.AdditiveNoiseModelIdentifiability
