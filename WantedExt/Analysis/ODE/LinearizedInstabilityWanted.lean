/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lyapunov's indirect method: instability

Let `f : ℝⁿ → ℝⁿ` be `C¹` with `f(x⋆) = 0` and Jacobian matrix `A` at `x⋆`. If `A` has an
eigenvalue with positive real part, then `x⋆` is an unstable equilibrium of `x' = f(x)`: there
is `ε > 0` such that arbitrarily close to `x⋆` there are initial points from which every
solution on `[0, ∞)` eventually leaves the ball of radius `ε` around `x⋆` (a solution that does
not exist on all of `[0, ∞)` leaves every bounded set, so the quantifier over solutions defined
on `[0, ∞)` loses nothing). Vectors carry the sup norm.

This is the instability half of Khalil, *Nonlinear Systems*, 3rd ed. (2002), Theorem 4.7; the
stability half is `MathlibExt.Analysis.ODE.LinearizedStability.
exists_locallyExponentiallyStable_of_hasFDerivAt`. Together with
`MathlibExt.Biology.Epidemiology.NextGenerationMatrix.exists_re_pos_jacobian_of_one_lt_R0` it
gives the instability half of Theorem 2 of van den Driessche and Watmough (2002): the
disease-free equilibrium is unstable when `R₀ > 1`.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.LinearAlgebra.Matrix.MMatrix
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace MathlibExt.Analysis.ODE.LinearizedInstabilityWanted

/-- **Lyapunov's indirect method, instability** (Khalil 2002, Theorem 4.7). If `f` is `C¹`,
`f x⋆ = 0`, and the Jacobian matrix `A` of `f` at `x⋆` has an eigenvalue with positive real
part, then `x⋆` is unstable: for some `ε > 0`, every neighbourhood of `x⋆` contains an initial
point `x₀` from which every solution of `x' = f(x)` on `[0, ∞)` reaches distance `≥ ε` from
`x⋆`. -/
theorem_wanted exists_unstable_of_hasFDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ι → ℝ} {xstar : ι → ℝ} {A : Matrix ι ι ℝ} (hf : f xstar = 0)
    (hfC1 : ContDiff ℝ 1 f)
    (hfA : HasFDerivAt f (LinearMap.toContinuousLinearMap (Matrix.toLin' A)) xstar)
    (hA : ∃ μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), 0 < μ.re) :
    ∃ ε > 0, ∀ δ > 0, ∃ x₀ : ι → ℝ, ‖x₀ - xstar‖ < δ ∧ ∀ x : ℝ → ι → ℝ, x 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt x (f (x t)) t) → ∃ t, 0 ≤ t ∧ ε ≤ ‖x t - xstar‖

end MathlibExt.Analysis.ODE.LinearizedInstabilityWanted
