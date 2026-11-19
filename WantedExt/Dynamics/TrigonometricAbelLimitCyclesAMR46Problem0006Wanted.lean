/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Limit cycles of trigonometric Abel equations (Gasull, Problem 6)

Gasull, Some open problems in low dimensional dynamical systems, Problem 6: for the family `dx/dt =
(a₀ + a₁ sin t + a₂ cos t) x³ + (b₀ + b₁ sin t + b₂ cos t) x²`, is `3` its maximum number of
`2π`-periodic limit cycles?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

namespace MathlibExt.Dynamics.TrigonometricAbelLimitCyclesAMR46Problem0006Wanted

/-!
Source: A. Gasull, Some open problems in low dimensional dynamical systems, SeMA J. 78 (2021),
arXiv:2012.02524, Problem 6. UnsolvedMath record UM-04700006 (`AMR-046-0006`), dataset
ulamai/UnsolvedMath v1.8.0.

A limit cycle is a `2π`-periodic solution isolated among the `2π`-periodic solutions (by its value
at `t = 0`, where solutions are determined by their initial value); as the source notes, `x = 0` is
always a periodic solution and counts when it is isolated. Limit cycles are counted by their initial
values, with `Set.encard` (an infinite set has size `⊤`). The maximum `3` means at most `3` for all
coefficients and exactly `3` for some. The general `(p, q, m, n)` version (Problem 7) is the
OpenConjectures entry `TrigAbelLimitCycleMaximum`.
-/

open Real

/-- The linear trigonometric polynomial `c₀ + c₁ sin t + c₂ cos t`. -/
noncomputable def trigCoeff (c : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  c 0 + c 1 * sin t + c 2 * cos t

/-- A `2π`-periodic solution of
`x' = (a₀ + a₁ sin t + a₂ cos t) x³ + (b₀ + b₁ sin t + b₂ cos t) x²`. -/
def IsPeriodicSolution (a b : Fin 3 → ℝ) (x : ℝ → ℝ) : Prop :=
  (∀ t, HasDerivAt x (trigCoeff a t * x t ^ 3 + trigCoeff b t * x t ^ 2) t) ∧
    ∀ t, x (t + 2 * π) = x t

/-- A limit cycle: a `2π`-periodic solution isolated among the `2π`-periodic solutions (by its value
at `t = 0`); the solution `x = 0` counts when it is isolated. -/
def IsLimitCycle (a b : Fin 3 → ℝ) (x : ℝ → ℝ) : Prop :=
  IsPeriodicSolution a b x ∧ ∃ δ > 0, ∀ y : ℝ → ℝ, IsPeriodicSolution a b y →
    |y 0 - x 0| < δ → y 0 = x 0

/-- The initial values `x(0)` of the limit cycles. -/
def limitCycleValues (a b : Fin 3 → ℝ) : Set ℝ :=
  {x₀ | ∃ x, IsLimitCycle a b x ∧ x 0 = x₀}

/-- Gasull's question, with a positive answer: `3` is the maximum number of `2π`-periodic limit
cycles of the trigonometric Abel equations with linear trigonometric coefficients (at most `3` for
all coefficients, and exactly `3` for some). -/
def maxThreeLimitCycles : Prop :=
  (∀ a b : Fin 3 → ℝ, (limitCycleValues a b).encard ≤ 3) ∧
    ∃ a b : Fin 3 → ℝ, (limitCycleValues a b).encard = 3

/--
Resolved true: Yu, Huang and Liu (Theorem 1.3) prove that the equation has at most three limit
cycles, `x = 0` included, for all real parameters, and that the bound three is attained. Source: A.
Gasull, Some open problems in low dimensional dynamical systems, SeMA J. 78 (2021),
arXiv:2012.02524, Problem 6; resolution: X. Yu, J. Huang and C. Liu, Maximum number of limit cycles
for Abel equation having coefficients with linear trigonometric functions, J. Differential Equations
410 (2024); arXiv:2309.00510, Theorem 1.3: equation (3) with arbitrary real parameters a₀, a₁, a₂,
b₀, b₁, b₂ has at most three limit cycles (including x = 0), and this upper bound is sharp,
https://doi.org/10.1016/j.jde.2024.07.030.
-/
public theorem_wanted maxThreeLimitCycles_holds : maxThreeLimitCycles

end MathlibExt.Dynamics.TrigonometricAbelLimitCyclesAMR46Problem0006Wanted
