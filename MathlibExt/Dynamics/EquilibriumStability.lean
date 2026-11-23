/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Stability of an equilibrium of a scalar equation on `[0, ∞)`

Stability notions for real-valued forward solutions, stated for an arbitrary solution relation
`Sol : (ℝ → ℝ) → Prop` (for example, "`p` solves `p' = f(p)` for all `t ≥ 0`"), so that different
models share one API. A model exposes its notions as abbreviations of these, as
`MathlibExt.Biology.Ecology.LevinsMetapopulation.IsGloballyStable c e` does with
`IsGloballyStable (LevinsMetapopulation.IsSolution c e)`.

## Main definitions

* `IsLyapunovStable Sol a D`: solutions in `Sol` that start in `D` close to `a` stay close to `a`
  for all `t ≥ 0`.
* `IsGloballyAttracting Sol a D`: every solution in `Sol` that starts in `D` tends to `a`.
* `IsGloballyStable Sol a D`: both.
-/

@[expose] public section

open Filter
open scoped Topology

namespace MathlibExt.Dynamics.EquilibriumStability

/-- `a` is **Lyapunov stable** for the solutions `Sol` starting in `D`: solutions that start in `D`
close to `a` stay close to `a` for all `t ≥ 0`. -/
def IsLyapunovStable (Sol : (ℝ → ℝ) → Prop) (a : ℝ) (D : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ p : ℝ → ℝ, Sol p → p 0 ∈ D → |p 0 - a| < δ →
    ∀ t, 0 ≤ t → |p t - a| < ε

/-- `a` **attracts** every solution in `Sol` starting in `D`. -/
def IsGloballyAttracting (Sol : (ℝ → ℝ) → Prop) (a : ℝ) (D : Set ℝ) : Prop :=
  ∀ p : ℝ → ℝ, Sol p → p 0 ∈ D → Tendsto p atTop (𝓝 a)

/-- `a` is **globally (asymptotically) stable** on `D` for `Sol`: Lyapunov stable and attracting
every solution starting in `D`. -/
def IsGloballyStable (Sol : (ℝ → ℝ) → Prop) (a : ℝ) (D : Set ℝ) : Prop :=
  IsLyapunovStable Sol a D ∧ IsGloballyAttracting Sol a D

end MathlibExt.Dynamics.EquilibriumStability
