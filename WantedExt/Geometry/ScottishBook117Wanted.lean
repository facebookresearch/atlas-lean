/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.Geometry.ScottishBook117Wanted

open scoped InnerProductSpace

/-- A `1`-periodic continuous injective-on-`[0, 1)` curve `γ : ℝ → ℝ³`
has an (oriented) tangent line at `t` if there is a unit direction `v` such
that every nearby secant vector `γ s - γ t` is arbitrarily close, relative
to its length, to the line spanned by `v`. -/
def HasTangentLineAt (γ : ℝ → EuclideanSpace ℝ (Fin 3)) (t : ℝ) : Prop :=
  ∃ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ,
      0 < |s - t| → |s - t| < δ →
      ‖(γ s - γ t) - ⟪γ s - γ t, v⟫_ℝ • v‖ ≤ ε * ‖γ s - γ t‖

/-- Fréchet's Problem 117 from the Scottish Book: every Jordan curve in
`ℝ³` with an (oriented) tangent at every point admits a parametric
representation whose coordinate functions are differentiable in the
parameter and whose three coordinate derivatives never vanish
simultaneously. -/
def ScottishBookProblem117Claim : Prop :=
  ∀ γ : ℝ → EuclideanSpace ℝ (Fin 3),
    (∀ t, γ (t + 1) = γ t) →
    Continuous γ →
    Set.InjOn γ (Set.Ico (0 : ℝ) 1) →
    (∀ t, HasTangentLineAt γ t) →
    ∃ p : ℝ → EuclideanSpace ℝ (Fin 3),
      (∀ t, p (t + 1) = p t) ∧
      Continuous p ∧
      Set.InjOn p (Set.Ico (0 : ℝ) 1) ∧
      Set.range p = Set.range γ ∧
      ∀ t, DifferentiableAt ℝ p t ∧ deriv p t ≠ 0

/--
Problem 117 is false in general: a Jordan curve with a tangent at every
point need not admit a parametrization with everywhere non-vanishing
derivative. Source: M. Fréchet, Problem 117 of the Scottish Book; in
general, no, by A. J. Ward, Fundamenta Mathematicae 28 (1937), cited in the
typescript addendum Ad 117. Ward also gives a representation whose
derivatives exist and are not all zero except on a null set of parameter
values whose points have Carathéodory measure zero.
-/
theorem_wanted frechet117_refuted : ¬ ScottishBookProblem117Claim

end MathlibExt.Geometry.ScottishBook117Wanted
