/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lebesgue functions of Lagrange interpolation on subintervals (Erdős Problem 1153)

Erdős Problem 1153: for nodes `x₁, …, xₙ ∈ [-1, 1]` with Lagrange basis polynomials `lₖ` and `λ(x) =
∑ₖ |lₖ(x)|`, is `max_{x ∈ [a, b]} λ(x) > (2/π - o(1)) log n` for every fixed `-1 ≤ a < b ≤ 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Analysis.Polynomial.Lagrange

@[expose] public section

namespace MathlibExt.Analysis.LagrangeLebesgueSubintervalErdosProblem1153Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1153, https://www.erdosproblems.com/1153 (status
PROVED). UnsolvedMath record UM-30007194 (`EP-1153`), dataset ulamai/UnsolvedMath v1.8.0.

The nodes are distinct (the `lₖ` presuppose it). `λ` is MathlibExt's `Lagrange.lebesgueFunction`,
built from Mathlib's `Lagrange.basis`; for distinct nodes `lₖ(t) = ∏_{i ≠ k} (t - xᵢ)/(xₖ - xᵢ)`.
`(2/π - o(1)) log n` is read as: for every `ε > 0` and all large `n`, uniformly over the nodes.
formal-conjectures has no statement.
-/

open Filter

/-- Erdős Problem 1153: for all `-1 ≤ a < b ≤ 1` and `ε > 0`, for all large `n` and all distinct
nodes `x₁, …, xₙ ∈ [-1, 1]`, some `t ∈ [a, b]` has `λ(t) > (2/π - ε) log n`, where
`λ = Lagrange.lebesgueFunction x` is the Lebesgue function `∑ₖ |lₖ(t)|` of the Lagrange basis
polynomials `lₖ` of the nodes. -/
def lebesgueFunctionLowerBoundOnSubintervals : Prop :=
  ∀ a b : ℝ, -1 ≤ a → a < b → b ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ x : Fin n → ℝ, Function.Injective x → (∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) →
      ∃ t ∈ Set.Icc a b, (2 / Real.pi - ε) * Real.log n < Lagrange.lebesgueFunction x t

/--
Resolved true: Tao proved (Theorem 1.10(i)) that for a fixed interval `I ⊆ [-1, 1]`, all large `n`
and all distinct nodes `x₁ < ⋯ < xₙ` in `[-1, 1]`, `sup_{x ∈ I} λ(x) ≥ (2/π) log n - O(1)`, which
exceeds `(2/π - ε) log n` once `n` is large (Bernstein had `I = [-1, 1]`, and Erdős and Szabados `≫
log n`); erdosproblems.com/1153 lists the problem as proved on the strength of this preprint.
Source: T. F. Bloom, Erdős Problems, Problem #1153, https://www.erdosproblems.com/1153 (status
PROVED); resolution: T. Tao, Local Bernstein theory, and lower bounds for Lebesgue constants,
arXiv:2603.21453 (2026), Theorem 1.10(i): for a fixed interval I ⊆ [-1, 1], all large n and distinct
nodes x₁ < ⋯ < xₙ in [-1, 1], sup_{x ∈ I} λ(x) ≥ (2/π) log n - O(1); erdosproblems.com/1153 accepts
this as the resolution, https://arxiv.org/abs/2603.21453.
-/
public theorem_wanted lebesgueFunctionLowerBoundOnSubintervals_holds :
    lebesgueFunctionLowerBoundOnSubintervals

end MathlibExt.Analysis.LagrangeLebesgueSubintervalErdosProblem1153Wanted
