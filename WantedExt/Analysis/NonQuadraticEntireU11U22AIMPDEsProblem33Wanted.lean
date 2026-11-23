/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Entire solutions of u₁₁u₂₂ = 1 need not be quadratic (AimPL nonlinear PDE, Problem 1.45)

AimPL Nonlinear PDEs in real and complex geometry, Problem 1.45 (Xiangwen Zhang): let `u : ℝ² → ℝ`
be a solution of `u₁₁ u₂₂ = 1`. If `u(x) ≤ C(1 + |x|²)`, then `u` must be quadratic. Can the growth
condition be removed? If one considers instead solutions `u : Ω → ℝ` for `Ω ⊆ ℝ²` convex and
bounded, with Dirichlet boundary conditions, can one obtain a `C²` boundary estimate?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

namespace MathlibExt.Analysis.NonQuadraticEntireU11U22AIMPDEsProblem33Wanted

/-!
Source: AimPL: Nonlinear PDEs in real and complex geometry, Section 1 (Monge-Ampère equations),
https://aimpl.org/nonlinpdegeom/1/, Problem 1.45 (Xiangwen Zhang). UnsolvedMath record UM-20002421
(`AIM-PDES-0033`), dataset ulamai/UnsolvedMath v1.8.0.

`u₁₁` and `u₂₂` are the second derivatives of the coordinate slices of `u : ℝ × ℝ → ℝ`. Mooney and
Savin study `(u₁₁u₂₂)^{1/2} = 1` for `u` convex along coordinate lines (their equation (1), elliptic
on that class), so the claim keeps that condition (`u₁₁ > 0`, which with `u₁₁u₂₂ = 1` gives `u₂₂ >
0`); smooth `u`; quadratic means a polynomial of degree at most two in `(x₁, x₂)`. The growth
question is the claim that every entire solution is quadratic; its refutation is Mooney and Savin's
Theorem 1.7. The second question (a `C²` boundary estimate on bounded convex domains, data
unspecified; Mooney and Savin's Remark 1.6 calls the boundary `C²` estimate tricky even in two
dimensions) is not formalized.
-/

open scoped ContDiff

/-- The pure second derivative `u₁₁(x) = ∂²u/∂x₁²` of `u : ℝ × ℝ → ℝ` at `x`: the second
derivative of the horizontal slice `t ↦ u (t, x₂)` at `x₁`. -/
noncomputable def d11 (u : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  iteratedDeriv 2 (fun t => u (t, x.2)) x.1

/-- The pure second derivative `u₂₂(x) = ∂²u/∂x₂²` of `u : ℝ × ℝ → ℝ` at `x`: the second
derivative of the vertical slice `t ↦ u (x₁, t)` at `x₂`. -/
noncomputable def d22 (u : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  iteratedDeriv 2 (fun t => u (x.1, t)) x.2

/-- `u` is a quadratic polynomial in the coordinates `(x₁, x₂)`. -/
def IsQuadraticPolynomial (u : ℝ × ℝ → ℝ) : Prop :=
  ∃ a b c d e f : ℝ, ∀ x : ℝ × ℝ,
    u x = a * x.1 ^ 2 + b * x.1 * x.2 + c * x.2 ^ 2 + d * x.1 + e * x.2 + f

/-- AimPL Problem 1.45 with the growth condition removed: every smooth entire solution
`u : ℝ² → ℝ` of `u₁₁ u₂₂ = 1` that is convex along horizontal lines (`u₁₁ > 0`, the elliptic
branch) is a quadratic polynomial. -/
def entireSolutionsQuadratic : Prop :=
  ∀ u : ℝ × ℝ → ℝ, ContDiff ℝ ∞ u → (∀ x, 0 < d11 u x) → (∀ x, d11 u x * d22 u x = 1) →
    IsQuadraticPolynomial u

/--
Resolved false: the growth condition cannot be removed. Mooney and Savin construct non-quadratic
entire solutions of `u₁₁u₂₂ = 1` that are convex along coordinate lines (Theorem 1.7; smooth by
their Corollary 1.5, and by their Corollary 1.2 they grow faster than quadratically, like `|x|² log
|x|` along the diagonals). Source: AimPL: Nonlinear PDEs in real and complex geometry, Section 1
(Monge-Ampère equations), https://aimpl.org/nonlinpdegeom/1/, Problem 1.45 (Xiangwen Zhang);
resolution: C. Mooney and O. Savin, Regularity results for the equation u11u22 = 1, Discrete Contin.
Dyn. Syst. 39 (2019), no. 12, arXiv:1806.05532, Theorem 1.7: there exist non-quadratic entire
solutions to (1), the equation (u11u22)^{1/2} = 1 for coordinate-convex u; Corollary 1.5: viscosity
solutions of (1) are smooth; Corollary 1.2: a smooth entire solution with |u| < C(1 + |x|²) is a
quadratic polynomial; the solution constructed grows like |x|² log |x| along the diagonals,
https://doi.org/10.3934/dcds.2019235.
-/
public theorem_wanted entireSolutionsQuadratic_refuted : ¬ entireSolutionsQuadratic

end MathlibExt.Analysis.NonQuadraticEntireU11U22AIMPDEsProblem33Wanted
