/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Positive entire solutions of the nonlinear heat equation (Oberwolfach Reports 29/2005)

Oberwolfach workshop Topological and Variational Methods for Differential Equations (2005),
Conjecture 1 (P. Quittner): positive solutions of `u_t - Δu = u^p` on `ℝ^N × ℝ` (`p > 1`) exist if
and only if `p (N - 2) ≥ N + 2`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Laplacian

@[expose] public section

namespace MathlibExt.Analysis.ParabolicLiouvilleCriticalExponentOWR1050Problem012Wanted

/-!
Source: P. Quittner, in Topological and Variational Methods for Differential Equations, Oberwolfach
Reports 2 (2005), no. 29, pp. 1649-1650, Conjecture 1, DOI 10.4171/OWR/2005/29. UnsolvedMath record
UM-30000261 (`OWR-1050-012`), dataset ulamai/UnsolvedMath v1.8.0.

A positive classical solution is read as a function `u (x, t) > 0` that is `C²` in `(x, t)` and
satisfies the equation at every point. Quittner's theorem excludes the larger class of positive
classical (`C^{2,1}`) solutions, and the positive steady states that give the other direction are
`C²`, so the choice does not affect either direction. For `N ≤ 2` no `p > 1` satisfies `p (N - 2) ≥
N + 2` and Quittner's theorem covers every `p > 1`.
-/

open Laplacian

/-- A positive classical solution of `u_t - Δu = u^p` on `ℝ^N × ℝ`: a function `u (x, t) > 0` that
is twice continuously differentiable in `(x, t)` and satisfies the equation at every point, where
`u_t` is the derivative of `t ↦ u (x, t)` and `Δu` is the Laplacian of `x ↦ u (x, t)`. -/
def IsPositiveClassicalSolution (N : ℕ) (p : ℝ) (u : EuclideanSpace ℝ (Fin N) × ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 u ∧ (∀ z, 0 < u z) ∧
    ∀ x t, deriv (fun s => u (x, s)) t - Δ (fun y => u (y, t)) x = u (x, t) ^ p

/-- Quittner's conjecture (Oberwolfach Report 29/2005, Conjecture 1): for `N ≥ 1` and `p > 1`, the
equation `u_t - Δu = u^p` on `ℝ^N × ℝ` has a positive classical solution if and only if
`p (N - 2) ≥ N + 2`. -/
def positiveSolutionIffSupercritical : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ p : ℝ, 1 < p →
    ((∃ u, IsPositiveClassicalSolution N p u) ↔ (N : ℝ) + 2 ≤ p * ((N : ℝ) - 2))

/--
Resolved true: the source notes that the equation has positive (bounded radial) steady states
exactly when `p (N - 2) ≥ N + 2`, and Quittner proved (Theorem 1) that for `1 < p < p_S`, i.e. `p (N
- 2) < N + 2`, it has no positive classical solution on `ℝ^N × ℝ`, with no boundedness, symmetry or
decay assumption. Source: P. Quittner, in Topological and Variational Methods for Differential
Equations, Oberwolfach Reports 2 (2005), no. 29, pp. 1649-1650, Conjecture 1, DOI
10.4171/OWR/2005/29; resolution: P. Quittner, Optimal Liouville theorems for superlinear parabolic
problems, Duke Math. J. 170 (2021), arXiv:2003.13223, Theorem 1: for 1 < p < p_S (that is, p(n - 2)
< n + 2) and n ≥ 1, u_t - Δu = u^p in ℝⁿ × ℝ has no positive classical solution; the source notes
that (3) has positive steady states if and only if p(N - 2) ≥ N + 2,
https://arxiv.org/abs/2003.13223.
-/
public theorem_wanted positiveSolutionIffSupercritical_holds : positiveSolutionIffSupercritical

end MathlibExt.Analysis.ParabolicLiouvilleCriticalExponentOWR1050Problem012Wanted
