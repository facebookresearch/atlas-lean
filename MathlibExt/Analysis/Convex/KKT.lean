/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import MathlibExt.Analysis.Convex.KarushKuhnTucker

@[expose] public section

/-! # KKT sufficiency

For a convex differentiable problem, a feasible point with
nonnegative multipliers satisfying complementary slackness and
stationarity of the Lagrangian is a global minimizer. This is the
sufficiency core of roadmap package ML-22 of the Atlas TCS canon
roadmap; Slater's condition and necessity are follow-ups. This is
the standard `ConvexOn` / `DifferentiableAt` / `fderiv` form: it is
proved by applying
`MathlibExt.Analysis.Convex.KarushKuhnTucker.isMinOn_of_karush_kuhn_tucker_convex`,
not by a parallel gradient-form encoding.

Source: Boyd and Vandenberghe, Convex Optimization (2004),
Section 5.5.3.
-/

/-- KKT sufficiency: let `f` and the constraint functions `g i` be
convex on the whole space and differentiable at `x`, let `lam i ≥ 0`
be multipliers with complementary slackness
(`lam i * g i x = 0`) and stationarity
(`fderiv ℝ f x + ∑ i, lam i • fderiv ℝ (g i) x = 0`). Then `x`
minimizes `f` over the feasible set. -/
theorem kkt_sufficient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {x : E} {lam : Fin m → ℝ}
    (hf_conv : ConvexOn ℝ Set.univ f) (hg_conv : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf_diff : DifferentiableAt ℝ f x) (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hlam : ∀ i, 0 ≤ lam i) (hcs : ∀ i, lam i * g i x = 0)
    (hstat : fderiv ℝ f x + ∑ i : Fin m, lam i • fderiv ℝ (g i) x = 0)
    (y : E) (hy : ∀ i, g i y ≤ 0) :
    f x ≤ f y :=
  MathlibExt.Analysis.Convex.KarushKuhnTucker.isMinOn_of_karush_kuhn_tucker_convex
    hf_conv hg_conv hf_diff hg_diff hlam hcs hstat hy
