/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.Calculus.ScottishBook66Wanted

open MeasureTheory

/-- **Mazur's mixed partial derivatives claim.** This is the following statement, the claim of
Mazur's Problem 66 from the Scottish Book. Let $Q = (0, 1) \times (0, 1)$ be the open unit square.
For every function $f : \mathbb{R}^2 \to \mathbb{R}$ such that, at every point $(x, y) \in Q$, the
functions $s \mapsto f(s, y)$ and $s \mapsto f(x, s)$ are differentiable at $x$ and at $y$
respectively, and their derivatives $\partial_x f(\cdot, y)$ and $\partial_y f(x, \cdot)$ are
again differentiable at $x$ and at $y$ respectively, the mixed partial derivative
$\partial_x \partial_y f$ exists at almost every point of $Q$ for Lebesgue measure: for almost
every $(x, y) \in Q$, the function $s \mapsto \partial_y f(s, y)$ is differentiable at $x$.

Mazur asked whether a function with first partial derivatives and both pure second partial
derivatives must have its mixed second partial derivatives almost everywhere; the claim asks this
only for $\partial_x \partial_y f$. -/
def ScottishBookProblem66Claim : Prop :=
  ∀ f : ℝ × ℝ → ℝ,
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun x' => f (x', y)) x) →
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun y' => f (x, y')) y) →
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (deriv (fun x' => f (x', y))) x) →
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (deriv (fun y' => f (x, y'))) y) →
    ∀ᵐ p ∂(volume.restrict (Set.Ioo (0, 0) (1, 1) :
      Set (ℝ × ℝ))),
      DifferentiableAt ℝ (fun x' => deriv (fun y' => f (x', y')) p.2)
        p.1

/--
**Mazur's Problem 66 has a negative answer.** Mazur's mixed partial derivatives claim is false:
there is a function $f : \mathbb{R}^2 \to \mathbb{R}$ such that, at every point $(x, y)$ of the
open unit square $Q = (0, 1) \times (0, 1)$, the functions $s \mapsto f(s, y)$ and
$s \mapsto f(x, s)$ are differentiable at $x$ and at $y$ respectively, and their derivatives
$\partial_x f(\cdot, y)$ and $\partial_y f(x, \cdot)$ are again differentiable at $x$ and at $y$
respectively, but the set of points $(x, y) \in Q$ at which $s \mapsto \partial_y f(s, y)$ is not
differentiable at $x$ is not a Lebesgue null set.

Source: S. Mazur, Problem 66 of the
Scottish Book; refuted by V. Mykhaylyuk and A. Plichko, who construct a
separately twice differentiable function on `[0, 1]²` and a set of
positive measure on which the mixed derivative `f_xy` does not exist
("On a Mazur problem from 'The Scottish Book' concerning second partial
derivatives", Colloq. Math. 141 (2015), 175–181, arXiv:1508.06909).
-/
theorem_wanted mazur66_refuted : ¬ ScottishBookProblem66Claim

end MathlibExt.Analysis.Calculus.ScottishBook66Wanted
