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

/-- Mazur's Problem 66 from the Scottish Book: if a real-valued function
`f` of two real variables has first partial derivatives and the two pure
second partial derivatives, must the two mixed second partial derivatives
exist almost everywhere? The hypotheses and the conclusion are stated
on the open unit square: `f` is separately twice differentiable at every
point of `(0, 1) × (0, 1)`, and the conclusion is that the mixed partial
`f_xy`, the derivative in `x` of the `y`-partial, exists at almost every
point of the square. -/
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
Mazur's Problem 66 is false: the mixed second partial derivatives need
not exist almost everywhere. Source: S. Mazur, Problem 66 of the
Scottish Book; refuted by V. Mykhaylyuk and A. Plichko, who construct a
separately twice differentiable function on `[0, 1]²` and a set of
positive measure on which the mixed derivative `f_xy` does not exist
("On a Mazur problem from 'The Scottish Book' concerning second partial
derivatives", Colloq. Math. 141 (2015), 175–181, arXiv:1508.06909).
-/
theorem_wanted mazur66_refuted : ¬ ScottishBookProblem66Claim

end MathlibExt.Analysis.Calculus.ScottishBook66Wanted
