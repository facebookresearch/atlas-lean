/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.CircleIntegral

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.Complex.ResidueTheoremWanted

/--
Residue theorem on a disc: if `f` is holomorphic on the closed disc minus a finite set
`S` of interior points, then the circle integral of `f` equals the sum of the circle
integrals over isolating circles around the points of `S` (each of which is `2πi` times the
residue at that point).

Sources: Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable",
entry "residue theorem"; L. V. Ahlfors, Complex Analysis, 3rd ed., Ch. 4, §5.1
(the residue theorem).
-/
theorem_wanted residueTheorem_closedBall
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {f : ℂ → ℂ} {S : Finset ℂ} {rad : ℂ → ℝ}
    (hS : ∀ s ∈ S, s ∈ Metric.ball c R)
    (hrad : ∀ s ∈ S, 0 < rad s ∧ Metric.closedBall s (rad s) ⊆ Metric.ball c R ∧
      ∀ s' ∈ S, s' ≠ s → s' ∉ Metric.closedBall s (rad s))
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R \ ↑S))
    (hint : CircleIntegrable f c R)
    (hintS : ∀ s ∈ S, CircleIntegrable f s (rad s)) :
    (∮ z in C(c, R), f z) = ∑ s ∈ S, ∮ z in C(s, rad s), f z

end MathlibExt.Analysis.Complex.ResidueTheoremWanted
