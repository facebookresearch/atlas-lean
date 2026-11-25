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
**Residue theorem on a disc.** Let $c\in\mathbb{C}$ and $R>0$, and let $S$ be a finite set of
points of the open disc $\{z:|z-c|<R\}$. For each $s\in S$ let $r_s>0$ be such that the closed
disc $\{z:|z-s|\le r_s\}$ lies in $\{z:|z-c|<R\}$ and contains no point of $S$ other than $s$.
Let $f:\mathbb{C}\to\mathbb{C}$ be complex differentiable on $\{z:|z-c|\le R\}\setminus S$ and
integrable on the circle $|z-c|=R$ and on each circle $|z-s|=r_s$. Then, with all circles
oriented counterclockwise,
$$\oint_{|z-c|=R} f(z)\,dz=\sum_{s\in S}\oint_{|z-s|=r_s} f(z)\,dz.$$

Each integral on the right is $2\pi i$ times the residue of $f$ at $s$.

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
