/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1121
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs

@[expose] public section

namespace MathlibExt.Geometry.ErdosProblem1121Wanted

/-! Source record `FC-ErdosProblem1121`, ported from FormalConjectures
`ErdosProblems/1121.lean` (`theorem erdos_1121`,
`erdos_1121.variants.higher_dimension`) and checked against
erdosproblems.com/1121. `ℝ²` unfolds to `EuclideanSpace ℝ (Fin 2)`. The two
claims are conjoined into one `conjecture`. Status: resolved true
(Goodman–Goodman; Hadwiger). -/

/-- **Erdős Problem 1121 (circle covering).** Write $B(c, r)$ for the closed ball with centre
$c$ and radius $r$ in Euclidean space $\mathbb{R}^d$. Call balls $B(c_1, r_1), \dots,
B(c_n, r_n)$ in $\mathbb{R}^d$ *nonseparable* if for every nonzero vector $v$ and every real
$t$ such that no point $p$ of any of the balls satisfies $\langle v, p \rangle = t$, either
$\langle v, c_i \rangle < t$ for all $i$ or $\langle v, c_i \rangle > t$ for all $i$. The
statement is the conjunction of two parts. First, for every natural number $n$, all points
$c_1, \dots, c_n \in \mathbb{R}^2$ and all reals $r_1, \dots, r_n > 0$ such that the discs
$B(c_i, r_i)$ are nonseparable, there is a point $z$ such that the closed disc
$B(z, r_1 + \dots + r_n)$ contains every $B(c_i, r_i)$. Second, the same holds in
$\mathbb{R}^d$ for every natural number $d$, with closed balls in place of discs. -/
def conjecture : Prop :=
  (∀ {n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin 2)) (r : Fin n → ℝ),
    (∀ i, 0 < r i) →
    (∀ (v : EuclideanSpace ℝ (Fin 2)) (t : ℝ), v ≠ 0 →
      (∀ i, ∀ p ∈ Metric.closedBall (c i) (r i), @inner ℝ _ _ v p ≠ t) →
      (∀ i, @inner ℝ _ _ v (c i) < t) ∨ (∀ i, t < @inner ℝ _ _ v (c i))) →
    ∃ z : EuclideanSpace ℝ (Fin 2),
      (⋃ i, Metric.closedBall (c i) (r i)) ⊆ Metric.closedBall z (∑ i, r i)) ∧
  (∀ {d n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
    (∀ i, 0 < r i) →
    (∀ (v : EuclideanSpace ℝ (Fin d)) (t : ℝ), v ≠ 0 →
      (∀ i, ∀ p ∈ Metric.closedBall (c i) (r i), @inner ℝ _ _ v p ≠ t) →
      (∀ i, @inner ℝ _ _ v (c i) < t) ∨ (∀ i, t < @inner ℝ _ _ v (c i))) →
    ∃ z : EuclideanSpace ℝ (Fin d),
      (⋃ i, Metric.closedBall (c i) (r i)) ⊆ Metric.closedBall z (∑ i, r i))

/--
**Circle covering theorem (Erdős Problem 1121).** Both parts of Erdős Problem 1121 hold. For
every natural number $d$, and in particular in the plane ($d = 2$): if $B(c_1, r_1), \dots,
B(c_n, r_n)$ are closed balls in Euclidean space $\mathbb{R}^d$ with centres $c_i$ and radii
$r_i > 0$ such that every hyperplane meeting none of the balls has all the centres $c_i$
strictly on the same side, then some closed ball of radius $r_1 + \dots + r_n$ contains all of
the balls.

Goodman and Goodman [GoGo45] proved this in the plane and in higher dimensions; Hadwiger [Ha47]
extended it to convex bodies.

Source: Goodman and Goodman [GoGo45] (planar
case and higher dimensions), per erdosproblems.com/1121, https://www.erdosproblems.com/1121.
Moved from `OpenConjectures/Geometry/ErdosProblem1121`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.ErdosProblem1121Wanted
