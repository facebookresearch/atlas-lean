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
public import Mathlib.Basic.Real.Basic
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

/-- Nonseparable circle families (and ball families in higher dimensions)
are covered by the summed-radius ball, conjoined. -/
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
Resolved true: Resolved affirmatively (Goodman-Goodman [GoGo45], higher dimensions; Hadwiger
[Ha47] convex bodies), per erdosproblems.com/1121. Source: Goodman and Goodman [GoGo45] (planar
case and higher dimensions), per erdosproblems.com/1121, https://www.erdosproblems.com/1121.
Moved from `OpenConjectures/Geometry/ErdosProblem1121`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.ErdosProblem1121Wanted
