/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.MetricSpace.BoundedMetricTopologicallyEquivalent

/-! # Tests for `MathlibExt.Topology.MetricSpace.BoundedMetricTopologicallyEquivalent` -/

namespace MathlibExtTest.BoundedMetricTopologicallyEquivalent

open MathlibExt.Analysis.FunctionalAnalysis.BoundedMetricTopologicallyEquivalentWanted
open scoped Topology

-- Test section: the conclusion supplies every hypothesis of `MetricSpace.ofDistTopology`, so
-- `d / (1 + d)` is the distance of a metric space structure on `X` whose topology is,
-- definitionally, the topology of `d`. Both distances are written with their structure, since
-- inside `∃ m'` an unqualified `dist` would refer to the bound instance `m'`.
example {X : Type*} [m : MetricSpace X] :
    ∃ m' : MetricSpace X, (∀ x y : X, m'.dist x y = m.dist x y / (1 + m.dist x y)) ∧
      m'.toUniformSpace.toTopologicalSpace = m.toUniformSpace.toTopologicalSpace := by
  obtain ⟨⟨h0, hcomm, htri⟩, hball, hball'⟩ :=
    dist_div_one_add_dist_balls_equivalent (X := X) _ fun _ _ => rfl
  -- The open sets of `d` are the sets that contain a `δ`-ball around each of their points.
  have H (s : Set X) :
      IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y / (1 + dist x y) < ε → y ∈ s := by
    rw [Metric.isOpen_iff]
    refine forall₂_congr fun x _ => ⟨fun ⟨ε, hε, hs⟩ => ?_, fun ⟨ε, hε, hs⟩ => ?_⟩
    · obtain ⟨η, hη, h⟩ := hball' x ε hε
      exact ⟨η, hη, fun y hy => hs (h hy)⟩
    · obtain ⟨η, hη, h⟩ := hball x ε hε
      exact ⟨η, hη, fun y hy => hs y (h hy)⟩
  exact ⟨MetricSpace.ofDistTopology (fun x y => dist x y / (1 + dist x y))
    (fun x => (h0 x x).2 rfl) hcomm htri H fun x y => (h0 x y).1, fun _ _ => rfl, rfl⟩

-- Test section: the `δ`-balls around `x` form a basis of the neighbourhoods of `x` for the
-- topology of `d`.
example {X : Type*} [MetricSpace X] (x : X) :
    (𝓝 x).HasBasis (fun η : ℝ => 0 < η) fun η => {y : X | dist x y / (1 + dist x y) < η} := by
  obtain ⟨-, hball, hball'⟩ := dist_div_one_add_dist_balls_equivalent (X := X) _ fun _ _ => rfl
  exact Metric.nhds_basis_ball.to_hasBasis (hball' x) (hball x)

-- Test section: `δ` need only agree pointwise with `d / (1 + d)`; here it is given by the formula
-- `1 - 1 / (1 + d)`, and the theorem yields its triangle inequality.
example {X : Type*} [MetricSpace X] (x y z : X) :
    1 - 1 / (1 + dist x z) ≤ (1 - 1 / (1 + dist x y)) + (1 - 1 / (1 + dist y z)) := by
  refine (dist_div_one_add_dist_balls_equivalent (fun a b : X => 1 - 1 / (1 + dist a b))
    fun a b => ?_).1.2.2 x y z
  have h : (1 : ℝ) + dist a b ≠ 0 := by positivity
  field_simp
  ring

end MathlibExtTest.BoundedMetricTopologicallyEquivalent
