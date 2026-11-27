/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Normal subgroup given by the identity component

In a topological group, the connected component of the identity is a subgroup stable under
conjugation by every group element. It is therefore a normal subgroup.

No compactness, separation or commutativity is assumed.
-/

@[expose] public section

namespace Subgroup

universe u

/-- **Identity component is normal in a topological group.** For every topological group `G`,
`connectedComponentOfOne G` is a normal subgroup: conjugation preserves the connected
component of the identity. -/
theorem connectedComponentOfOne_normal
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (connectedComponentOfOne G).Normal := by
  constructor
  intro n hn g
  change g * n * g⁻¹ ∈ connectedComponent (1 : G)
  have hn' : n ∈ connectedComponent (1 : G) := hn
  have hconj :
      g * n * g⁻¹ ∈ connectedComponent (g * (1 : G) * g⁻¹) :=
    (IsTopologicalGroup.continuous_conj g).mapsTo_connectedComponent
      (1 : G) hn'
  have hfix : g * (1 : G) * g⁻¹ = 1 := by
    simp
  simpa only [hfix] using hconj

end Subgroup
