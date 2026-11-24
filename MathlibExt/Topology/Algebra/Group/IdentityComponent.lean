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
# Normality of the identity component

The connected component of the identity in a topological group is a normal
subgroup.  This file packages the existing continuity and connected-component
APIs as a theorem, without registering a new global instance.
-/

@[expose] public section

namespace Subgroup

universe u

/-- The connected component of the identity is normal in every topological
group.  This is a theorem rather than a global instance, so consumers may
activate it only for the subgroup they own. -/
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
