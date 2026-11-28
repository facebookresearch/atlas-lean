/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

/-!
# Compact generation of a Hausdorff classical CW space

The existing closed-cell weak topology and compactness of every closed
cell imply the stock compact-generation criterion. The actual topology
is retained; no replacement of the underlying space is made.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace Topology.CWComplex

/-- A Hausdorff classical CW space is compactly generated in its original
carrier universe, by the existing weak topology on compact closed cells. -/
public theorem uCompactlyGeneratedSpace_of_classicalCW
    (X : Type u) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    UCompactlyGeneratedSpace.{u} X := by
  apply compactlyGeneratedSpace_of_isClosed_of_t2
  intro S hS
  apply (Topology.CWComplex.closed (Set.univ : Set X) S (Set.subset_univ S)).mpr
  intro n j
  exact hS (Topology.CWComplex.closedCell n j)
    (Topology.CWComplex.isCompact_closedCell (C := (Set.univ : Set X)) (n := n) (i := j))

end Topology.CWComplex

end
