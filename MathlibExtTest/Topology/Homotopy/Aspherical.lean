/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Keith Mills
-/
module

public import MathlibExt.Topology.Homotopy.Aspherical

@[expose] public section

namespace MathlibExtTest.Topology.Homotopy.Aspherical

open MetaMathlibExt

-- Topology 368: Aspherical

/-
An aspherical space is path-connected.
Includes the stipulation that the space is nonempty since otherwise
nothing makes sense. Note that HomotopyGroup is the thing that does not
make sense for empty spaces since homotopy groups are based sets.
-/

theorem aspherical_implies_path_connected (X : Type*) [TopologicalSpace X] [Nonempty X]
  (asph_X: IsAspherical X) : PathConnectedSpace X := by
    rw [pathConnectedSpace_iff_zerothHomotopy]
    let x : X := Classical.ofNonempty
    rw [← (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).nonempty_congr,
      ← (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).subsingleton_congr]
    constructor
    · exact instNonemptyOfInhabited
    · apply asph_X
      trivial

end MathlibExtTest.Topology.Homotopy.Aspherical

end
