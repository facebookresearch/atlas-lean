/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.DataStructures.EulerTour

@[expose] public section

/-- A single node tours to one entry. -/
example : (RTree.node 7 []).tour 0 = [(7, 0)] := by simp [RTree.tour]

/-- A root with one leaf child tours to three entries. -/
example : (RTree.node 1 [RTree.node 2 []]).tour 0 = [(1, 0), (2, 1), (1, 0)] := by simp [RTree.tour]

end
