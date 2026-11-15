/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.DecisionTree

@[expose] public section

/-- A single comparison has two leaves and depth one. -/
example : (DTree.node (DTree.leaf 0) (DTree.leaf 1)).leaves = 2 := rfl

/-- Its depth bound is attained. -/
example : (DTree.node (DTree.leaf 0) (DTree.leaf 1)).depth = 1 := rfl

end
