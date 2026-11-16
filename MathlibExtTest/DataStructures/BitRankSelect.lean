/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.DataStructures.BitRankSelect

@[expose] public section

/-- The first one in `[false, true]` sits at index 1. -/
example : bselect [false, true] 0 = some 1 := rfl

end
