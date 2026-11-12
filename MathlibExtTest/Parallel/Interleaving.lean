/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Parallel.Interleaving

@[expose] public section

/-- Boundary check: running a trace of writes ends at the last
write. -/
example : runTrace 0 [(0, RegOp.write 3), (1, RegOp.read),
    (0, RegOp.write 5)] = 5 := rfl

/-- Boundary check: projecting an interleaving onto thread 0
recovers thread 0's operations. -/
example : project 0 [(0, RegOp.write 3), (1, RegOp.read),
    (0, RegOp.read)] = [RegOp.write 3, RegOp.read] := rfl
