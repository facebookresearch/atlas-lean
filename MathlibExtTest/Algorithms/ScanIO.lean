/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.ScanIO

@[expose] public section

/-- Scanning five items in blocks of two costs three transfers. -/
example : blocks 2 [1, 2, 3, 4, 5] = 3 :=
  blocks_length 2 [1, 2, 3, 4, 5] (by decide)

end
