/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.BlockArndtGeneratingFunction

open MetaMathlibExt PowerSeries

-- With one part per block, the series counts unrestricted compositions, including the empty one.
example : bivariateCountGF (blockArndtCompositionCount 1) *
    (1 - X - C Polynomial.X * X) = 1 - X := by
  simpa using bivariateCountGF_blockArndt 1 (by decide)

-- At minimum weight the full block is (3, 2, 1) and the remaining part is 1.
example : blockArndtCompositionCount 3 7 4 = 1 := by decide

example : blockArndtCompositionCount 3 6 4 = 0 := by decide
