/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StrongSchreierCount

open MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

-- At the smallest allowed maximum, only the singleton contributes.
example : strongSchreierCount 1 5 = 1 := by decide

-- With no restriction on positive parts, all subsets containing the maximum contribute.
example : strongSchreierCount 4 0 = 8 := by decide

-- The five compositions of six with parts at least two include the boundary case [2, 2, 2].
example : compositionMinPartCount 6 2 = 5 := by
  rw [← strongSchreierCount_eq 5 1 (by decide)]
  decide
