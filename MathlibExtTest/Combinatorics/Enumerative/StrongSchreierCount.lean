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

-- With one element, only the singleton {4} contributes, matching the one-part composition [6].
example : compositionMinPartExactCount 6 3 1 = 1 := by
  rw [← strongSchreierCardCount_eq 1 4 2 (by decide) (by decide)]
  decide

-- A 1-strong Schreier set with three elements has all of them at least 3, so none has maximum 4;
-- likewise no composition of five has three parts that are all at least two.
example : compositionMinPartExactCount 5 2 3 = 0 := by
  rw [← strongSchreierCardCount_eq 3 4 1 (by decide) (by decide)]
  decide

-- The sets {2, 5}, {3, 5} and {4, 5} match the compositions [2, 4], [3, 3] and [4, 2] of six.
example : compositionMinPartExactCount 6 2 2 = 3 := by
  rw [← strongSchreierCardCount_eq 2 5 1 (by decide) (by decide)]
  decide
