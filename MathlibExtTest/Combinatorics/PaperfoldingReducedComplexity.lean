/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.PaperfoldingReducedComplexity

open InfiniteWord MathlibExt.Combinatorics.ReducedComplexitiesWanted

example : rhoRed paperfoldingSeq 2 = 4 :=
  rhoRed_paperfolding_two_mul 1 (hn := by decide)

-- These length-four factors exhibit both reduction lengths for each first letter.
example :
    [1, 3, 5, 11].map (fun i => redWord (factorList paperfoldingSeq 4 i)) =
      [[false, true, false], [false, true], [true, false], [true, false, true]] := by
  decide +kernel
