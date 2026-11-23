/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ReducedComplexities

open MathlibExt.Combinatorics.ReducedComplexitiesWanted

example : muWord [] = [] ∧ alternations [] = 0 := by decide

example (a : Bool) : alternations (muWord [a]) = 1 := by
  cases a <;> decide

-- Equal letters give an extra alternation between blocks; different letters give none.
example : alternations (muWord [true, true]) = 3 := by decide
example : alternations (muWord [true, false]) = 2 := by decide

example : muWord [false, true, true] = [false, true, true, false, true, false] := rfl

example : redWord [false, false, true, true, false] = [false, true, false] := by decide
example : (List.range 8).map paperfoldingSeq =
    [false, false, true, false, false, true, true, false] := by decide +kernel
