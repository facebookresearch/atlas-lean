/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.PaperfoldingReducedComplexity

open InfiniteWord MathlibExt.Combinatorics.ReducedComplexitiesWanted

-- A singleton has one run, with no alternation hypothesis to check.
example (a : Bool) : (redWord (List.ofFn (fun _ : Fin 1 => a))).length = 1 :=
  redWord_length_alternating_even 0 _ (fun i => Fin.elim0 i)

-- The middle letter of the first triple agrees with its left endpoint, and that of the
-- second triple agrees with its right endpoint.
example : (redWord (List.ofFn ![false, false, true, false, false])).length = 3 :=
  redWord_length_alternating_even 2 _ (by decide)

example : rhoRed paperfoldingSeq 2 = 4 :=
  rhoRed_paperfolding_two_mul 1 (hn := by decide)

-- These length-four factors exhibit both reduction lengths for each first letter.
example :
    [1, 3, 5, 11].map (fun i => redWord (factorList paperfoldingSeq 4 i)) =
      [[false, true, false], [false, true], [true, false], [true, false, true]] := by
  decide +kernel

-- The smallest positive even length has one- and two-letter reductions.
example : rhoAbRed paperfoldingSeq 2 = 3 :=
  rhoAbRed_paperfolding_even 2 (by decide) ⟨1, rfl⟩

-- At length four the shorter, rather than the longer, reductions have even length.
example : rhoAbRed paperfoldingSeq 4 = 3 :=
  rhoAbRed_paperfolding_even 4 (by decide) ⟨2, rfl⟩
