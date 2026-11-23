/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ReducedResidueLongestAP
import Mathlib.Tactic.IntervalCases

open MetaMathlibExt

-- The progression 1, 5 attains the bound for a composite squarefree modulus.
example : longestAPLengthWithDiff 0 6 4 = 2 := by
  apply le_antisymm
  · exact (longestAPLengthWithDiff_le_gpf_sub_one_of_squarefree 0
      (n := 6) (d := 4) (by decide) (by decide) (by decide +kernel)).trans (by decide +kernel)
  · unfold longestAPLengthWithDiff
    refine le_csSup ⟨6, fun s ⟨b, h⟩ => apLength_le (by decide : 0 < 4) h⟩ ?_
    refine ⟨1, fun i hi => ?_⟩
    interval_cases i <;> decide

-- At the smallest allowed modulus a step equal to the modulus leaves only the term -1.
example : longestAPLengthWithDiff (-2) 2 2 = 1 := by
  apply le_antisymm
  · exact (longestAPLengthWithDiff_le_gpf_sub_one_of_squarefree (-2)
      (n := 2) (d := 2) (by decide) (by decide) Nat.squarefree_two).trans (by decide +kernel)
  · unfold longestAPLengthWithDiff
    refine le_csSup ⟨2, fun s ⟨b, h⟩ => apLength_le (by decide : 0 < 2) h⟩ ?_
    refine ⟨-1, fun i hi => ?_⟩
    interval_cases i
    decide
