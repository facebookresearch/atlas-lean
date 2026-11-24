/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ReducedResiduePrimeBound
import Mathlib.Tactic.IntervalCases

open MetaMathlibExt

-- The non-squarefree modulus is allowed, and the progression 1, 5 attains the bound.
example : longestAPLengthWithDiff 0 9 4 = 2 := by
  apply le_antisymm
  · exact longestAPLengthWithDiff_le_prime_sub_one 0 (n := 9) (d := 4) (p := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · unfold longestAPLengthWithDiff
    refine le_csSup ⟨9, fun s ⟨b, h⟩ => apLength_le (by decide : 0 < 4) h⟩ ⟨1, ?_⟩
    intro i hi
    interval_cases i <;> decide +kernel

example : longestAPLengthWithDiff (-3) 6 1 ≤ 1 :=
  longestAPLengthWithDiff_le_prime_sub_one (-3) (n := 6) (d := 1) (p := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
