/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoSetsSumsetSquaresPairwiseSumsSquaresQuintupleFamily41
import Mathlib.Tactic.NormNum

/-! # Tests for `TwoSetsSumsetSquaresPairwiseSumsSquaresQuintupleFamily41` -/

namespace MathlibExtTest.NumberTheory.TwoSetsSumsetSquaresPairwiseSumsSquaresQuintupleFamily41

open MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

-- Choudhry's numerical example, in the order given by the formulas in Equation (4.1).
example : PairwiseSumsSquares ![1674436, 13468900, 19404025, 198916, 532900]
    ![0, 3588000, (8527200 : ℚ)] := by
  have h := pairwiseSumsSquares_quintuple_family41 4 1 3 2 1 3 1
  norm_num at h
  exact h

-- A nonintegral specialization with `m = 0` and repeated entries in both families.
example : PairwiseSumsSquares ![0, 16, (81 / 16 : ℚ), 0, 16] ![0, 9, 9] := by
  have h := pairwiseSumsSquares_quintuple_family41 (1 / 2) 1 0 2 1 2 1
  norm_num at h
  exact h

end MathlibExtTest.NumberTheory.TwoSetsSumsetSquaresPairwiseSumsSquaresQuintupleFamily41
