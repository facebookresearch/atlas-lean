/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoSetsSumsetSquaresPairwiseSumsSquaresTripleFamily31
import Mathlib.Tactic.NormNum

/-! # Tests for `TwoSetsSumsetSquaresPairwiseSumsSquaresTripleFamily31` -/

namespace MathlibExtTest.NumberTheory.TwoSetsSumsetSquaresPairwiseSumsSquaresTripleFamily31

open MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

-- Family (3.1) at `p = 5`, `q = 3`, `r = 2`, `s = 1`: all entries but the first are nonzero.
example : PairwiseSumsSquares ![0, 480, 165] ![196, 4, (676 : ℤ)] := by
  have h := pairwiseSumsSquares_triple_family31 5 3 2 1
  norm_num at h
  exact h

-- At `p = 1`, `q = 2`, `r = 3`, `s = 4` the factor `p - q - r + s` vanishes, so `a₃ = 0`.
example : PairwiseSumsSquares ![0, 384, 0] ![100, 16, (400 : ℤ)] := by
  have h := pairwiseSumsSquares_triple_family31 1 2 3 4
  norm_num at h
  exact h

end MathlibExtTest.NumberTheory.TwoSetsSumsetSquaresPairwiseSumsSquaresTripleFamily31
