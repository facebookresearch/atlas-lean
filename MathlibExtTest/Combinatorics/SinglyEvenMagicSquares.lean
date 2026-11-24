/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SinglyEvenMagicSquares
import Mathlib.Tactic.FinCases

open MetaMathlibExt

namespace MathlibExtTest.SinglyEvenMagicSquares

private def loShu : Matrix (Fin 3) (Fin 3) ℕ := !![7, 0, 5; 2, 4, 6; 3, 8, 1]

private def outerDigits : Matrix (Fin 3) (Fin 3) ℕ := !![3, 0, 0; 0, 3, 0; 3, 0, 0]

/-- The first admissible order, with Lo Shu on the left and its transpose on the right. -/
example : IsReducedMagicSquare !![34, 0, 5, 25, 20, 21;
                                  2, 31, 6, 18, 22, 26;
                                  30, 8, 1, 23, 24, 19;
                                  7, 27, 32, 16, 11, 12;
                                  29, 4, 33, 9, 13, 17;
                                  3, 35, 28, 14, 15, 10] := by
  have hT : IsReducedMagicSquare loShu.transpose := by
    refine ⟨⟨12, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      first | decide | (intro i j; fin_cases i <;> fin_cases j <;> decide)
  have h := isReducedMagicSquare_extendedStrachey 1 outerDigits (fun _ _ => 1) loShu
    loShu.transpose (by intro i j; fin_cases i <;> fin_cases j <;> decide)
    (by decide) (by decide) (by decide) (fun _ _ => Or.inl rfl) (by decide) (by decide) (by decide)
    isReducedMagicSquare_loShu hT
  convert h using 1
  decide

end MathlibExtTest.SinglyEvenMagicSquares
