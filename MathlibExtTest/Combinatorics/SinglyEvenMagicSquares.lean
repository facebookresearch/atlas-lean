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

private def refSymmetricSquare : Matrix (Fin 6) (Fin 6) ℕ :=
  !![34, 0, 5, 23, 18, 25;
     2, 31, 6, 24, 22, 20;
     28, 8, 3, 21, 26, 19;
     7, 27, 32, 14, 9, 16;
     33, 4, 29, 11, 13, 15;
     1, 35, 30, 12, 17, 10]

/-- In order six the two flips differ on the middle row of Lo Shu. Check every entry
of the resulting square and its horizontal reflection identity. -/
example : IsReducedMagicSquare refSymmetricSquare ∧
    ∀ i j, refSymmetricSquare i j + refSymmetricSquare i.rev j = 35 := by
  have h := isReducedMagicSquare_refSymmetric_strachey 1 outerDigits (fun _ _ => 1) loShu
    (by intro i j; fin_cases i <;> fin_cases j <;> decide)
    (by decide) (by decide) (by decide) (fun _ _ => Or.inl rfl) (by decide) (by decide) (by decide)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide)
    (by decide) (by decide) (by decide) isReducedMagicSquare_loShu
    (by intro i j; fin_cases i <;> fin_cases j <;> decide)
  let P (T : Matrix (Fin 6) (Fin 6) ℕ) := IsReducedMagicSquare T ∧ ∀ i j, T i j + T i.rev j = 35
  have transfer {T : Matrix (Fin 6) (Fin 6) ℕ} (hT : P T) (heq : T = refSymmetricSquare) :
      P refSymmetricSquare := heq ▸ hT
  exact transfer h (by decide)

example : (∑ j, refSymmetricSquare 0 j) = 105 := by decide

end MathlibExtTest.SinglyEvenMagicSquares
