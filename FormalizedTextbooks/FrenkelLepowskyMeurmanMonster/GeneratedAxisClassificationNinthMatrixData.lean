/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthDiagonalData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPairPhaseData

/-! Exact integer matrix data follow from all original pair and diagonal source certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Thirty-two times the expected full actual matrix, including its eight signed pair blocks. -/
def generatedNinthMatrixNumerator (i j : Fin 24) : ℤ :=
  if i = j then generatedNinthDiagonalNumerator i else
    if (min i.val j.val, max i.val j.val) ∈
      ([(0, 23), (6, 17), (10, 13), (14, 15)] : List (ℕ × ℕ)) then 2 else
      if (min i.val j.val, max i.val j.val) ∈
        ([(1, 16), (2, 4), (7, 22), (19, 21)] : List (ℕ × ℕ)) then -2 else 0

/-- The exact integer matrix is symmetric. -/
theorem generatedNinthMatrixNumerator_symmetric : ∀ i j : Fin 24,
    generatedNinthMatrixNumerator i j = generatedNinthMatrixNumerator j i := by
  decide +kernel

/-- Each original diagonal entry is the already certified finite diagonal numerator. -/
theorem generatedNinthMatrixNumerator_diagonal (i : Fin 24) :
    generatedNinthMatrixNumerator i i = generatedNinthDiagonalNumerator i := by
  simp only [generatedNinthMatrixNumerator, ite_true]

set_option maxRecDepth 20000 in
-- This combines the two preferred source signs for every ordered pair.
/-- Exterior triality's pair sum is exactly the original full-matrix off-diagonal numerator. -/
theorem generatedNinth_matrix_pair_certificate : ∀ a b : Fin 24, a < b →
    generatedNinthPairCoefficientNumerator (generatedNinthPairLookup 0 a b) +
      generatedNinthPairCoefficientNumerator (generatedNinthPairLookup 1 a b) =
        generatedNinthMatrixNumerator a b := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
