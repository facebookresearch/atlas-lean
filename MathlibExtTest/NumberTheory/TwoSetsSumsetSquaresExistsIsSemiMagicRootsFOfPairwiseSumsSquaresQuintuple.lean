/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.TwoSetsSumsetSquaresExistsIsSemiMagicRootsFOfPairwiseSumsSquaresQuintuple
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for quintuple extensions from a second semi-magic square

The zero matrix admits extensions with prescribed squared entries one and four.

## References

* Ajai Choudhry, "Two Sets of Integers Such That All Elements of the Sumset of the Two Sets
  Are Perfect Squares", *INTEGERS* 26 (2026), Article A66,
  <https://math.colgate.edu/~integers/aa66/aa66.pdf>, Lemma 2.
-/

namespace MathlibExtTest.NumberTheory
namespace TwoSetsSumsetSquaresExistsIsSemiMagicRootsFOfPairwiseSumsSquaresQuintuple

open MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

example : ∃ f : Fin 3 → Fin 3 → ℤ,
    IsSemiMagicRoots f ∧
      f 0 0 ^ 2 = 0 ∧ f 1 1 ^ 2 = 0 ∧ f 2 2 ^ 2 = 0 ∧
        f 0 2 ^ 2 = 1 ∧ f 2 0 ^ 2 = 4 := by
  have he : IsSemiMagicRoots (fun _ _ ↦ 0) := by
    refine ⟨0, ?_, ?_⟩ <;> intro i <;> simp
  have h : PairwiseSumsSquares
      ![(0 : ℤ), 0, 0, 1, 4] ![0, 0, 0] := by
    intro i j
    refine ⟨(![0, 0, 0, 1, 2] : Fin 5 → ℤ) i, ?_⟩
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.cons_val]
  obtain ⟨f, hf, h00, h11, h22, h02, h20⟩ :=
    exists_isSemiMagicRoots_f_of_pairwiseSumsSquares_quintuple (fun _ _ ↦ 0) he 1 4
      (by simpa using h)
  exact ⟨f, hf, h00.symm, h11.symm, h22.symm, h02.symm, h20.symm⟩

end TwoSetsSumsetSquaresExistsIsSemiMagicRootsFOfPairwiseSumsSquaresQuintuple
end MathlibExtTest.NumberTheory
