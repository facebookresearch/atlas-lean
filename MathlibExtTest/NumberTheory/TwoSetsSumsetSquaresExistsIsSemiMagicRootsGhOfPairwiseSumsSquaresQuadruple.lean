/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.TwoSetsSumsetSquaresExistsIsSemiMagicRootsGhOfPairwiseSumsSquaresQuadruple
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Defs
import MathlibExt.NumberTheory.TwoSetsSumsetSquaresQuintuple
import MathlibExt.NumberTheory.TwoSetsSumsetSquaresTriple

/-! # Tests for quadruple extensions from two further semi-magic squares -/

namespace MathlibExtTest.NumberTheory.TwoSetsSumsetSquaresExistsIsSemiMagicRootsGhOfPairwiseSumsSquaresQuadruple

open MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

-- A zero semi-magic square extended by `9` and `16`: the new roots square to `25` and `9`.
example : ∃ g : Fin 3 → Fin 3 → ℤ,
    IsSemiMagicRoots g ∧ g 0 0 ^ 2 = 25 ∧ g 0 1 ^ 2 = 0 ∧ g 0 2 ^ 2 = 0 ∧
      g 1 0 ^ 2 = 0 ∧ g 1 1 ^ 2 = 9 ∧ g 2 0 ^ 2 = 0 := by
  have he : IsSemiMagicRoots (fun _ _ => (0 : ℤ)) := ⟨0, by decide⟩
  have hlit : PairwiseSumsSquares ![0, 0, 0, (9 : ℤ)] ![0, 0, 0, (16 : ℤ)] := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val]
    case «0».«3» => exact ⟨4, by norm_num⟩
    case «1».«3» => exact ⟨4, by norm_num⟩
    case «2».«3» => exact ⟨4, by norm_num⟩
    case «3».«0» => exact ⟨3, by norm_num⟩
    case «3».«1» => exact ⟨3, by norm_num⟩
    case «3».«2» => exact ⟨3, by norm_num⟩
    case «3».«3» => exact ⟨5, by norm_num⟩
  obtain ⟨g, _, hg, _, h01, h02, h10, h20, _, _, _, _, ha4, hb4⟩ :=
    exists_isSemiMagicRoots_gh_of_pairwiseSumsSquares_quadruple (fun _ _ => 0) he 9 16 hlit
  have hg00 : g 0 0 ^ 2 = 25 := by linear_combination -hb4 - ha4
  have hg01 : g 0 1 ^ 2 = 0 := by simpa using h01.symm
  have hg02 : g 0 2 ^ 2 = 0 := by simpa using h02.symm
  have hg10 : g 1 0 ^ 2 = 0 := by simpa using h10.symm
  have hg11 : g 1 1 ^ 2 = 9 := ha4.symm
  have hg20 : g 2 0 ^ 2 = 0 := by simpa using h20.symm
  exact ⟨g, hg, hg00, hg01, hg02, hg10, hg11, hg20⟩

-- In the same example the common row and column sum of `g` is `25`.
example : ∃ S : ℤ, S = 25 ∧ ∃ g : Fin 3 → Fin 3 → ℤ,
    (∀ i : Fin 3, ∑ j : Fin 3, (g i j) ^ 2 = S) ∧
      ∀ j : Fin 3, ∑ i : Fin 3, (g i j) ^ 2 = S := by
  have he : IsSemiMagicRoots (fun _ _ => (0 : ℤ)) := ⟨0, by decide⟩
  have hlit : PairwiseSumsSquares ![0, 0, 0, (9 : ℤ)] ![0, 0, 0, (16 : ℤ)] := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val]
    case «0».«3» => exact ⟨4, by norm_num⟩
    case «1».«3» => exact ⟨4, by norm_num⟩
    case «2».«3» => exact ⟨4, by norm_num⟩
    case «3».«0» => exact ⟨3, by norm_num⟩
    case «3».«1» => exact ⟨3, by norm_num⟩
    case «3».«2» => exact ⟨3, by norm_num⟩
    case «3».«3» => exact ⟨5, by norm_num⟩
  obtain ⟨g, _, hg, _, h01, h02, _, _, _, _, _, _, ha4, hb4⟩ :=
    exists_isSemiMagicRoots_gh_of_pairwiseSumsSquares_quadruple (fun _ _ => 0) he 9 16 hlit
  obtain ⟨S, hrow, hcol⟩ := hg
  have hg00 : g 0 0 ^ 2 = 25 := by linear_combination -hb4 - ha4
  have hg01 : g 0 1 ^ 2 = 0 := by simpa using h01.symm
  have hg02 : g 0 2 ^ 2 = 0 := by simpa using h02.symm
  have hS : S = 25 := by
    have h0 := hrow 0
    simpa [Fin.sum_univ_three, hg00, hg01, hg02] using h0.symm
  exact ⟨S, hS, g, hrow, hcol⟩

end MathlibExtTest.NumberTheory.TwoSetsSumsetSquaresExistsIsSemiMagicRootsGhOfPairwiseSumsSquaresQuadruple
