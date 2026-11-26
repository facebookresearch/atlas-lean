/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.TwoSetsSumsetSquaresTriple
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! # Tests for semi-magic roots of triples with square pairwise sums -/

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

-- A triple with a negative offset and zero pairwise sums: the semi-magic
-- square has entries `0`, `36`, `64` and `100` only.
example : ∃ e : Fin 3 → Fin 3 → ℤ,
    IsSemiMagicRoots e ∧
      e 0 0 ^ 2 = 0 ∧ e 0 1 ^ 2 = 36 ∧ e 0 2 ^ 2 = 64 ∧
        e 1 0 ^ 2 = 100 ∧ e 1 1 ^ 2 = 0 ∧ e 1 2 ^ 2 = 0 ∧
        e 2 0 ^ 2 = 0 ∧ e 2 1 ^ 2 = 64 ∧ e 2 2 ^ 2 = 36 := by
  have h := pairwiseSumsSquares_triple_family33 1 (-2) 2 1
  norm_num at h
  obtain ⟨e, he, h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ :=
    exists_isSemiMagicRoots_of_pairwiseSumsSquares_triple _ _ h
  exact ⟨e, he, by norm_num [h00], by norm_num [h01], by norm_num [h02],
    by norm_num [h10], by norm_num [h11], by norm_num [h12], by norm_num [h20],
    by norm_num [h21], by norm_num [h22]⟩

-- In the same example the common row and column sum is `100`.
example : ∃ S : ℤ, S = 100 ∧ ∃ e : Fin 3 → Fin 3 → ℤ,
    (∀ i : Fin 3, ∑ j : Fin 3, (e i j) ^ 2 = S) ∧
      ∀ j : Fin 3, ∑ i : Fin 3, (e i j) ^ 2 = S := by
  have h := pairwiseSumsSquares_triple_family33 1 (-2) 2 1
  norm_num at h
  obtain ⟨e, he, h00, h01, h02, -, -, -, -, -, -⟩ :=
    exists_isSemiMagicRoots_of_pairwiseSumsSquares_triple _ _ h
  obtain ⟨S, hrow, hcol⟩ := he
  have hS : S = 100 := by
    have h0 := hrow 0
    simp [Fin.sum_univ_three, h00, h01, h02] at h0
    omega
  exact ⟨S, hS, e, hrow, hcol⟩

-- Euler's matrix (2.10) at `(p, q, r, s) = (7, 3, 2, 1)`: the nine squares are distinct,
-- and the nonzero offsets have opposite signs.
example : PairwiseSumsSquares ![484, 1156, 1849] ![0, -480, (960 : ℤ)] := by
  let e : Fin 3 → Fin 3 → ℤ := ![![53, 26, -22], ![-2, 43, 46], ![34, -38, 37]]
  have he : IsSemiMagicRoots e := ⟨3969, by decide⟩
  have h := pairwiseSumsSquares_triple_of_isSemiMagicRoots e he
  norm_num [e] at h
  exact h

-- The construction allows a zero common sum and repeated values in both triples.
example : PairwiseSumsSquares ![0, 0, 0] ![0, 0, (0 : ℤ)] :=
  pairwiseSumsSquares_triple_of_isSemiMagicRoots (fun _ _ ↦ 0) ⟨0, by decide⟩

end MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted
