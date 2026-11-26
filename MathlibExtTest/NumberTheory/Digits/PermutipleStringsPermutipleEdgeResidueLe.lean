/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.PermutipleStringsPermutipleEdgeResidueLe

/-! # Tests for `MathlibExt.NumberTheory.Digits.PermutipleStringsPermutipleEdgeResidueLe` -/

namespace MathlibExtTest.NumberTheory.Digits.PermutipleStringsPermutipleEdgeResidueLe

open MetaMathlibExt

-- The units digit of `87912 = 4 * 21978` gives residue `0`.
example : ((2 : ℤ) + 6 * 8) % 10 ≤ 3 :=
  permutiple_edge_residue_le 4 10 (by decide) _ _ isPermutiple_87912 0

-- The middle digit `9` of `87912` gives the maximal residue `3`.
example : ((9 : ℤ) + 6 * 9) % 10 ≤ 3 :=
  permutiple_edge_residue_le 4 10 (by decide) _ _ isPermutiple_87912 2

-- With base one all digits vanish, so the residue is `0`.
example : ((0 : ℤ) + ((1 : ℤ) - 5) * 0) % (1 : ℕ) ≤ (5 : ℤ) - 1 := by
  have hp : IsPermutiple 5 1 (k := 0) (fun _ => 0) 1 := by
    unfold IsPermutiple
    decide
  exact permutiple_edge_residue_le 5 1 (by decide) _ _ hp 0

-- Every digit pair of a permutiple is an edge of the mother graph.
example (n b : ℕ) (hn : 1 ≤ n) {k : ℕ} (d : Fin (k + 1) → ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ) (j : Fin (k + 1)) :
    IsMotherGraphEdge n b (d j) (d (σ j)) :=
  ⟨hp.1 j, hp.1 (σ j), permutiple_edge_residue_le n b hn d σ hp j⟩

end MathlibExtTest.NumberTheory.Digits.PermutipleStringsPermutipleEdgeResidueLe
