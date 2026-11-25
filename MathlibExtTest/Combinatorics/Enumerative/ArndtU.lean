/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ArndtU

/-! # Tests for the pairwise map U on compositions -/

open MetaMathlibExt

example : arndtU [] = [] := rfl

-- A single part is an unpaired final part, so it becomes a run of ones.
example (n : ℕ) (hn : 0 < n) :
    ∃ σ : Equiv.Perm (Composition n), σ (Composition.single n hn) = Composition.ones n := by
  obtain ⟨σ, hσ⟩ := exists_perm_composition_blocks_eq_arndtU n
  exact ⟨σ, Composition.ext (hσ (Composition.single n hn))⟩

-- The first pair decreases and gives an odd part, the next two pairs (equal parts, then a
-- difference of three) give even parts, and the final unpaired part gives the trailing ones.
example : arndtU [3, 1, 2, 2, 2, 5, 3] = [1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1] := by
  decide

-- An even and an odd difference `b - a` give the same terminating part `2k = 4`; the run length
-- `2a - 2` or `2a - 1` tells them apart.
example : arndtU [2, 4] = [1, 1, 4] ∧ arndtU [2, 5] = [1, 1, 1, 4] := by
  decide

-- The images of the sixteen compositions of `5` are again the sixteen compositions of `5`.
example :
    [[5], [2, 3], [1, 4], [4, 1], [2, 2, 1], [1, 3, 1], [3, 2], [2, 1, 1, 1], [3, 1, 1],
        [1, 2, 2], [2, 1, 2], [1, 2, 1, 1], [1, 1, 3], [1, 1, 2, 1], [1, 1, 1, 2],
        [1, 1, 1, 1, 1]].map arndtU =
      [[1, 1, 1, 1, 1], [1, 1, 1, 2], [1, 4], [1, 1, 3], [1, 1, 2, 1], [4, 1], [5], [3, 2],
        [1, 3, 1], [1, 2, 1, 1], [3, 1, 1], [1, 2, 2], [2, 1, 1, 1], [2, 3], [2, 1, 2],
        [2, 2, 1]] := by
  decide

-- On compositions the map is onto and one-to-one.
example (n : ℕ) (d : Composition n) : ∃ c : Composition n, arndtU c.blocks = d.blocks := by
  obtain ⟨σ, hσ⟩ := exists_perm_composition_blocks_eq_arndtU n
  exact ⟨σ.symm d, by rw [← hσ, Equiv.apply_symm_apply]⟩

example (n : ℕ) (c d : Composition n) (h : arndtU c.blocks = arndtU d.blocks) : c = d := by
  obtain ⟨σ, hσ⟩ := exists_perm_composition_blocks_eq_arndtU n
  exact σ.injective (Composition.ext (by rw [hσ, hσ, h]))

-- With a zero part the exponent `a + b - 2k` truncates: the map is not one-to-one on lists of
-- natural numbers and does not preserve their sum.
example : arndtU [0, 0] = [2] ∧ arndtU [1, 1] = [2] := by
  decide
