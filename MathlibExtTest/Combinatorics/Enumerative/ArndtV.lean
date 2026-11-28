/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ArndtV

/-! # Tests for the pairwise map V on compositions -/

open MetaMathlibExt

example : arndtV [] = [] := rfl

example (n : ℕ) (hn : 0 < n) :
    ∃ σ : Equiv.Perm (Composition n), σ (Composition.single n hn) = Composition.ones n := by
  obtain ⟨σ, hσ⟩ := exists_perm_composition_blocks_eq_arndtV n
  exact ⟨σ, Composition.ext (hσ (Composition.single n hn))⟩

-- The equal pair gives an even part. The next two pairs have odd and even differences,
-- and the final unpaired part contributes the trailing ones.
example : arndtV [2, 2, 1, 2, 2, 4, 3] = [4, 3, 1, 1, 1, 3, 1, 1, 1] := by
  decide
