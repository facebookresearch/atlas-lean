/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.UlamWordsSierpinski

open MetaMathlibExt

-- The exceptional singleton is accepted without a membership witness.
example : IsUlamWord [true] :=
  (isUlamWord_ones_zeros_iff_mem_discreteSierpinski 1 1 (by decide) (by decide)).2 (Or.inl rfl)

-- Constant words of length greater than one give no point on the diagonal.
example : (4, 4) ∉ discreteSierpinski := by
  intro h
  have hw : IsUlamWord [true, true, true, true] :=
    (isUlamWord_ones_zeros_iff_mem_discreteSierpinski 4 4 (by decide) (by decide)).2 (Or.inr h)
  exact (by decide : ¬IsUlamWord [true, true, true, true]) hw

-- The third copy of stage one translates (3, 2) to (5, 4).
example : IsUlamWord [true, true, true, true, false] := by
  apply (isUlamWord_ones_zeros_iff_mem_discreteSierpinski 5 4 (by decide) (by decide)).2
  right
  apply Set.mem_iUnion.mpr
  refine ⟨2, ?_⟩
  change (5, 4) ∈ _ ∪ (fun p : ℕ × ℕ => (p.1 + 2 ^ 1, p.2 + 2 ^ 1)) '' discreteSierpinskiStage 1
  exact Or.inr ⟨(3, 2), by simp [discreteSierpinskiStage_one], rfl⟩

-- The two distinct endpoint cuts of 1100 leave a hole at (4, 2).
example : (4, 2) ∉ discreteSierpinski := by
  intro h
  have hw : IsUlamWord [true, true, false, false] :=
    (isUlamWord_ones_zeros_iff_mem_discreteSierpinski 4 2 (by decide) (by decide)).2 (Or.inr h)
  exact (by decide : ¬IsUlamWord [true, true, false, false]) hw

-- In the other direction an independently computed Ulam word gives a triangle point.
example : (5, 2) ∈ discreteSierpinski := by
  have h := (isUlamWord_ones_zeros_iff_mem_discreteSierpinski 5 2 (by decide) (by decide)).1
    (by decide)
  exact h.resolve_left (by decide)
