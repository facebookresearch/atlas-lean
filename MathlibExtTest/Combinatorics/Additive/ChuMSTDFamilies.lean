/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ChuMSTDFamilies

open MetaMathlibExt
open scoped Pointwise

-- At the largest allowed indices, both the terminal block and the grid endpoints are needed.
example : 33 ∈ chuFamilyKLT 1 1 1 + chuFamilyKLT 1 1 1 ∧
    34 ∈ chuFamilyKLT 1 1 1 + chuFamilyKLT 1 1 1 ∧
    31 ∈ chuFamilyKLT 1 1 1 + chuFamilyKLT 1 1 1 := by
  have h := chuFamilyKLT_mem_add (k := 1) (l := 1) (t := 1) (by decide) (by decide) (by decide)
  have h₈ := h.1 8 (by decide)
  exact ⟨h₈.1, h₈.2, h.2 7 (by decide)⟩

-- The same proposition is visible at its zero index.
example : 1 ∈ chuFamilyKLT 1 1 1 + chuFamilyKLT 1 1 1 :=
  ((chuFamilyKLT_mem_add (k := 1) (l := 1) (t := 1) (by decide) (by decide)
    (by decide)).1 0 (by decide)).1

-- A zero gap repeats the previous partial sum, even when the start is negative.
example : setOfConsecutiveDifferences (-1) [0, 2] = {-1, 1} := by decide

example : chuBlock 0 = [1, 3] := rfl

-- With no repeated blocks, only the fixed tail contributes gaps.
example (k l : ℕ) : chuFamilyKLT k l 0 = {0, 1, 2, 4, 5} := rfl

-- Two copies of the block [1, 4, 3] contribute 16 to each repeated segment.
example :
    (Finset.Icc 1 2).image (fun j =>
      ([1, 1] ++ (List.replicate j
        (2 :: (List.replicate 2 (chuBlock 1)).flatten ++ [1, 1])).flatten).sum) = {22, 42} :=
  (chuFamilyKLT_run_sums_R1_eq_R3 1 2 2).trans (by decide)

-- The first and last indexed starts in the last outer block.
example : (32 : ℤ) ∈ chuFamilyKLT 2 2 2 := by
  simpa using chuFamilyKLT_mem_block_starts (k := 2) (l := 2) (t := 2)
    (by decide) (by decide) (by decide) 0 1 (by decide) (by decide)

example : (56 : ℤ) ∈ chuFamilyKLT 2 2 2 := by
  simpa using chuFamilyKLT_mem_block_starts (k := 2) (l := 2) (t := 2)
    (by decide) (by decide) (by decide) 2 1 (by decide) (by decide)
