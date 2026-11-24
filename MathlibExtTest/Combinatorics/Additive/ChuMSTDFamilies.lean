/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ChuMSTDFamilies

open MetaMathlibExt

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
