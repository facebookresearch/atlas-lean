/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.KNaplesParkingInt

open MetaMathlibExt

-- The backward search on the integer line can cross zero.
example : naplesSpotInt 2 [0, 1] 1 = -1 := by decide

-- When the backward search is exhausted, the car skips the occupied forward spots.
example : naplesParkInt 1 [1, 2, 3] [2] = [4, 1, 2, 3] := by decide

-- Increasing k from zero can attain both endpoints of the bound in the same run.
example : naplesParkInt 0 [] [1, 1, 3, 4] = [4, 3, 2, 1] ∧
    naplesParkInt 1 [] [1, 1, 3, 4] = [4, 3, 0, 1] := by decide

example : ∀ s ∈ naplesParkInt 1 [] [1, 1, 3, 4], 0 ≤ s ∧ s ≤ 4 := by
  apply naplesParkInt_succ_mem_Icc (k := 0) (n := 4) rfl
  · decide
  · intro s
    have h : naplesParkInt 0 [] [1, 1, 3, 4] = [4, 3, 2, 1] := by decide
    rw [h]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
