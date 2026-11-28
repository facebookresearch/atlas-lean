/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
import MathlibExt.Data.List.AdjacentInversion

/-! # Occurrence counts and the first adjacent descent -/

example : List.inversionCount ([2, 2, 1, 0] : List ℕ) = 5 := by decide
example : List.adjacentInversion ([2, 2, 1, 0] : List ℕ) =
    some ([2], 2, 1, [0]) := by decide
example : List.inversionCount ([2, 2] : List ℕ) = 0 := by decide
example : List.adjacentInversion ([2, 2] : List ℕ) = none := by decide
example : List.inversionCount ([3, 1, 2] : List ℕ) = 2 := by decide
example : List.adjacentInversion ([1, 3, 2] : List ℕ) =
    some ([1], 3, 2, []) := by decide
