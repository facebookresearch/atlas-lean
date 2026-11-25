/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GijswijtSequence

open MetaMathlibExt

-- The empty suffix supplies the lower bound even when the whole word is empty.
example (S : List ℕ) : 1 ≤ curlingNumber S := by
  rw [← curlingNumber_nil]
  exact curlingNumber_le_of_suffix List.nil_suffix

-- Two copies of a two-letter block still witness a lower bound after any prefix.
example (P : List ℕ) : 2 ≤ curlingNumber (P ++ [1, 2, 1, 2]) :=
  calc
    2 = curlingNumber [1, 2, 1, 2] := by decide
    _ ≤ curlingNumber (P ++ [1, 2, 1, 2]) := curlingNumber_le_of_suffix ⟨P, rfl⟩

-- Prepending one more copy can strictly increase the curling number.
example : curlingNumber [1, 2, 1, 2] < curlingNumber [1, 2, 1, 2, 1, 2] := by decide
