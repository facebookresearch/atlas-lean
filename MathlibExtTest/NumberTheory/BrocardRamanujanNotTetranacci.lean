/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BrocardRamanujanNotTetranacci

open MetaMathlibExt

-- The theorem applied at arbitrary indices.
example (m n : ℕ) : Nat.factorial m + 1 ≠ tetranacci n ^ 2 :=
  brocardRamanujan_not_tetranacci m n

-- The factorial-plus-one values at the known Brocard indices are not
-- Tetranacci squares: 5, 11 and 71 are not Tetranacci numbers.
example : Nat.factorial 4 + 1 ≠ tetranacci 3 ^ 2 :=
  brocardRamanujan_not_tetranacci 4 3

example : Nat.factorial 5 + 1 ≠ tetranacci 4 ^ 2 :=
  brocardRamanujan_not_tetranacci 5 4

example : ¬ ∃ m n : ℕ, Nat.factorial m + 1 = tetranacci n ^ 2 := by
  rintro ⟨m, n, h⟩
  exact brocardRamanujan_not_tetranacci m n h

#print axioms MetaMathlibExt.brocardRamanujan_not_tetranacci
