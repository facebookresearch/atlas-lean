/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# Pulling a factor out of a remainder

For a natural product below the modulus, reducing either the product or just its right factor
before multiplying gives the same value.
-/

public section

namespace MetaMathlibExt

/--
**Pulling a factor out of a remainder.** Let $a$, $y$ and $C$ be natural numbers with $ay < C$.
Then $(ay) \bmod C = a \cdot (y \bmod C)$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 5.
-/
theorem mul_mod_eq_mul_mod_of_mul_lt
    (a y C : ℕ) (hbound : a * y < C) :
    (a * y) % C = a * (y % C) := by
  by_cases ha : a = 0
  · simp [ha]
  have hy : y < C := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left y (Nat.pos_of_ne_zero ha)) hbound
  rw [Nat.mod_eq_of_lt hbound, Nat.mod_eq_of_lt hy]

end MetaMathlibExt
