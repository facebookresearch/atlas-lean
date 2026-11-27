/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RoundedQuotientLatticeDisc

namespace MetaMathlibExt

-- At radius zero, only the origin is counted.
example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ 2 * (0 : ℤ)} = 1 := by
  have h : 4 * roundQuotientOddCount 0 + 4 * 0 + 1 = 1 := by decide +kernel
  exact (card_lattice_disc_two_mul (n := 0)).trans h

-- The four points (±1, ±1) on the boundary are included in the nine points.
example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ 2 * (1 : ℤ)} = 9 := by
  have h : 4 * roundQuotientOddCount 1 + 4 * 1 + 1 = 9 := by decide +kernel
  exact (card_lattice_disc_two_mul (n := 1)).trans h

-- Dent and Shor, Example 18: the closed disc of radius 6 contains 113 points.
example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ 2 * (18 : ℤ)} = 113 := by
  have h : 4 * roundQuotientOddCount 18 + 4 * 18 + 1 = 113 := by decide +kernel
  exact (card_lattice_disc_two_mul (n := 18)).trans h

end MetaMathlibExt
