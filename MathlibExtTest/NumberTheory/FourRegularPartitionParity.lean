/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FourRegularPartitionParity

namespace MetaMathlibExt

-- The smallest positive index is triangular.
example : Odd (Nat.Partition.restricted 1 (¬ 4 ∣ ·)).card :=
  (odd_card_four_regular_iff_triangular 1 (by decide)).2 ⟨1, rfl⟩

-- Six is triangular and beyond the first excluded part size.
example : Odd (Nat.Partition.restricted 6 (¬ 4 ∣ ·)).card :=
  (odd_card_four_regular_iff_triangular 6 (by decide)).2 ⟨3, rfl⟩

-- Four is the first index where the restriction excludes a partition; it is not triangular.
example : ¬ Odd (Nat.Partition.restricted 4 (¬ 4 ∣ ·)).card := by
  rw [odd_card_four_regular_iff_triangular 4 (by decide)]
  rintro ⟨m, hm⟩
  by_cases h : m ≤ 2
  · have hprod : m * (m + 1) ≤ 2 * 3 := Nat.mul_le_mul h (by omega)
    omega
  · have hprod : 3 * 4 ≤ m * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega

end MetaMathlibExt
