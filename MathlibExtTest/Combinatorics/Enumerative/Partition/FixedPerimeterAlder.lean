/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterAlder

namespace MetaMathlibExt

-- At d = a = 1 both floor bounds are sharp, for either parity of the inner quotient.
-- The hypothesis 2a < d + 3 is passed by its name `had` from the wanted statement.
example (n : ℕ) (hn : 1 ≤ n) :
    (n - 1) / 2 / 2 = (n - 1) / 4 ∧ ((n - 1) / 2 + 1) / 2 = (n + 1) / 4 := by
  obtain ⟨hdown, hup⟩ := floor_half_div_le_div_of_two_mul_lt (d := 1) (a := 1)
    (by decide) (by decide) (had := by decide) hn
  exact ⟨le_antisymm hdown (by omega), le_antisymm hup (by omega)⟩

-- At n = a the strict bound on 2a puts even the larger numerator below the divisor.
example {d a : ℕ} (had : 2 * a < d + 3) :
    (a - a) / (d + 3) = 0 ∧ (a + a) / (d + 3) = 0 := by
  exact ⟨by simp, Nat.div_eq_of_lt (by omega)⟩

example : fixedPerimeterPartitions 0 = ∅ := by decide

example : ({2, 2} : Multiset ℕ) ∈ fixedPerimeterPartitions 3 ∧ ¬ IsDDistinctParts 1 {2, 2} := by
  decide

-- The singleton part 5 represents -2 modulo 7.
example : perimeterPMResidueArmLegCount 4 2 5 1 = 1 ∧ perimeterResidueArmLegCount 4 2 5 1 = 0 := by
  decide

end MetaMathlibExt
