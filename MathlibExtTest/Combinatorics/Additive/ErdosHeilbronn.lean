/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.ErdosHeilbronn

@[expose] public section

open MathlibExt.Combinatorics.Additive.ErdosHeilbronn

namespace MathlibExtTest.Combinatorics.Additive.ErdosHeilbronn

-- The progression `{0, 1, 2}` in `ℤ/7` has restricted sums `{1, 2, 3}`: the bound `2|A| - 3 = 3`
-- is attained.
example : (MetaMathlibExt.restrictedSumset 2 ({0, 1, 2} : Finset (ZMod 7))).card = 3 := by decide

example : min 7 (2 * ({0, 1, 2} : Finset (ZMod 7)).card - 3) ≤
    (MetaMathlibExt.restrictedSumset 2 ({0, 1, 2} : Finset (ZMod 7))).card :=
  min_le_card_restrictedSumset (by decide) ⟨0, by simp⟩

-- When `2|A| - 3 > p` the bound is `p`: all of `ℤ/5` is a restricted sum of elements of `ℤ/5`.
example : (MetaMathlibExt.restrictedSumset 2 (Finset.univ : Finset (ZMod 5))).card = 5 := by decide

example : min 5 (2 * (Finset.univ : Finset (ZMod 5)).card - 3) ≤
    (MetaMathlibExt.restrictedSumset 2 (Finset.univ : Finset (ZMod 5))).card :=
  min_le_card_restrictedSumset (by decide) Finset.univ_nonempty

-- A singleton has no restricted sums, and the bound is `0`.
example : (MetaMathlibExt.restrictedSumset 2 ({3} : Finset (ZMod 7))).card = 0 := by decide

-- The `h = 2` case of the wanted Dias da Silva–Hamidoune statement, for `{0, 1, 2} ⊆ ℤ/7`.
example : min 7 (2 * ({0, 1, 2} : Finset (ZMod 7)).card - 2 ^ 2 + 1) ≤
    (MetaMathlibExt.restrictedSumset 2 ({0, 1, 2} : Finset (ZMod 7))).card :=
  dias_da_silva_hamidoune_two (by decide) _ ⟨0, by simp⟩ (by decide)

end MathlibExtTest.Combinatorics.Additive.ErdosHeilbronn
