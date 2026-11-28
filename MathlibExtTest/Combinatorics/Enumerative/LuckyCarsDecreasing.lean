/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Enumerative.LuckyCarsDecreasing

/-! # Tests for the lucky-spot count in weakly decreasing parking functions -/

open MetaMathlibExt MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

-- The first two cars both prefer spot 1, but the second takes spot 2.
example : List.ofFn (parkSpots (![1, 1, 0] : Fin 3 → Fin 3)) = [1, 2, 0] := by
  decide +kernel

-- Enumerate the lucky (car, preference function) pairs using greedy parking itself.
private def directLuckySpotCount (n : ℕ) (j : Fin n) : ℕ :=
  ∑ i : Fin n, (Finset.univ.filter fun f : Fin n → Fin n =>
    IsParkingFunction n f ∧ Antitone f ∧ f i = j ∧ parkSpots f i = j).card

example : directLuckySpotCount 1 0 = 1 := by decide +kernel

-- The first, middle, and last spots in a three-car lot.
example : directLuckySpotCount 3 0 = 5 := by decide +kernel
example : directLuckySpotCount 3 1 = 3 := by decide +kernel
example : directLuckySpotCount 3 2 = 2 := by decide +kernel

-- Compare the independently computed interior count to the Catalan sum.
example : directLuckySpotCount 3 1 =
    ∑ k ∈ Finset.range 2, catalan (3 - 1 - k) * catalan k := by
  decide +kernel

-- Apply the public formula to the same spot counted independently above.
example : (∑ i : Fin 3, (qDec 3 i 1 : ℚ)) = 3 := by
  rw [card_dec_lucky_spot_eq_sum_catalan, ← Nat.cast_sum]
  norm_cast
  decide +kernel
