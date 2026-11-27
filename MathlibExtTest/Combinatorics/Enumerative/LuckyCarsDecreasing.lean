/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.LuckyCarsDecreasing

/-! # Tests for the lucky-spot count in weakly decreasing parking functions -/

open MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

-- The sole spot in a one-car lot.
example : (∑ i : Fin 1, (qDec 1 i 0 : ℚ)) = 1 := by
  rw [card_dec_lucky_spot_eq_sum_catalan, ← Nat.cast_sum]
  norm_cast
  decide +kernel

-- The first, an interior, and the last spot in a four-car lot.
example : (∑ i : Fin 4, (qDec 4 i 0 : ℚ)) = 14 := by
  rw [card_dec_lucky_spot_eq_sum_catalan, ← Nat.cast_sum]
  norm_cast
  decide +kernel

example : (∑ i : Fin 4, (qDec 4 i 1 : ℚ)) = 9 := by
  rw [card_dec_lucky_spot_eq_sum_catalan, ← Nat.cast_sum]
  norm_cast
  decide +kernel

example : (∑ i : Fin 4, (qDec 4 i 3 : ℚ)) = 5 := by
  rw [card_dec_lucky_spot_eq_sum_catalan, ← Nat.cast_sum]
  norm_cast
  decide +kernel
