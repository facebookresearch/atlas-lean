/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DeterminantalRecurrentSequencesCompositionSumSuccMulTwoZpow
import Mathlib.Tactic.NormNum

/-!
# Tests for the composition sum with linear and geometric weights

The first three positive indices exercise both parity branches.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 1, equation (8).
-/

namespace MathlibExtTest.NumberTheory.DeterminantalRecurrentSequencesCompositionSumSuccMulTwoZpow

example :
    ∑ c : Composition 1, ∏ i : Fin c.length,
      ((c.blocksFun i : ℚ) + 1) * (2 : ℚ) ^ ((c.blocksFun i : ℤ) - 2) = 1 := by
  rw [MetaMathlibExt.composition_sum_succ_mul_two_zpow 1 (by decide)]
  norm_num [Nat.fib, MetaMathlibExt.lucasNumber]

example :
    ∑ c : Composition 2, ∏ i : Fin c.length,
      ((c.blocksFun i : ℚ) + 1) * (2 : ℚ) ^ ((c.blocksFun i : ℤ) - 2) = 4 := by
  rw [MetaMathlibExt.composition_sum_succ_mul_two_zpow 2 (by decide)]
  norm_num [Nat.fib, MetaMathlibExt.lucasNumber]

example :
    ∑ c : Composition 3, ∏ i : Fin c.length,
      ((c.blocksFun i : ℚ) + 1) * (2 : ℚ) ^ ((c.blocksFun i : ℤ) - 2) = 15 := by
  rw [MetaMathlibExt.composition_sum_succ_mul_two_zpow 3 (by decide)]
  have h : Odd (3 : ℕ) := by decide
  norm_num [h, Nat.fib]

end MathlibExtTest.NumberTheory.DeterminantalRecurrentSequencesCompositionSumSuccMulTwoZpow
