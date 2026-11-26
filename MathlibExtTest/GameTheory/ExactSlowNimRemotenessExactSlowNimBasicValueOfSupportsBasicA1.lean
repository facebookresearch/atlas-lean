/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ExactSlowNimRemoteness

/-!
# Tests for moves supported by type (A1) basic vectors

Concrete applications of the M-move equality and the option lower bound.

Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi,
*On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 3 (the journal's numbering).
-/

namespace MathlibExtTest.GameTheory.ExactSlowNimRemotenessExactSlowNimBasicValueOfSupportsBasicA1

open MetaMathlibExt

private theorem basic_two_three_one : IsExactSlowNimBasicA1 2 3 ![2, 3, 1] := by
  unfold IsExactSlowNimBasicA1 ExistsUnique
  decide

private theorem value_two_three_one : exactSlowNimBasicValue 2 ![2, 3, 1] = 3 := by
  classical
  have hz := basic_two_three_one
  have hsum : ∑ i, (![2, 3, 1] : Fin 3 → ℕ) i = 6 := by decide
  unfold exactSlowNimBasicValue
  rw [hsum, Nat.findGreatest_eq_iff]
  refine ⟨by decide, fun _ => ⟨![2, 3, 1], le_rfl, Or.inr (Or.inl hz)⟩, ?_⟩
  rintro n hn _ ⟨y, hyx, ha | ha | hb⟩ <;>
    have hle := (Finset.sum_le_sum fun i _ => hyx i).trans_eq hsum
  · have := ha.1
    omega
  · have := ha.1
    omega
  · have := hb.1
    omega

example : exactSlowNimBasicValue 2 ![2, 2, 0] = 2 := by
  have hz := basic_two_three_one
  have h := (exactSlowNimBasicValue_of_supports_basicA1 (by decide : 0 < 2)
    ![2, 3, 1] ![2, 3, 1] le_rfl (value_two_three_one.symm ▸ hz)).2
  have hm : exactSlowNimMRuleMove ![2, 3, 1] = ![2, 2, 0] := by decide
  simpa [hm, value_two_three_one] using h

example : 1 ≤ exactSlowNimBasicValue 2 ![1, 3, 0] := by
  have hz := basic_two_three_one
  have h := (exactSlowNimBasicValue_of_supports_basicA1 (by decide : 0 < 2)
    ![2, 3, 1] ![2, 3, 1] le_rfl (value_two_three_one.symm ▸ hz)).1
    ![1, 3, 0] (by decide)
  simpa [value_two_three_one] using h

end MathlibExtTest.GameTheory.ExactSlowNimRemotenessExactSlowNimBasicValueOfSupportsBasicA1
