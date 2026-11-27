/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ExactSlowNimA0Moves

/-!
# Tests for moves supported by type (A0) basic vectors

The examples keep an uncapped pile or keep a capped pile with spare room on a different pile.
-/

namespace MathlibExtTest.GameTheory.ExactSlowNimA0Moves

open MetaMathlibExt

private theorem support : IsExactSlowNimBasicA0 2 2 ![0, 2, 2] := by
  unfold IsExactSlowNimBasicA0
  decide

private theorem start_value (x : Fin 3 → ℕ) (hx : ![0, 2, 2] ≤ x) (hm : ∑ i, x i ≤ 5) :
    exactSlowNimBasicValue 2 x = 2 := by
  classical
  unfold exactSlowNimBasicValue
  have hmass : (∑ i, (![0, 2, 2] : Fin 3 → ℕ) i) ≤ ∑ i, x i :=
    Finset.sum_le_sum fun i _ => hx i
  have hsum : ∑ i, (![0, 2, 2] : Fin 3 → ℕ) i = 4 := by decide
  rw [hsum] at hmass
  rw [Nat.findGreatest_eq_iff]
  refine ⟨(show 2 ≤ 4 by decide).trans hmass, fun _ => ⟨![0, 2, 2], hx, Or.inl support⟩, ?_⟩
  rintro b hb _ ⟨y, hyx, ha | ha | hc⟩
  all_goals
    have hle := (Finset.sum_le_sum fun i _ => hyx i).trans hm
    first | have := ha.1 | have := hc.1
    omega

example : exactSlowNimBasicValue 2 ![0, 1, 1] = 1 := by
  have hv := start_value ![0, 2, 2] le_rfl (by decide)
  have h := exactSlowNimBasicValue_of_supports_basicA0 (by decide : 0 < 2)
    ![0, 2, 2] ![0, 2, 2] le_rfl (hv.symm ▸ support) 0 (by decide)
  have hafter : slowANimAfter ![0, 2, 2] (Finset.univ.erase 0) = ![0, 1, 1] := by decide
  rw [hafter, hv] at h
  exact h.2.2 (Or.inl (by decide))

example : exactSlowNimBasicValue 2 ![0, 2, 1] = 1 ∧ Odd (exactSlowNimBasicValue 2 ![0, 2, 1]) := by
  have hzx : (![0, 2, 2] : Fin 3 → ℕ) ≤ ![1, 2, 2] := by decide
  have hv := start_value ![1, 2, 2] hzx (by decide)
  have h := exactSlowNimBasicValue_of_supports_basicA0 (by decide : 0 < 2)
    ![1, 2, 2] ![0, 2, 2] hzx (hv.symm ▸ support) 1 (by decide)
  have hafter : slowANimAfter ![1, 2, 2] (Finset.univ.erase 1) = ![0, 2, 1] := by decide
  rw [hafter, hv] at h
  exact ⟨h.2.2 (Or.inr ⟨by decide, 0, by decide⟩), h.2.1⟩

end MathlibExtTest.GameTheory.ExactSlowNimA0Moves
