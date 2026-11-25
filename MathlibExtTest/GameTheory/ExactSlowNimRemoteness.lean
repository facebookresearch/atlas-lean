/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ExactSlowNimRemoteness

namespace MetaMathlibExt.exactSlowNimBasicValue_of_supports_basicB

-- At k = 1 the two single-token piles form a type (B) vector of value two.
-- A legal move empties a pile.
example : exactSlowNimBasicValue 1 ![0, 1] = 1 := by
  let x : Fin 2 → ℕ := ![1, 1]
  have hb : IsExactSlowNimBasicB 1 2 x := by
    unfold IsExactSlowNimBasicB
    decide
  have hx : exactSlowNimBasicValue 1 x = 2 := by
    classical
    unfold exactSlowNimBasicValue
    rw [show ∑ i, x i = 2 by decide]
    exact Nat.findGreatest_eq ⟨x, le_rfl, Or.inr (Or.inr hb)⟩
  have h := (exactSlowNimBasicValue_of_supports_basicB (by decide : 0 < 1) x x le_rfl
    (hx.symm ▸ hb)).2 ![0, 1] (by decide)
  simpa [hx] using h

-- For three piles of size three, the move playing the outer piles drops the value from four
-- to three. The type (A1) witness beneath the resulting position has one even pile.
example : exactSlowNimBasicValue 2 ![2, 3, 2] = 3 := by
  let x : Fin 3 → ℕ := ![3, 3, 3]
  have hb : IsExactSlowNimBasicB 2 4 x := by
    unfold IsExactSlowNimBasicB
    decide
  have hsum : ∑ i, x i = 9 := by decide
  have hx : exactSlowNimBasicValue 2 x = 4 := by
    classical
    unfold exactSlowNimBasicValue
    rw [hsum, Nat.findGreatest_eq_iff]
    refine ⟨by decide, fun _ => ⟨x, le_rfl, Or.inr (Or.inr hb)⟩, ?_⟩
    rintro n hn _ ⟨y, hyx, ha | ha | hB⟩ <;>
      have hle := (Finset.sum_le_sum fun i _ => hyx i).trans_eq hsum
    · have := ha.1
      omega
    · have := ha.1
      omega
    · have := hB.1
      omega
  have h := (exactSlowNimBasicValue_of_supports_basicB (by decide : 0 < 2) x x le_rfl
    (hx.symm ▸ hb)).2 ![2, 3, 2] (by decide)
  simpa [hx] using h

end MetaMathlibExt.exactSlowNimBasicValue_of_supports_basicB
