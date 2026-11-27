/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ExactSlowNimCritical

open MetaMathlibExt

-- An even level with all piles even (type A0).
example : IsExactSlowNimCritical 2 2 ![0, 2, 2] :=
  (isExactSlowNimCritical_iff (by decide) 2 ![0, 2, 2]).2 <| Or.inl
    ⟨by decide, by decide, fun _ => by decide,
      fun h => ((Nat.not_even_iff_odd.mpr h) (by decide)).elim⟩

-- An odd level with the unique even pile in the middle (type A1).
example : IsExactSlowNimCritical 2 1 ![1, 0, 1] := by
  apply (isExactSlowNimCritical_iff (by decide) 1 ![1, 0, 1]).2
  refine Or.inl ⟨by decide, by decide, ?_, fun _ => ⟨1, by decide, ?_⟩⟩
  · intro h
    exact (Nat.not_even_iff_odd.mpr (by decide : Odd 1) h).elim
  · decide

-- A type (B) position whose total is strictly larger than k * m.
example : IsExactSlowNimCritical 2 4 ![3, 3, 3] :=
  (isExactSlowNimCritical_iff (by decide) 4 ![3, 3, 3]).2 (Or.inr (by decide))

-- Adding a token to the type (A0) example makes it noncritical at the old level.
example : ¬ IsExactSlowNimCritical 2 2 ![0, 2, 3] := by
  rw [isExactSlowNimCritical_iff (by decide)]
  exact not_or.mpr ⟨fun h => (by decide : (∑ i, (![0, 2, 3] : Fin 3 → ℕ) i) ≠ 2 * 2) h.1,
    fun h => (by decide : ¬ (![0, 2, 3] : Fin 3 → ℕ) 2 < 2) (h.2.1 2)⟩
