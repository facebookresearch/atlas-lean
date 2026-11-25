/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MonochromaticLinearEquations.Recolouring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.isUncommonOverIntegers_of_two.Test

open Finset Filter

-- On [1, 64m], every solution of x + y = 16z has z ≤ 8m. Colour at that cutoff.
-- The pairs (x, z) with x ≤ 32m and 2m < z ≤ 4m give at least 64m² solutions.
-- A monochromatic solution must have x, y ≤ 8m, hence z ≤ m, giving at most 8m².
private lemma twoColours : IsUncommonOverIntegers (![1, 1, -16] : Fin 3 → ℤ) 2 := by
  refine ⟨1 / 4, by norm_num, frequently_atTop.mpr fun N => ?_⟩
  let m : ℕ := N + 1
  let χ (t : ℤ) : Fin 2 := if t ≤ 8 * m then 0 else 1
  refine ⟨64 * m, by dsimp [m]; omega, χ, ?_⟩
  let box := Fintype.piFinset fun _ : Fin 3 => Icc (1 : ℤ) (64 * m)
  let eqn (v : Fin 3 → ℤ) := ∑ i, (![1, 1, -16] : Fin 3 → ℤ) i * v i = 0
  let mono (v : Fin 3 → ℤ) := ∀ i j, χ (v i) = χ (v j)
  have he (v) : eqn v ↔ v 0 + v 1 = 16 * v 2 := by
    simp [eqn, Fin.sum_univ_succ]
    omega
  have htot : (32 * m) * (2 * m) ≤ (box.filter eqn).card := by
    let pairs := Icc (1 : ℤ) (32 * m) ×ˢ Icc (2 * (m : ℤ) + 1) (4 * m)
    have hc : pairs.card = (32 * m) * (2 * m) := by
      rw [card_product]
      congr 1 <;> simp [Int.card_Icc] <;> omega
    rw [← hc]
    apply card_le_card_of_injOn (fun p : ℤ × ℤ => ![p.1, 16 * p.2 - p.1, p.2])
    · rintro ⟨x, z⟩ hp
      obtain ⟨hxp, hzp⟩ := mem_product.mp hp
      obtain ⟨hx, hx'⟩ := mem_Icc.mp hxp
      obtain ⟨hz, hz'⟩ := mem_Icc.mp hzp
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, (he _).mpr (by simp)⟩
      fin_cases i <;> simp <;> omega
    · intro p _ q _ h
      exact Prod.ext (congrFun h 0) (congrFun h 2)
  have hmono : (box.filter (fun v => eqn v ∧ mono v)).card ≤ 8 * m * m := by
    let small := Icc (1 : ℤ) (8 * m) ×ˢ Icc (1 : ℤ) m
    have hc : small.card = 8 * m * m := by
      rw [card_product]
      congr 1 <;> simp [Int.card_Icc]
      omega
    rw [← hc]
    apply card_le_card_of_injOn (fun v : Fin 3 → ℤ => (v 0, v 2))
    · intro v hv
      obtain ⟨hv, hv', hm⟩ := mem_filter.mp hv
      have hb (i) := mem_Icc.mp ((Fintype.mem_piFinset.mp hv) i)
      have heq := (he v).mp hv'
      have hz : v 2 ≤ 8 * m := by linarith [(hb 0).2, (hb 1).2]
      have hs (i) : v i ≤ 8 * m := by
        by_contra! h
        simpa [χ, hz, not_le.mpr h] using hm i 2
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨(hb 0).1, hs 0⟩,
        mem_Icc.mpr ⟨(hb 2).1, by linarith [hs 0, hs 1]⟩⟩
    · intro v hv w hw h
      have hv' := (he v).mp (mem_filter.mp hv).2.1
      have hw' := (he w).mp (mem_filter.mp hw).2.1
      have h0 : v 0 = w 0 := congrArg Prod.fst h
      have h2 : v 2 = w 2 := congrArg Prod.snd h
      funext i
      fin_cases i <;> simp <;> omega
  push_cast
  change (2 : ℝ) ^ (3 - 1 : ℕ) * ((box.filter (fun v => eqn v ∧ mono v)).card : ℝ) <
    (1 - 1 / 4) * (box.filter eqn).card
  have hM : ((box.filter (fun v => eqn v ∧ mono v)).card : ℝ) ≤ 8 * (m : ℝ) * m := by
    exact_mod_cast hmono
  have hS : 32 * (m : ℝ) * (2 * m) ≤ (box.filter eqn).card := by exact_mod_cast htot
  have hm : 0 < (m : ℝ) ^ 2 := by dsimp [m]; positivity
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, Nat.reducePow, Nat.one_pow] at *
  linarith

-- Exercise the minimum arity and the first new colour, including repeated-coordinate solutions.
example : IsUncommonOverIntegers (![1, 1, -16] : Fin 3 → ℤ) 3 :=
  isUncommonOverIntegers_of_two 3 (by decide) _ (by decide) twoColours 3 (by decide)

end MetaMathlibExt.isUncommonOverIntegers_of_two.Test
