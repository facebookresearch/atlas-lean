/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.JavanpeykarBelyiCounting
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

open Javanpeykar

/-! Checks and concrete instances of the counting steps of Javanpeykar's Theorem 4.5.2. -/

#check @two_mul_add_one_le_of_riemannHurwitz
#check @genus_le_degree_of_riemannHurwitz
#check @three_le_degree_of_riemannHurwitz
#check @Finset.exists_mem_notMem_of_card_lt_mul
#check @exists_mem_fiber_notMem_of_card_le

/-- The Riemann–Hurwitz count for `z ↦ z³` (degree 3, genus 0): one point of index 3 above `0`
and above `∞`, three points of index 1 above `1`. -/
example : 2 * 0 + 1 ≤ 3 := by
  let b : Fin 5 → Fin 3 := ![0, 2, 1, 1, 1]
  let e : Fin 5 → ℕ := ![3, 3, 1, 1, 1]
  refine two_mul_add_one_le_of_riemannHurwitz (b := b) (e := e) (d := 3) (g := 0) ?_ ?_ ?_
  · intro t
    fin_cases t
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
  · intro t
    fin_cases t <;> decide
  · decide

/-- The general lemma with two disjoint sets of two elements and at most three excluded
points. -/
example (W : Finset ℕ) (hW : W.card ≤ 3) :
    ∃ i ∈ (Finset.univ : Finset (Fin 2)), ∃ x ∈ (![{0, 1}, {2, 3}] : Fin 2 → Finset ℕ) i,
      x ∉ W := by
  refine Finset.exists_mem_notMem_of_card_lt_mul (d := 2) ?_ ?_ ?_
  · intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · show Disjoint ({0, 1} : Finset ℕ) {2, 3}
      decide
    · show Disjoint ({2, 3} : Finset ℕ) {0, 1}
      decide
    · exact absurd rfl hij
  · intro i _
    fin_cases i <;> simp
  · simpa using Nat.lt_succ_of_le hW

/-- With `d = g = 1` there is one fibre of one point, and `W` must be empty. -/
example : ∃ i ∈ Finset.Icc 1 (1 ^ 2), ∃ x ∈ ({0} : Finset ℕ), x ∉ (∅ : Finset ℕ) :=
  exists_mem_fiber_notMem_of_card_le (F := fun _ => {0}) (W := ∅) (d := 1) (g := 1) le_rfl le_rfl
    (by simp [Set.PairwiseDisjoint]) (by simp) (by simp)

#print axioms two_mul_add_one_le_of_riemannHurwitz
#print axioms genus_le_degree_of_riemannHurwitz
#print axioms three_le_degree_of_riemannHurwitz
#print axioms Finset.exists_mem_notMem_of_card_lt_mul
#print axioms exists_mem_fiber_notMem_of_card_le
