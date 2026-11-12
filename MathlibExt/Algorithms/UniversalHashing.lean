/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section



/-- Card of a filtered `univ` as a real-valued indicator sum. -/
private theorem card_filter_univ_eq_sum_ite {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] :
    ((Finset.univ.filter p).card : ℝ) = ∑ a : α, (if p a then (1 : ℝ) else 0) := by
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : p a <;> simp [h]

/-- Expected chain length for chaining with a universal hash
family. `H` is a finite family of hash functions from keys `K`
to buckets `Fin m`; the family is universal if for distinct keys
`x ≠ y`, the number of functions in the family that collide on
`x, y` is at most `|H| / m`. Then for every fixed key `x`, the
total over the family of the chain length at `x`'s bucket (the
number of keys hashing to the same bucket as `x`, summed over
all functions) is at most `|H| * (1 + (|K| - 1) / m)`: the
expected chain length is at most `1 + α` for load factor
`α = |K| / m` (up to the `-1`). -/
theorem expected_chain_length {K H : Type*} [Fintype K] [Fintype H]
    (m : ℕ) (hash : H → K → Fin m)
    (huniv : ∀ x y : K, x ≠ y →
      ((Finset.univ.filter (fun hh => hash hh x = hash hh y)).card : ℝ) ≤
        (Fintype.card H : ℝ) / m)
    (x : K) :
    (∑ hh : H, ((Finset.univ.filter (fun y => hash hh y = hash hh x)).card : ℝ)) ≤
      (Fintype.card H : ℝ) * (1 + (Fintype.card K - 1 : ℝ) / m) := by
  classical
  have hLHS : (∑ hh : H, ((Finset.univ.filter (fun y => hash hh y = hash hh x)).card : ℝ))
      = ∑ y : K, ∑ hh : H, (if hash hh y = hash hh x then (1 : ℝ) else 0) := by
    trans ∑ hh : H, ∑ y : K, (if hash hh y = hash hh x then (1 : ℝ) else 0)
    · apply Finset.sum_congr rfl
      intro hh _
      exact card_filter_univ_eq_sum_ite _
    · exact Finset.sum_comm
  set g : K → ℝ := fun y => ∑ hh : H, (if hash hh y = hash hh x then (1 : ℝ) else 0) with hg
  rw [hLHS]
  have hsplit : (∑ y : K, g y) = g x + ∑ y ∈ Finset.univ.erase x, g y := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  rw [hsplit]
  have hgx : g x = (Fintype.card H : ℝ) := by
    have h1 : ∀ hh : H, (if hash hh x = hash hh x then (1 : ℝ) else 0) = 1 := by
      intro hh
      simp
    have h2 : g x = ∑ _hh : H, (1 : ℝ) := by
      show (∑ hh : H, (if hash hh x = hash hh x then (1 : ℝ) else 0)) = _
      apply Finset.sum_congr rfl
      intro hh _
      exact h1 hh
    rw [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hgx]
  have hbound : ∀ y ∈ Finset.univ.erase x, g y ≤ (Fintype.card H : ℝ) / m := by
    intro y hy
    have hyx : y ≠ x := Finset.ne_of_mem_erase hy
    have hcard : g y = ((Finset.univ.filter (fun hh => hash hh x = hash hh y)).card : ℝ) := by
      have h1 := card_filter_univ_eq_sum_ite (fun hh => hash hh x = hash hh y)
      rw [h1]
      show (∑ hh : H, (if hash hh y = hash hh x then (1 : ℝ) else 0)) =
        ∑ hh : H, (if hash hh x = hash hh y then (1 : ℝ) else 0)
      apply Finset.sum_congr rfl
      intro hh _
      by_cases h : hash hh y = hash hh x
      · rw [ite_eq_left h, ite_eq_left h.symm]
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    rw [hcard]
    exact huniv x y (Ne.symm hyx)
  have h1K : 1 ≤ Fintype.card K := Fintype.card_pos_iff.mpr ⟨x⟩
  have herase : (Finset.univ.erase x).card = Fintype.card K - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
  have hsum : ∑ y ∈ Finset.univ.erase x, g y
      ≤ ((Fintype.card K : ℝ) - 1) * ((Fintype.card H : ℝ) / m) := by
    have hle : ∑ y ∈ Finset.univ.erase x, g y
        ≤ ∑ _y ∈ Finset.univ.erase x, ((Fintype.card H : ℝ) / m) :=
      Finset.sum_le_sum hbound
    rw [Finset.sum_const, herase, nsmul_eq_mul, Nat.cast_sub h1K, Nat.cast_one] at hle
    exact hle
  have hfinal : (Fintype.card H : ℝ) + ((Fintype.card K : ℝ) - 1) * ((Fintype.card H : ℝ) / m)
      = (Fintype.card H : ℝ) * (1 + ((Fintype.card K : ℝ) - 1) / m) := by
    ring
  rw [← hfinal]
  exact add_le_add_right hsum _
