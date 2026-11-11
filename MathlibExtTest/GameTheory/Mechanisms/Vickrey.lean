/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import MathlibExt.GameTheory.Mechanisms.Vickrey

open Finset Matrix

/-- Boundary check: with two bidders, bidder `0` with valuation `5`
gains nothing by deviating from truthful bidding, whatever the other
bid profile was. -/
example (b : Fin 2 → ℝ) :
    vickreyUtility 5 b 0 ≤ vickreyUtility 5 (Function.update b 0 5) 0 :=
  vickrey_truthful_dominant (by norm_num) 0 5 b

/-- Boundary check: truthful bidding never loses money for a
nonnegative valuation. -/
example (b : Fin 2 → ℝ) : 0 ≤ vickreyUtility 5 (Function.update b 0 5) 0 :=
  vickrey_ir (by norm_num) 0 (by norm_num) b

/-- Concrete tied bids `![2, 2, 1]`: bidder `0` is a maximal bidder. -/
private theorem tied_zero_mem :
    (0 : Fin 3) ∈ Finset.univ.filter (fun i => ∀ j, (![2, 2, 1] : Fin 3 → ℝ) j ≤ (![2, 2, 1] : Fin 3 → ℝ) i) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro j
  fin_cases j <;> simp

/-- Concrete tied bids: the least-index tie-break makes bidder `0`
the winner. -/
theorem tied_winner : vickreyWinner ![2, 2, 1] = 0 := by
  unfold vickreyWinner
  apply le_antisymm
  · exact Finset.min'_le _ _ tied_zero_mem
  · exact Finset.le_min' _ _ _ (fun i _ => Fin.zero_le i)

/-- The image of the other bids under tied bids `![2, 2, 1]` is
`{2, 1}`. -/
private theorem tied_other_bids :
    (Finset.univ.erase (0 : Fin 3)).image ![2, 2, 1] = {2, 1} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    fin_cases i
    · exact absurd rfl hi.1
    · simp [Matrix.cons_val_one, Matrix.head_cons]
    · simp [Matrix.cons_val_two, Matrix.head_cons]
  · rintro (rfl | rfl)
    · exact ⟨1, by norm_num, by norm_num [Matrix.cons_val_one, Matrix.head_cons]⟩
    · exact ⟨2, by norm_num, by norm_num [Matrix.cons_val_two, Matrix.head_cons]⟩

/-- Concrete tied bids: the price is the second-highest bid, with the
tie counted, so the price is `2`. -/
theorem tied_price : vickreyPrice ![2, 2, 1] = 2 := by
  have hne : ((Finset.univ.erase (vickreyWinner ![2, 2, 1])).image (![2, 2, 1] : Fin 3 → ℝ)).Nonempty := by
    refine ⟨2, Finset.mem_image.mpr ⟨1, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ 1⟩, ?_⟩⟩
    · rw [tied_winner]; norm_num
    · norm_num [Matrix.cons_val_one, Matrix.head_cons]
  unfold vickreyPrice
  split_ifs with h
  · apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_erase] at hi
      fin_cases i
      · simp [tied_winner] at hi
      · norm_num [Matrix.cons_val_one, Matrix.head_cons]
      · norm_num [Matrix.cons_val_two, Matrix.head_cons]
    · apply Finset.le_max'
      exact Finset.mem_image.mpr ⟨1, Finset.mem_erase.mpr
        ⟨by rw [tied_winner]; norm_num, Finset.mem_univ 1⟩,
        by norm_num [Matrix.cons_val_one, Matrix.head_cons]⟩
  · exact absurd hne h

/-- Concrete tied bids: the winner with valuation `5` gets utility
`5 - 2 = 3`. -/
theorem tied_winner_utility : vickreyUtility 5 ![2, 2, 1] 0 = 3 := by
  norm_num [vickreyUtility, tied_winner, tied_price]

/-- Concrete tied bids: the tied loser gets utility `0`. -/
theorem tied_loser_utility : vickreyUtility 5 ![2, 2, 1] 1 = 0 := by
  simp [vickreyUtility, tied_winner]

/-- Concrete distinct bids `![3, 2, 1]`: bidder `0` is the unique
maximal bidder, hence the winner. -/
private theorem distinct_winner : vickreyWinner ![3, 2, 1] = 0 := by
  unfold vickreyWinner
  apply le_antisymm
  · apply Finset.min'_le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro j
    fin_cases j <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons]
  · exact Finset.le_min' _ _ _ (fun i _ => Fin.zero_le i)

/-- Concrete distinct bids `![3, 2, 1]`: the price is the
second-highest bid `2`. -/
theorem distinct_price : vickreyPrice ![3, 2, 1] = 2 := by
  have hne : ((Finset.univ.erase (vickreyWinner ![3, 2, 1])).image (![3, 2, 1] : Fin 3 → ℝ)).Nonempty := by
    refine ⟨2, Finset.mem_image.mpr ⟨1, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ 1⟩, ?_⟩⟩
    · rw [distinct_winner]; norm_num
    · norm_num [Matrix.cons_val_one, Matrix.head_cons]
  unfold vickreyPrice
  split_ifs with h
  · apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_erase] at hi
      fin_cases i
      · simp [distinct_winner] at hi
      · norm_num [Matrix.cons_val_one, Matrix.head_cons]
      · norm_num [Matrix.cons_val_two, Matrix.head_cons]
    · apply Finset.le_max'
      exact Finset.mem_image.mpr ⟨1, Finset.mem_erase.mpr
        ⟨by rw [distinct_winner]; norm_num, Finset.mem_univ 1⟩,
        by norm_num [Matrix.cons_val_one, Matrix.head_cons]⟩
  · exact absurd hne h

/-- Singleton auction: there are no other bidders, so the price
is `0`. -/
theorem singleton_price : vickreyPrice ![7] = 0 := by
  unfold vickreyPrice
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    obtain ⟨i, hi, -⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_erase] at hi
    exact absurd (by rw [Fin.eq_zero i, Fin.eq_zero (vickreyWinner ![7])]) hi.1
  · rfl
