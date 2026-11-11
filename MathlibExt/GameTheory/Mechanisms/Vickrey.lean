/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Function.Basic

import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

@[expose] public section

/-! # The Vickrey (second-price) auction

With at least two bidders, truthful bidding is a weakly dominant
strategy in the second-price auction with the least-index tie-break,
and truthful bidding is individually rational for nonnegative
valuations. This file covers roadmap package DPA-39 of the Atlas TCS
canon roadmap.

Source: W. Vickrey, "Counterspeculation, auctions, and competitive
sealed tenders", Journal of Finance 16 (1961), 8--37.
-/

open Finset

/-- The winner of a second-price (Vickrey) auction: the least index
attaining the maximal bid. -/
noncomputable def vickreyWinner {n : ℕ} [Nonempty (Fin n)] (b : Fin n → ℝ) : Fin n :=
  (Finset.univ.filter (fun i => ∀ j, b j ≤ b i)).min' (by
    rcases Finset.exists_max_image Finset.univ b Finset.univ_nonempty with ⟨i, hi, hmax⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun j => hmax j (Finset.mem_univ j)⟩⟩)

/-- The price paid by the winner: the largest bid among the other
bidders, or `0` if there are none. -/
noncomputable def vickreyPrice {n : ℕ} [Nonempty (Fin n)] (b : Fin n → ℝ) : ℝ :=
  if h : ((Finset.univ.erase (vickreyWinner b)).image b).Nonempty then
    ((Finset.univ.erase (vickreyWinner b)).image b).max' h
  else 0

/-- Quasilinear utility of bidder `i` with valuation `v` under bids `b`:
the winner gets `v - price`, losers get `0`. -/
noncomputable def vickreyUtility {n : ℕ} [Nonempty (Fin n)] (v : ℝ) (b : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  if vickreyWinner b = i then v - vickreyPrice b else 0

/-- The winner's bid is maximal. -/
private lemma vickreyWinner_max {n : ℕ} [Nonempty (Fin n)] (b : Fin n → ℝ) (j : Fin n) :
    b j ≤ b (vickreyWinner b) := by
  have hm : vickreyWinner b ∈ Finset.univ.filter (fun i => ∀ k, b k ≤ b i) :=
    Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hm).2 j

/-- With at least two bidders, removing the winner leaves someone. -/
private lemma erase_winner_nonempty {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    (b : Fin n → ℝ) : (Finset.univ.erase (vickreyWinner b)).Nonempty := by
  rw [← Finset.card_pos]
  have hcard : (Finset.univ.erase (vickreyWinner b)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-- With at least two bidders, the price is taken over a nonempty set. -/
private lemma image_erase_winner_nonempty {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    (b : Fin n → ℝ) : ((Finset.univ.erase (vickreyWinner b)).image b).Nonempty :=
  (erase_winner_nonempty hn b).image b

/-- The price is at most any upper bound on the other bids. -/
private lemma vickreyPrice_le {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    (b : Fin n → ℝ) (x : ℝ) (hx : ∀ j, j ≠ vickreyWinner b → b j ≤ x) :
    vickreyPrice b ≤ x := by
  have hne := image_erase_winner_nonempty hn b
  unfold vickreyPrice
  rw [dite_eq_left hne]
  apply Finset.max'_le
  intro y hy
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  exact hx j (Finset.mem_erase.mp hj).1

/-- Every other bid is at most the price. -/
private lemma le_vickreyPrice {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    (b : Fin n → ℝ) (j : Fin n) (hj : j ≠ vickreyWinner b) :
    b j ≤ vickreyPrice b := by
  have hne := image_erase_winner_nonempty hn b
  unfold vickreyPrice
  rw [dite_eq_left hne]
  apply Finset.le_max'
  rw [Finset.mem_image]
  exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩, rfl⟩

/-- Weak dominance of truthful bidding in the Vickrey auction. -/
theorem vickrey_truthful_dominant {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    (i : Fin n) (v : ℝ) (b : Fin n → ℝ) :
    vickreyUtility v b i ≤ vickreyUtility v (Function.update b i v) i := by
  by_cases hw : vickreyWinner b = i
  · by_cases hw' : vickreyWinner (Function.update b i v) = i
    · have hprice : vickreyPrice (Function.update b i v) = vickreyPrice b := by
        apply le_antisymm
        · apply vickreyPrice_le hn
          intro j hj
          rw [hw'] at hj
          have hupd : Function.update b i v j = b j := Function.update_of_ne hj _ _
          rw [hupd]
          apply le_vickreyPrice hn
          rw [hw]
          exact hj
        · apply vickreyPrice_le hn
          intro j hj
          rw [hw] at hj
          have hupd : b j = Function.update b i v j :=
            (Function.update_of_ne hj _ _).symm
          rw [hupd]
          apply le_vickreyPrice hn
          rw [hw']
          exact hj
      have hu : vickreyUtility v b i = v - vickreyPrice b := ite_eq_left hw
      have hu' : vickreyUtility v (Function.update b i v) i
          = v - vickreyPrice (Function.update b i v) := ite_eq_left hw'
      rw [hu, hu', hprice]
    · have hu : vickreyUtility v b i = v - vickreyPrice b := ite_eq_left hw
      have hu' : vickreyUtility v (Function.update b i v) i = 0 := ite_eq_right hw'
      rw [hu, hu']
      have hmax : v ≤ Function.update b i v (vickreyWinner (Function.update b i v)) := by
        have h := vickreyWinner_max (Function.update b i v) i
        have hself : Function.update b i v i = v := Function.update_self _ _ _
        rw [hself] at h
        exact h
      have hupd : Function.update b i v (vickreyWinner (Function.update b i v))
          = b (vickreyWinner (Function.update b i v)) := Function.update_of_ne hw' _ _
      rw [hupd] at hmax
      have hle : b (vickreyWinner (Function.update b i v)) ≤ vickreyPrice b :=
        le_vickreyPrice hn b _ (by rw [hw]; exact hw')
      linarith
  · by_cases hw' : vickreyWinner (Function.update b i v) = i
    · have hu : vickreyUtility v b i = 0 := ite_eq_right hw
      have hu' : vickreyUtility v (Function.update b i v) i
          = v - vickreyPrice (Function.update b i v) := ite_eq_left hw'
      rw [hu, hu']
      have hle : vickreyPrice (Function.update b i v) ≤ v := by
        have hmax : vickreyPrice (Function.update b i v)
            ≤ Function.update b i v (vickreyWinner (Function.update b i v)) :=
          vickreyPrice_le hn _ _ (fun j _ => vickreyWinner_max _ j)
        have hself : Function.update b i v (vickreyWinner (Function.update b i v)) = v := by
          rw [hw']
          exact Function.update_self _ _ _
        rw [hself] at hmax
        exact hmax
      linarith
    · have hu : vickreyUtility v b i = 0 := ite_eq_right hw
      have hu' : vickreyUtility v (Function.update b i v) i = 0 := ite_eq_right hw'
      rw [hu, hu']

/-- Individual rationality of truthful bidding for nonnegative
valuations. -/
theorem vickrey_ir {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    (i : Fin n) {v : ℝ} (hv : 0 ≤ v) (b : Fin n → ℝ) :
    0 ≤ vickreyUtility v (Function.update b i v) i := by
  by_cases hw' : vickreyWinner (Function.update b i v) = i
  · have hu' : vickreyUtility v (Function.update b i v) i
        = v - vickreyPrice (Function.update b i v) := ite_eq_left hw'
    rw [hu']
    have hle : vickreyPrice (Function.update b i v) ≤ v := by
      have hmax : vickreyPrice (Function.update b i v)
          ≤ Function.update b i v (vickreyWinner (Function.update b i v)) :=
        vickreyPrice_le hn _ _ (fun j _ => vickreyWinner_max _ j)
      have hself : Function.update b i v (vickreyWinner (Function.update b i v)) = v := by
        rw [hw']
        exact Function.update_self _ _ _
      rw [hself] at hmax
      exact hmax
    have _ : 0 ≤ v := hv
    linarith
  · have hu' : vickreyUtility v (Function.update b i v) i = 0 := ite_eq_right hw'
    rw [hu']
