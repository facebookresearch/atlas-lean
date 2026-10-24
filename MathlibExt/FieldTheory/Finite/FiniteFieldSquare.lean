/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# A square avoiding `0`, `1`, and `-1` in a finite field

Source: `v1/Atlas/AlgebraNotes/code/SimpleGroups.lean`
(`exists_sq_not_in_zero_one_neg_one'`, fully proved there), formalizing the
book's Lemma in the proof that `SL₂` is simple (Proof of Theorem
(`SL₂` simple)): if `|F| > 5`, then there exists some `r ∈ F` such that
`r ^ 2` is not `0`, `1`, or `-1`.

The proof is counting: if every square landed in `{0, 1, -1}`, then every
element of `F` would lie in one of three fibres of the squaring map. The
fibre of `0` has at most one element, and every other fibre has at most two
elements (two elements with the same square are equal up to sign), so
`|F| ≤ 1 + 2 + 2 = 5`, contradicting `5 < |F|`.
-/

@[expose] public section

set_option autoImplicit false

/-- Every fibre of the squaring map on a field has at most two elements:
two elements with the same square are equal up to sign. -/
private theorem card_filter_sq_eq_le_two {F : Type*} [Field F] [Fintype F] [DecidableEq F] (a : F) :
    (Finset.univ.filter (fun r : F => r ^ 2 = a)).card ≤ 2 := by
  classical
  by_cases h : ∃ r₀ : F, r₀ ^ 2 = a
  · obtain ⟨r₀, hr₀⟩ := h
    have hsub : Finset.univ.filter (fun r : F => r ^ 2 = a) ⊆ ({r₀, -r₀} : Finset F) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have h1 : x ^ 2 = r₀ ^ 2 := by rw [hx, hr₀]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with heq | heq
      · exact Finset.mem_insert.mpr (Or.inl heq)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr heq))
    calc (Finset.univ.filter (fun r : F => r ^ 2 = a)).card
        ≤ ({r₀, -r₀} : Finset F).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  · have hempty : Finset.univ.filter (fun r : F => r ^ 2 = a) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hx => h ⟨x, hx⟩
    rw [hempty]
    simp

/-- The fibre of `0` under the squaring map on a field has at most one
element: a square is `0` only for `0` itself. -/
private theorem card_filter_sq_eq_zero_le_one {F : Type*} [Field F] [Fintype F] [DecidableEq F] :
    (Finset.univ.filter (fun r : F => r ^ 2 = 0)).card ≤ 1 := by
  classical
  have hsub : Finset.univ.filter (fun r : F => r ^ 2 = 0) ⊆ ({0} : Finset F) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)] at hx
    exact Finset.mem_singleton.mpr hx
  calc (Finset.univ.filter (fun r : F => r ^ 2 = 0)).card
      ≤ ({0} : Finset F).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton 0

/-- In a field with more than five elements, some square avoids `0`, `1`,
and `-1`. -/
theorem exists_sq_ne_zero_one_neg_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : 5 < Fintype.card F) :
    ∃ r : F, r ^ 2 ≠ 0 ∧ r ^ 2 ≠ 1 ∧ r ^ 2 ≠ -1 := by
  classical
  by_contra h
  have hforall : ∀ r : F, r ^ 2 = 0 ∨ r ^ 2 = 1 ∨ r ^ 2 = -1 := by
    intro r
    by_contra hr
    have h0 : r ^ 2 ≠ 0 := fun h0 => hr (Or.inl h0)
    have h1 : r ^ 2 ≠ 1 := fun h1 => hr (Or.inr (Or.inl h1))
    have h2 : r ^ 2 ≠ -1 := fun h2 => hr (Or.inr (Or.inr h2))
    exact h ⟨r, h0, h1, h2⟩
  have hcover : Finset.univ ⊆
      Finset.univ.filter (fun r : F => r ^ 2 = 0) ∪
        Finset.univ.filter (fun r : F => r ^ 2 = 1) ∪
          Finset.univ.filter (fun r : F => r ^ 2 = -1) := by
    intro r _
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hforall r with hr | hr | hr
    · exact Or.inl (Or.inl hr)
    · exact Or.inl (Or.inr hr)
    · exact Or.inr hr
  have hle : Fintype.card F ≤
      (Finset.univ.filter (fun r : F => r ^ 2 = 0) ∪
        Finset.univ.filter (fun r : F => r ^ 2 = 1) ∪
          Finset.univ.filter (fun r : F => r ^ 2 = -1)).card := by
    have hcard := Finset.card_le_card hcover
    rwa [Finset.card_univ] at hcard
  have hle2 : (Finset.univ.filter (fun r : F => r ^ 2 = 0) ∪
        Finset.univ.filter (fun r : F => r ^ 2 = 1) ∪
          Finset.univ.filter (fun r : F => r ^ 2 = -1)).card ≤ 5 := by
    calc (Finset.univ.filter (fun r : F => r ^ 2 = 0) ∪
            Finset.univ.filter (fun r : F => r ^ 2 = 1) ∪
              Finset.univ.filter (fun r : F => r ^ 2 = -1)).card
        ≤ (Finset.univ.filter (fun r : F => r ^ 2 = 0) ∪
              Finset.univ.filter (fun r : F => r ^ 2 = 1)).card +
            (Finset.univ.filter (fun r : F => r ^ 2 = -1)).card :=
          Finset.card_union_le _ _
      _ ≤ (Finset.univ.filter (fun r : F => r ^ 2 = 0)).card +
            (Finset.univ.filter (fun r : F => r ^ 2 = 1)).card +
              (Finset.univ.filter (fun r : F => r ^ 2 = -1)).card :=
          add_le_add (Finset.card_union_le _ _) le_rfl
      _ ≤ 1 + 2 + 2 :=
          add_le_add (add_le_add card_filter_sq_eq_zero_le_one
            (card_filter_sq_eq_le_two (F := F) 1))
            (card_filter_sq_eq_le_two (F := F) (-1))
      _ = 5 := by norm_num
  linarith
