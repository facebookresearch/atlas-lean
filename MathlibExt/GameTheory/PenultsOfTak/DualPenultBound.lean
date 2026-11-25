/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.PenultsOfTak
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Token bound for dual Impartial Tic penults

`MetaMathlibExt.impartialTic_dual_penult_card_le` bounds the number of empty
cells of an Impartial Tic penult on an `n × n` board, for `n ≥ 5`, by `4 * (n - 2)`.
Equivalently, a penult of the dual game has at most `4 * (n - 2)` tokens.
-/

namespace MetaMathlibExt.impartialTic_dual_penult_card_le

private abbrev Cell (n : ℕ) := Fin n × Fin n

/-- The empty cells of `S` in row `r`, as a finset of cells. -/
private def rowHoles {n : ℕ} (S : Finset (Cell n)) (r : Fin n) : Finset (Cell n) :=
  (Finset.univ \ S).filter fun p => p.1 = r

/-- The empty cells of `S` in column `c`, as a finset of cells. -/
private def colHoles {n : ℕ} (S : Finset (Cell n)) (c : Fin n) : Finset (Cell n) :=
  (Finset.univ \ S).filter fun p => p.2 = c

private theorem rowHoles_image {n : ℕ} (S : Finset (Cell n)) (r : Fin n) :
    rowHoles S r = (Finset.univ.filter fun c => (r, c) ∉ S).image (fun c => (r, c)) := by
  ext ⟨a, b⟩
  simp only [rowHoles, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨hnot, hr⟩
    refine ⟨b, ?_, Prod.ext hr.symm rfl⟩
    rwa [← hr]
  · rintro ⟨c, hc, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨hc, rfl⟩

private theorem rowHoles_card_eq {n : ℕ} (S : Finset (Cell n)) (r : Fin n) :
    (rowHoles S r).card = (Finset.univ.filter fun c => (r, c) ∉ S).card := by
  rw [rowHoles_image, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]

private theorem colHoles_image {n : ℕ} (S : Finset (Cell n)) (c : Fin n) :
    colHoles S c = (Finset.univ.filter fun r => (r, c) ∉ S).image (fun r => (r, c)) := by
  ext ⟨a, b⟩
  simp only [colHoles, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨hnot, hc⟩
    refine ⟨a, ?_, Prod.ext rfl hc.symm⟩
    rwa [← hc]
  · rintro ⟨r, hr, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨hr, rfl⟩

private theorem colHoles_card_eq {n : ℕ} (S : Finset (Cell n)) (c : Fin n) :
    (colHoles S c).card = (Finset.univ.filter fun r => (r, c) ∉ S).card := by
  rw [colHoles_image, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]

-- A line completed by two moves must contain the first move if the reply alone
-- would not complete it. Its original holes can only be the two played cells.
private theorem holes_on_completed_line {n : ℕ} {S : Finset (Cell n)} {p q : Cell n}
    (line : Fin n → Cell n) (coord : Cell n → Fin n)
    (hcoord : Function.LeftInverse coord line)
    (hfull : ∀ i, line i ∈ insert q (insert p S)) (hprev : ¬ ∀ i, line i ∈ insert q S) :
    (∃ i, line i = p) ∧ (Finset.univ.filter fun i => line i ∉ S).card ≤ 2 := by
  constructor
  · by_contra! h
    exact hprev fun i => by simpa [Finset.mem_insert, h i] using hfull i
  · suffices (Finset.univ.filter fun i => line i ∉ S) ⊆ {coord q, coord p} from
      (Finset.card_le_card this).trans Finset.card_le_two
    intro i hi
    have h := hfull i
    simp only [Finset.mem_insert, (Finset.mem_filter.mp hi).2, or_false] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton, hcoord i] using
      h.imp (congrArg coord) (congrArg coord)

/-- If `p` is an empty cell of a penult, its row or its column has at most two
empty cells: the reply to playing `p` completes a row or a column through `p`,
and that line had at most the two played cells empty. -/
private theorem row_or_col_le_two {n : ℕ} {S : Finset (Cell n)}
    (hS : placementPenult (ticEnded n) S) {p : Cell n} (hp : p ∉ S) :
    (rowHoles S p.1).card ≤ 2 ∨ (colHoles S p.2).card ≤ 2 := by
  obtain ⟨q, hq, hterminal⟩ := (hS.2 p hp).2
  have hqS : q ∉ S := fun h => hq (Finset.mem_insert_of_mem h)
  have hprev : ¬ placementTerminal (ticEnded n) (insert q S) := (hS.2 q hqS).1
  rcases hterminal with htic | huniv
  · rcases htic with ⟨i, hi⟩ | ⟨j, hj⟩
    · obtain ⟨⟨k, hk⟩, hcard⟩ := holes_on_completed_line (fun k => (i, k)) Prod.snd
        (fun _ => rfl) hi (fun h => hprev (Or.inl (Or.inl ⟨i, h⟩)))
      have hi' : i = p.1 := congrArg Prod.fst hk
      left
      rw [rowHoles_card_eq, ← hi']
      exact hcard
    · obtain ⟨⟨k, hk⟩, hcard⟩ := holes_on_completed_line (fun k => (k, j)) Prod.fst
        (fun _ => rfl) hj (fun h => hprev (Or.inl (Or.inr ⟨j, h⟩)))
      have hj' : j = p.2 := congrArg Prod.snd hk
      right
      rw [colHoles_card_eq, ← hj']
      exact hcard
  · -- The two moves fill the board, so the row through `p` has at most two holes.
    left
    rw [rowHoles_card_eq]
    have hsub : Finset.univ.filter (fun c => (p.1, c) ∉ S) ⊆ {p.2, q.2} := by
      intro c hc
      have hmem : (p.1, c) ∈ insert q (insert p S) := huniv ▸ Finset.mem_univ _
      simp only [Finset.mem_insert] at hmem
      rcases hmem with h1 | h1 | hmemS
      · have h2 : c = q.2 := congrArg Prod.snd h1
        rw [h2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · have h2 : c = p.2 := congrArg Prod.snd h1
        rw [h2]; exact Finset.mem_insert_self _ _
      · exact ((Finset.mem_filter.mp hc).2 hmemS).elim
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- Every row of a penult has a hole, since no row is full. -/
private theorem exists_row_hole {n : ℕ} {S : Finset (Cell n)}
    (hS : placementPenult (ticEnded n) S) (r : Fin n) : ∃ c, (r, c) ∉ S := by
  by_contra! hf
  exact hS.1 (Or.inl (Or.inl ⟨r, hf⟩))

/-- Every column of a penult has a hole, since no column is full. -/
private theorem exists_col_hole {n : ℕ} {S : Finset (Cell n)}
    (hS : placementPenult (ticEnded n) S) (c : Fin n) : ∃ r, (r, c) ∉ S := by
  by_contra! hf
  exact hS.1 (Or.inl (Or.inr ⟨c, hf⟩))

/-- Every row of a penult has at least two holes: with exactly one hole,
playing it would complete the row, so the resulting position would be
terminal rather than an ult. -/
private theorem two_le_rowHoles {n : ℕ} {S : Finset (Cell n)}
    (hS : placementPenult (ticEnded n) S) (r : Fin n) : 2 ≤ (rowHoles S r).card := by
  rw [rowHoles_card_eq]
  obtain ⟨c₀, hc₀⟩ := exists_row_hole hS r
  by_contra hlt
  have hle : (Finset.univ.filter fun c => (r, c) ∉ S).card ≤ 1 := by omega
  have hsub : Finset.univ.filter (fun c => (r, c) ∉ S) ⊆ {c₀} := by
    intro c hc
    simp only [Finset.mem_singleton]
    by_contra hne
    have hc₀mem : c₀ ∈ Finset.univ.filter (fun c => (r, c) ∉ S) := by
      simp [hc₀]
    have h2 := Finset.one_lt_card.mpr ⟨c₀, hc₀mem, c, hc, fun h => hne h.symm⟩
    omega
  have hfull : ∀ c, (r, c) ∈ insert (r, c₀) S := by
    intro c
    by_cases hc : (r, c) ∈ S
    · exact Finset.mem_insert_of_mem hc
    · have : c = c₀ := by
        have := hsub (by simp [hc] : c ∈ Finset.univ.filter (fun c => (r, c) ∉ S))
        exact Finset.mem_singleton.mp this
      subst this
      exact Finset.mem_insert_self _ _
  exact (hS.2 (r, c₀) hc₀).1 (Or.inl (Or.inl ⟨r, hfull⟩))

/-- Every column of a penult has at least two holes, by the symmetric argument. -/
private theorem two_le_colHoles {n : ℕ} {S : Finset (Cell n)}
    (hS : placementPenult (ticEnded n) S) (c : Fin n) : 2 ≤ (colHoles S c).card := by
  rw [colHoles_card_eq]
  obtain ⟨r₀, hr₀⟩ := exists_col_hole hS c
  by_contra hlt
  have hle : (Finset.univ.filter fun r => (r, c) ∉ S).card ≤ 1 := by omega
  have hsub : Finset.univ.filter (fun r => (r, c) ∉ S) ⊆ {r₀} := by
    intro r hr
    simp only [Finset.mem_singleton]
    by_contra hne
    have hr₀mem : r₀ ∈ Finset.univ.filter (fun r => (r, c) ∉ S) := by
      simp [hr₀]
    have h2 := Finset.one_lt_card.mpr ⟨r₀, hr₀mem, r, hr, fun h => hne h.symm⟩
    omega
  have hfull : ∀ r, (r, c) ∈ insert (r₀, c) S := by
    intro r
    by_cases hr : (r, c) ∈ S
    · exact Finset.mem_insert_of_mem hr
    · have : r = r₀ := by
        have := hsub (by simp [hr] : r ∈ Finset.univ.filter (fun r => (r, c) ∉ S))
        exact Finset.mem_singleton.mp this
      subst this
      exact Finset.mem_insert_self _ _
  exact (hS.2 (r₀, c) hr₀).1 (Or.inl (Or.inr ⟨c, hfull⟩))

private theorem card_filter_fst_eq_sum {n : ℕ} (T : Finset (Cell n))
    (P : Fin n → Prop) [DecidablePred P] :
    (T.filter fun p => P p.1).card =
      ∑ r ∈ Finset.univ.filter P, (T.filter fun p => p.1 = r).card := by
  have hfib := Finset.card_eq_sum_card_fiberwise (s := T.filter fun p => P p.1)
    (f := Prod.fst) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [hfib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hP : P r
  · simp only [hP, ite_true]
    have heq : (T.filter fun p => P p.1).filter (fun p => p.1 = r) =
        T.filter fun p => p.1 = r := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro a _
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨h ▸ hP, h⟩
    rw [heq]
  · simp only [hP, ite_false]
    have heq : (T.filter fun p => P p.1).filter (fun p => p.1 = r) = ∅ := by
      rw [Finset.filter_filter]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have ha' := Finset.mem_filter.mp ha
      exact hP (ha'.2.2 ▸ ha'.2.1)
    rw [heq, Finset.card_empty]

private theorem card_filter_snd_eq_sum {n : ℕ} (T : Finset (Cell n))
    (P : Fin n → Prop) [DecidablePred P] :
    (T.filter fun p => P p.2).card =
      ∑ c ∈ Finset.univ.filter P, (T.filter fun p => p.2 = c).card := by
  have hfib := Finset.card_eq_sum_card_fiberwise (s := T.filter fun p => P p.2)
    (f := Prod.snd) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [hfib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hP : P c
  · simp only [hP, ite_true]
    have heq : (T.filter fun p => P p.2).filter (fun p => p.2 = c) =
        T.filter fun p => p.2 = c := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro a _
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨h ▸ hP, h⟩
    rw [heq]
  · simp only [hP, ite_false]
    have heq : (T.filter fun p => P p.2).filter (fun p => p.2 = c) = ∅ := by
      rw [Finset.filter_filter]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have ha' := Finset.mem_filter.mp ha
      exact hP (ha'.2.2 ▸ ha'.2.1)
    rw [heq, Finset.card_empty]

private theorem sum_rowHoles {n : ℕ} (S : Finset (Cell n)) :
    ∑ r, (rowHoles S r).card = (Finset.univ \ S).card := by
  calc
    ∑ r, (rowHoles S r).card
      = ∑ r, ((Finset.univ \ S).filter fun p => p.1 = r).card :=
        Finset.sum_congr rfl fun r _ => rfl
  _ = (Finset.univ \ S).card := (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ \ S) (f := Prod.fst) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm

private theorem sum_colHoles {n : ℕ} (S : Finset (Cell n)) :
    ∑ c, (colHoles S c).card = (Finset.univ \ S).card := by
  calc
    ∑ c, (colHoles S c).card
      = ∑ c, ((Finset.univ \ S).filter fun p => p.2 = c).card :=
        Finset.sum_congr rfl fun c _ => rfl
  _ = (Finset.univ \ S).card := (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ \ S) (f := Prod.snd) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm

/-- A row with at least three holes has all its holes in columns with at most
two holes, and hence at most as many holes as there are such columns. -/
private theorem rowHoles_card_le_goodCols {n : ℕ} {S : Finset (Cell n)}
    (hS : placementPenult (ticEnded n) S) {r : Fin n}
    (hr : ¬ (rowHoles S r).card ≤ 2) :
    (rowHoles S r).card ≤
      (Finset.univ.filter fun c => (colHoles S c).card ≤ 2).card := by
  rw [rowHoles_card_eq]
  apply Finset.card_le_card
  intro c hc
  have hcS : (r, c) ∉ S := (Finset.mem_filter.mp hc).2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases row_or_col_le_two hS hcS with h | h
  · exact absurd h hr
  · exact h

/-- A column with at least three holes has all its holes in rows with at most
two holes, and hence at most as many holes as there are such rows. -/
private theorem colHoles_card_le_goodRows {n : ℕ} {S : Finset (Cell n)}
    (hS : placementPenult (ticEnded n) S) {c : Fin n}
    (hc : ¬ (colHoles S c).card ≤ 2) :
    (colHoles S c).card ≤
      (Finset.univ.filter fun r => (rowHoles S r).card ≤ 2).card := by
  rw [colHoles_card_eq]
  apply Finset.card_le_card
  intro r hr
  have hrS : (r, c) ∉ S := (Finset.mem_filter.mp hr).2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases row_or_col_le_two hS hrS with h | h
  · exact h
  · exact absurd h hc

/-- The holes in rows with at least three holes are at most twice the number
of columns with at most two holes: every such hole lies in a column with at
most two holes, and each such column has exactly two holes. -/
private theorem sum_badRows_le {n : ℕ} {S : Finset (Cell n)}
    (hS : placementPenult (ticEnded n) S) :
    ∑ r ∈ Finset.univ.filter (fun r => ¬ (rowHoles S r).card ≤ 2), (rowHoles S r).card ≤
      2 * (Finset.univ.filter fun c => (colHoles S c).card ≤ 2).card := by
  have hsub : (Finset.univ \ S).filter (fun p => ¬ (rowHoles S p.1).card ≤ 2) ⊆
      (Finset.univ \ S).filter (fun p => (colHoles S p.2).card ≤ 2) := by
    intro p hp
    have hpS : p ∉ S := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).2
    have hp1 : ¬ (rowHoles S p.1).card ≤ 2 := (Finset.mem_filter.mp hp).2
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    refine ⟨hpS, ?_⟩
    rcases row_or_col_le_two hS hpS with h | h
    · exact absurd h hp1
    · exact h
  have hA := card_filter_fst_eq_sum (Finset.univ \ S)
    (fun r => ¬ (rowHoles S r).card ≤ 2)
  have hB := card_filter_snd_eq_sum (Finset.univ \ S)
    (fun c => (colHoles S c).card ≤ 2)
  have hB2 : ∑ c ∈ Finset.univ.filter (fun c => (colHoles S c).card ≤ 2),
      (colHoles S c).card =
      2 * (Finset.univ.filter fun c => (colHoles S c).card ≤ 2).card := by
    have hsum : ∑ c ∈ Finset.univ.filter (fun c => (colHoles S c).card ≤ 2),
        (colHoles S c).card =
        ∑ _c ∈ Finset.univ.filter (fun c => (colHoles S c).card ≤ 2), 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      have hc2 : (colHoles S c).card ≤ 2 := (Finset.mem_filter.mp hc).2
      exact le_antisymm hc2 (two_le_colHoles hS c)
    rw [hsum, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  calc
    ∑ r ∈ Finset.univ.filter (fun r => ¬ (rowHoles S r).card ≤ 2), (rowHoles S r).card
      = ((Finset.univ \ S).filter fun p => ¬ (rowHoles S p.1).card ≤ 2).card := hA.symm
  _ ≤ ((Finset.univ \ S).filter fun p => (colHoles S p.2).card ≤ 2).card :=
      Finset.card_le_card hsub
  _ = ∑ c ∈ Finset.univ.filter (fun c => (colHoles S c).card ≤ 2),
        (colHoles S c).card := hB
  _ = 2 * (Finset.univ.filter fun c => (colHoles S c).card ≤ 2).card := hB2

/-- The symmetric bound for the holes in columns with at least three holes. -/
private theorem sum_badCols_le {n : ℕ} {S : Finset (Cell n)}
    (hS : placementPenult (ticEnded n) S) :
    ∑ c ∈ Finset.univ.filter (fun c => ¬ (colHoles S c).card ≤ 2), (colHoles S c).card ≤
      2 * (Finset.univ.filter fun r => (rowHoles S r).card ≤ 2).card := by
  have hsub : (Finset.univ \ S).filter (fun p => ¬ (colHoles S p.2).card ≤ 2) ⊆
      (Finset.univ \ S).filter (fun p => (rowHoles S p.1).card ≤ 2) := by
    intro p hp
    have hpS : p ∉ S := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).2
    have hp2 : ¬ (colHoles S p.2).card ≤ 2 := (Finset.mem_filter.mp hp).2
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    refine ⟨hpS, ?_⟩
    rcases row_or_col_le_two hS hpS with h | h
    · exact h
    · exact absurd h hp2
  have hA := card_filter_snd_eq_sum (Finset.univ \ S)
    (fun c => ¬ (colHoles S c).card ≤ 2)
  have hB := card_filter_fst_eq_sum (Finset.univ \ S)
    (fun r => (rowHoles S r).card ≤ 2)
  have hB2 : ∑ r ∈ Finset.univ.filter (fun r => (rowHoles S r).card ≤ 2),
      (rowHoles S r).card =
      2 * (Finset.univ.filter fun r => (rowHoles S r).card ≤ 2).card := by
    have hsum : ∑ r ∈ Finset.univ.filter (fun r => (rowHoles S r).card ≤ 2),
        (rowHoles S r).card =
        ∑ _r ∈ Finset.univ.filter (fun r => (rowHoles S r).card ≤ 2), 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr2 : (rowHoles S r).card ≤ 2 := (Finset.mem_filter.mp hr).2
      exact le_antisymm hr2 (two_le_rowHoles hS r)
    rw [hsum, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  calc
    ∑ c ∈ Finset.univ.filter (fun c => ¬ (colHoles S c).card ≤ 2), (colHoles S c).card
      = ((Finset.univ \ S).filter fun p => ¬ (colHoles S p.2).card ≤ 2).card := hA.symm
  _ ≤ ((Finset.univ \ S).filter fun p => (rowHoles S p.1).card ≤ 2).card :=
      Finset.card_le_card hsub
  _ = ∑ r ∈ Finset.univ.filter (fun r => (rowHoles S r).card ≤ 2),
        (rowHoles S r).card := hB
  _ = 2 * (Finset.univ.filter fun r => (rowHoles S r).card ≤ 2).card := hB2

end MetaMathlibExt.impartialTic_dual_penult_card_le

namespace MetaMathlibExt

open impartialTic_dual_penult_card_le

/-- **Token bound for dual Impartial Tic penults.** Let $n \ge 5$. If $S$ is a penult of
Impartial Tic on the $n \times n$ board, then at most $4(n - 2)$ cells of the board lie outside
$S$.

In the dual of Impartial Tic, tokens are removed from a full board and play ends once some row or
column is empty; its penults are the sets of empty cells of Impartial Tic penults, so this says
that a penult of the dual game on the $n \times n$ board has at most $4(n - 2)$ tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 4 (`integers-2025-G1-prop-4`). -/
public theorem impartialTic_dual_penult_card_le {n : ℕ} (hn : 5 ≤ n)
    {S : Finset (Fin n × Fin n)} (hS : placementPenult (ticEnded n) S) :
    (Finset.univ \ S).card ≤ 4 * (n - 2) := by
  have hmR : (Finset.univ \ S).card =
      ∑ r ∈ Finset.univ.filter (fun r => (rowHoles S r).card ≤ 2), (rowHoles S r).card +
      ∑ r ∈ Finset.univ.filter (fun r => ¬ (rowHoles S r).card ≤ 2), (rowHoles S r).card := by
    rw [← sum_rowHoles S]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hmC : (Finset.univ \ S).card =
      ∑ c ∈ Finset.univ.filter (fun c => (colHoles S c).card ≤ 2), (colHoles S c).card +
      ∑ c ∈ Finset.univ.filter (fun c => ¬ (colHoles S c).card ≤ 2), (colHoles S c).card := by
    rw [← sum_colHoles S]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hgoodR : ∑ r ∈ Finset.univ.filter (fun r => (rowHoles S r).card ≤ 2),
      (rowHoles S r).card =
      2 * (Finset.univ.filter fun r => (rowHoles S r).card ≤ 2).card := by
    have hsum : ∑ r ∈ Finset.univ.filter (fun r => (rowHoles S r).card ≤ 2),
        (rowHoles S r).card =
        ∑ _r ∈ Finset.univ.filter (fun r => (rowHoles S r).card ≤ 2), 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr2 : (rowHoles S r).card ≤ 2 := (Finset.mem_filter.mp hr).2
      exact le_antisymm hr2 (two_le_rowHoles hS r)
    rw [hsum, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  have hgoodC : ∑ c ∈ Finset.univ.filter (fun c => (colHoles S c).card ≤ 2),
      (colHoles S c).card =
      2 * (Finset.univ.filter fun c => (colHoles S c).card ≤ 2).card := by
    have hsum : ∑ c ∈ Finset.univ.filter (fun c => (colHoles S c).card ≤ 2),
        (colHoles S c).card =
        ∑ _c ∈ Finset.univ.filter (fun c => (colHoles S c).card ≤ 2), 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      have hc2 : (colHoles S c).card ≤ 2 := (Finset.mem_filter.mp hc).2
      exact le_antisymm hc2 (two_le_colHoles hS c)
    rw [hsum, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  have hcardR : (Finset.univ.filter fun r => ¬ (rowHoles S r).card ≤ 2).card +
      (Finset.univ.filter fun r => (rowHoles S r).card ≤ 2).card = n := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun r => (rowHoles S r).card ≤ 2)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  have hcardC : (Finset.univ.filter fun c => ¬ (colHoles S c).card ≤ 2).card +
      (Finset.univ.filter fun c => (colHoles S c).card ≤ 2).card = n := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun c => (colHoles S c).card ≤ 2)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  have hbadR := sum_badRows_le hS
  by_cases hcase : (Finset.univ.filter fun r => (rowHoles S r).card ≤ 2).card +
      (Finset.univ.filter fun c => (colHoles S c).card ≤ 2).card ≤ 2 * (n - 2)
  · calc
      (Finset.univ \ S).card
        = ∑ r ∈ Finset.univ.filter (fun r => (rowHoles S r).card ≤ 2), (rowHoles S r).card +
          ∑ r ∈ Finset.univ.filter (fun r => ¬ (rowHoles S r).card ≤ 2),
            (rowHoles S r).card := hmR
    _ ≤ 2 * (Finset.univ.filter fun r => (rowHoles S r).card ≤ 2).card +
          2 * (Finset.univ.filter fun c => (colHoles S c).card ≤ 2).card := by
        rw [hgoodR]
        exact Nat.add_le_add_left hbadR _
    _ ≤ 4 * (n - 2) := by omega
  · have hsmall : (Finset.univ.filter fun r => ¬ (rowHoles S r).card ≤ 2).card +
        (Finset.univ.filter fun c => ¬ (colHoles S c).card ≤ 2).card ≤ 3 := by omega
    have hperR : ∑ r ∈ Finset.univ.filter (fun r => ¬ (rowHoles S r).card ≤ 2),
        (rowHoles S r).card ≤
        (Finset.univ.filter fun r => ¬ (rowHoles S r).card ≤ 2).card *
          (Finset.univ.filter fun c => (colHoles S c).card ≤ 2).card := by
      have hle := Finset.sum_le_sum (s := Finset.univ.filter
        (fun r => ¬ (rowHoles S r).card ≤ 2)) (f := fun r => (rowHoles S r).card)
        (g := fun _ => (Finset.univ.filter fun c => (colHoles S c).card ≤ 2).card)
        (fun r hr => rowHoles_card_le_goodCols hS (Finset.mem_filter.mp hr).2)
      rwa [Finset.sum_const, nsmul_eq_mul] at hle
    have hperC : ∑ c ∈ Finset.univ.filter (fun c => ¬ (colHoles S c).card ≤ 2),
        (colHoles S c).card ≤
        (Finset.univ.filter fun c => ¬ (colHoles S c).card ≤ 2).card *
          (Finset.univ.filter fun r => (rowHoles S r).card ≤ 2).card := by
      have hle := Finset.sum_le_sum (s := Finset.univ.filter
        (fun c => ¬ (colHoles S c).card ≤ 2)) (f := fun c => (colHoles S c).card)
        (g := fun _ => (Finset.univ.filter fun r => (rowHoles S r).card ≤ 2).card)
        (fun c hc => colHoles_card_le_goodRows hS (Finset.mem_filter.mp hc).2)
      rwa [Finset.sum_const, nsmul_eq_mul] at hle
    have hUrow : (Finset.univ \ S).card ≤
        2 * (Finset.univ.filter fun r => (rowHoles S r).card ≤ 2).card +
        (Finset.univ.filter fun r => ¬ (rowHoles S r).card ≤ 2).card *
          (Finset.univ.filter fun c => (colHoles S c).card ≤ 2).card := by
      rw [hmR, hgoodR]
      exact Nat.add_le_add_left hperR _
    have hUcol : (Finset.univ \ S).card ≤
        2 * (Finset.univ.filter fun c => (colHoles S c).card ≤ 2).card +
        (Finset.univ.filter fun c => ¬ (colHoles S c).card ≤ 2).card *
          (Finset.univ.filter fun r => (rowHoles S r).card ≤ 2).card := by
      rw [hmC, hgoodC]
      exact Nat.add_le_add_left hperC _
    have hcasesR : (Finset.univ.filter fun r => ¬ (rowHoles S r).card ≤ 2).card = 0 ∨
        (Finset.univ.filter fun r => ¬ (rowHoles S r).card ≤ 2).card = 1 ∨
        (Finset.univ.filter fun r => ¬ (rowHoles S r).card ≤ 2).card = 2 ∨
        (Finset.univ.filter fun r => ¬ (rowHoles S r).card ≤ 2).card = 3 := by omega
    have hcasesC : (Finset.univ.filter fun c => ¬ (colHoles S c).card ≤ 2).card = 0 ∨
        (Finset.univ.filter fun c => ¬ (colHoles S c).card ≤ 2).card = 1 ∨
        (Finset.univ.filter fun c => ¬ (colHoles S c).card ≤ 2).card = 2 ∨
        (Finset.univ.filter fun c => ¬ (colHoles S c).card ≤ 2).card = 3 := by omega
    rcases hcasesR with hk | hk | hk | hk <;>
      rcases hcasesC with hl | hl | hl | hl <;>
      rw [hk] at hUrow <;> rw [hl] at hUcol <;> omega

end MetaMathlibExt
