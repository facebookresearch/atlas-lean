/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Bounds.Defs
public import MathlibExt.GameTheory.PenultsOfTak
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# The largest Impartial Tak penult

`MetaMathlibExt.impartialTak_isGreatest_penult_card` gives the maximum number of tokens in a
penult on a square board. The proof counts empty cells by row and constructs a board attaining
the bound.
-/

namespace MetaMathlibExt.impartialTak_isGreatest_penult_card

private abbrev Cell (n : ℕ) := Fin n × Fin n

private theorem road_of_full_row {n : ℕ} {S : Finset (Cell n)} (r : Fin n)
    (h : ∀ c, (r, c) ∈ S) : takHasRoad S := by
  have hn := r.isLt
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have walk (j : ℕ) (hj : j < n) : Relation.ReflTransGen
      (fun x y : Cell n => takAdjacent x y ∧ y ∈ S) (r, first) (r, ⟨j, hj⟩) := by
    induction j with
    | zero => exact .refl
    | succ i ih => exact (ih (by omega)).tail ⟨Or.inl ⟨rfl, Or.inl rfl⟩, h _⟩
  exact ⟨(r, first), h _, (r, last), walk _ _, Or.inl ⟨rfl, by dsimp [last]; omega⟩⟩

private theorem exists_hole {n : ℕ} {S : Finset (Cell n)} (h : ¬ placementTerminal takHasRoad S)
    (r : Fin n) : ∃ c, (r, c) ∉ S := by
  by_contra! hf
  exact h (.inl (road_of_full_row r hf))

private def holesInRow {n : ℕ} (S : Finset (Cell n)) (r : Fin n) : Finset (Cell n) :=
  Sᶜ.filter fun p => p.1 = r

private theorem card_by_empty_cells {n : ℕ} (S : Finset (Cell n)) :
    S.card = n ^ 2 - ∑ r, (holesInRow S r).card := by
  have rows : Sᶜ.card = ∑ r, (holesInRow S r).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [← rows]
  simpa only [compl_compl, Fintype.card_prod, Fintype.card_fin, sq] using Finset.card_compl Sᶜ

private theorem penult_card_le {n : ℕ} {S : Finset (Cell n)}
    (h : placementPenult takHasRoad S) : S.card ≤ n ^ 2 - 2 * n := by
  have two (r : Fin n) : 2 ≤ (holesInRow S r).card := by
    obtain ⟨c, hc⟩ := exists_hole h.1 r
    obtain ⟨d, hd⟩ := exists_hole (h.2 _ hc).1 r
    simp only [Finset.mem_insert, Prod.mk.injEq, true_and, not_or] at hd
    exact Finset.one_lt_card.mpr ⟨(r, c), by simp [holesInRow, hc],
      (r, d), by simp [holesInRow, hd.2], fun he => hd.1 (congrArg Prod.snd he.symm)⟩
  rw [card_by_empty_cells]
  apply Nat.sub_le_sub_left
  simpa [Nat.mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun r _ => two r)

-- The holes in row r are immediately to either side of the diagonal, clamped at the edges.
private def lower {n : ℕ} (r : Fin n) : Fin n := ⟨r.val - 1, by have := r.isLt; omega⟩

private def upper {n : ℕ} (r : Fin n) : Fin n :=
  ⟨min (r.val + 1) (n - 1), by have := r.isLt; omega⟩

private theorem lower_ne_upper {n : ℕ} (hn : 2 ≤ n) (r : Fin n) : lower r ≠ upper r := by
  intro he
  have := congrArg Fin.val he
  dsimp [lower, upper] at this
  have := r.isLt
  omega

private def board (n : ℕ) : Finset (Cell n) :=
  Finset.univ.filter fun p => p.2 ≠ lower p.1 ∧ p.2 ≠ upper p.1

private theorem mem_board {n : ℕ} (p : Cell n) :
    p ∈ board n ↔ p.2 ≠ lower p.1 ∧ p.2 ≠ upper p.1 := by simp [board]

private theorem notMem_board {n : ℕ} (p : Cell n) :
    p ∉ board n ↔ p.2 = lower p.1 ∨ p.2 = upper p.1 := by
  simp only [mem_board, not_and_or, not_not]

private theorem mem_board_swap {n : ℕ} {p : Cell n} (hp : p ∈ board n) :
    p.swap ∈ board n := by
  obtain ⟨r, c⟩ := p
  simp only [mem_board, Prod.swap_prod_mk, ne_eq, Fin.ext_iff, lower, upper] at *
  have := r.isLt
  have := c.isLt
  omega

private theorem board_card {n : ℕ} (hn : 2 ≤ n) : (board n).card = n ^ 2 - 2 * n := by
  have row (r : Fin n) : holesInRow (board n) r = {(r, lower r), (r, upper r)} := by
    ext ⟨s, c⟩
    by_cases h : s = r
    · subst s
      simp [holesInRow, notMem_board]
    · simp [holesInRow, h]
  rw [card_by_empty_cells]
  simp [row, lower_ne_upper hn, Nat.mul_comm]

-- A horizontal road must cross the graph of either clamped diagonal. After a single
-- insertion at least one of the two graphs still consists entirely of holes.
private theorem no_horizontal {n : ℕ} (hn : 2 ≤ n) (p : Cell n) {a b : Cell n}
    (ha : a ∈ insert p (board n))
    (path : Relation.ReflTransGen (fun x y => takAdjacent x y ∧ y ∈ insert p (board n)) a b)
    (left : a.2.val = 0) (right : b.2.val + 1 = n) : False := by
  let wall : Fin n → Fin n := if p.2 = lower p.1 then upper else lower
  have avoids {x : Cell n} (hx : x ∈ insert p (board n)) : x.2 ≠ wall x.1 := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · dsimp only [wall]
      split_ifs with he
      · exact he ▸ lower_ne_upper hn _
      · exact he
    · obtain ⟨hl, hu⟩ := (mem_board _).mp hx
      dsimp only [wall]
      split <;> assumption
  have side {z : Cell n} (w : Relation.ReflTransGen
      (fun x y => takAdjacent x y ∧ y ∈ insert p (board n)) a z) : z.2.val < (wall z.1).val := by
    induction w with
    | refl =>
      have ne := (Fin.val_ne_of_ne (avoids ha))
      omega
    | @tail x y _ step ih =>
      obtain ⟨hxy, hy⟩ := step
      have ne := Fin.val_ne_of_ne (avoids hy)
      rcases hxy with ⟨hr, hc⟩ | ⟨hc, hr⟩
      · rw [hr] at ih
        omega
      · have eq := congrArg Fin.val hc
        dsimp only [wall] at ih ne ⊢
        split_ifs at * <;> dsimp only [upper, lower] at * <;> omega
  have := side path
  have := (wall b.1).isLt
  omega

private theorem no_road_insert {n : ℕ} (hn : 2 ≤ n) (p : Cell n) :
    ¬ takHasRoad (insert p (board n)) := by
  rintro ⟨a, ha, b, path, ends⟩
  rcases ends with ⟨left, right⟩ | ⟨top, bottom⟩
  · exact no_horizontal hn p ha path left right
  · have swap_mem {x : Cell n} (hx : x ∈ insert p (board n)) :
        x.swap ∈ insert p.swap (board n) := by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_insert_self ..
      · exact Finset.mem_insert_of_mem (mem_board_swap hx)
    apply no_horizontal hn p.swap (swap_mem ha) (b := b.swap) _ top bottom
    apply path.lift Prod.swap
    rintro x y ⟨hxy, hy⟩
    exact ⟨hxy.symm, swap_mem hy⟩

private theorem nonterminal_of_subset {n : ℕ} (hn : 2 ≤ n) (p : Cell n) {S : Finset (Cell n)}
    (hsub : S ⊆ insert p (board n)) : ¬ placementTerminal takHasRoad S := by
  apply mt _ (no_road_insert hn p)
  rintro (⟨a, ha, b, path, ends⟩ | rfl)
  · refine ⟨a, hsub ha, b, ?_, ends⟩
    exact Relation.ReflTransGen.mono (fun _ _ step => ⟨step.1, hsub step.2⟩) a b path
  · exact road_of_full_row p.1 (fun _ => hsub (Finset.mem_univ _))

private theorem board_penult {n : ℕ} (hn : 2 ≤ n) : placementPenult takHasRoad (board n) := by
  let z : Fin n := ⟨0, by omega⟩
  refine ⟨nonterminal_of_subset hn (z, z) (Finset.subset_insert ..), ?_⟩
  rintro ⟨r, c⟩ hc
  refine ⟨nonterminal_of_subset hn (r, c) (Finset.Subset.refl _), ?_⟩
  have reply (d : Fin n) (hne : d ≠ c) (hd : (r, d) ∉ board n)
      (holes : ∀ j, (r, j) ∉ board n → j = d ∨ j = c) :
      ∃ q ∉ insert (r, c) (board n), placementTerminal takHasRoad (insert q (insert (r, c)
        (board n))) := by
    refine ⟨(r, d), by simp [hne, hd], Or.inl (road_of_full_row r ?_)⟩
    intro j
    by_cases hj : (r, j) ∈ board n
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj)
    · rcases holes j hj with rfl | rfl <;> simp
  have h : c = lower r ∨ c = upper r := (notMem_board _).mp hc
  rcases h with rfl | rfl
  · apply reply (upper r) (lower_ne_upper hn r).symm (by simp [mem_board])
    simp [notMem_board, or_comm]
  · apply reply (lower r) (lower_ne_upper hn r) (by simp [mem_board])
    simp [notMem_board]

end MetaMathlibExt.impartialTak_isGreatest_penult_card

namespace MetaMathlibExt

open impartialTak_isGreatest_penult_card

/-- **The largest Impartial Tak penult.** Impartial Tak is the placement game on the $n \times n$
board whose play ends once the tokens contain a road. For every $n \ge 2$, the largest number of
tokens in an Impartial Tak penult on the $n \times n$ board is $U(n) = n^2 - 2n$: some penult has
exactly $n^2 - 2n$ tokens and no penult has more.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Corollary 1 (`integers-2025-G1-cor-1`). -/
public theorem impartialTak_isGreatest_penult_card {n : ℕ} (hn : 2 ≤ n) :
    IsGreatest {x | ∃ S : Finset (Fin n × Fin n), placementPenult takHasRoad S ∧ S.card = x}
      (n ^ 2 - 2 * n) := by
  refine ⟨⟨board n, board_penult hn, board_card hn⟩, ?_⟩
  rintro _ ⟨S, hS, rfl⟩
  exact penult_card_le hS

end MetaMathlibExt
