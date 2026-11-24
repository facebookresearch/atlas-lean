/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.GridLRamsey
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat

/-!
# Monochromatic L-shapes in the three-colored 772 × 772 grid

Counting distances between pairs of nearby ranks on the main diagonal gives the upper bound
772 for the three-color grid Ramsey number of the L.
-/

namespace MetaMathlibExt

namespace gridLRamseyProperty_three_772

open Finset

-- Summing the gaps of a fixed rank difference cancels the interior marks. Only the first
-- and last k marks remain, and their spacing saves k - 1 units per pair of endpoints.
private lemma sum_rank_gaps_le (f : ℕ → ℕ) (hf : StrictMono f) (h₀ : 0 < f 0)
    (hmax : f 257 ≤ 772) {k : ℕ} (hk : k ≤ 258) :
    ∑ i ∈ range (258 - k), (f (k + i) - f i) ≤ k * (772 - k) := by
  have ends (i : ℕ) (hi : i < k) : f (258 - k + i) ≤ f i + (772 - k) := by
    have hfirst := hf.add_le_nat i 0
    have hlast := hf.add_le_nat (k - 1 - i) (258 - k + i)
    rw [show k - 1 - i + (258 - k + i) = 257 by omega] at hlast
    simp only [Nat.add_zero] at hfirst
    omega
  have hsum := sum_le_sum (s := range k) fun i hi => ends i (mem_range.mp hi)
  rw [sum_add_distrib] at hsum
  simp only [sum_const, card_range, Nat.nsmul_eq_mul] at hsum
  have hsplit := sum_range_add f k (258 - k)
  have hsplit' := sum_range_add f (258 - k) k
  rw [Nat.add_comm k (258 - k)] at hsplit
  rw [sum_tsub_distrib _ fun i _ => hf.monotone (Nat.le_add_left i k)]
  omega

-- If each positive distance occurs at most 78 times, bound the total shortfall below 39
-- by summing 78 copies of each possible shortfall.
private lemma shortfall_le {α : Type*} (P : Finset α) (gap : α → ℕ)
    (hpos : ∀ p ∈ P, 0 < gap p)
    (hcap : ∀ d, 0 < d → (P.filter fun p => gap p = d).card ≤ 78) :
    ∑ p ∈ P, (39 - gap p) ≤ 57798 := by
  have expand (p : α) (hp : p ∈ P) :
      39 - gap p = ∑ d ∈ Icc 1 38, if gap p = d then 39 - d else 0 := by
    rw [sum_ite_eq]
    split_ifs with h
    · rfl
    · have := hpos p hp
      simp only [mem_Icc] at h
      omega
  calc
    _ = ∑ d ∈ Icc 1 38, ∑ p ∈ P, if gap p = d then 39 - d else 0 := by
      rw [sum_congr rfl expand, sum_comm]
    _ ≤ ∑ d ∈ Icc 1 38, 78 * (39 - d) := by
      refine sum_le_sum fun d hd => ?_
      rw [← sum_filter, sum_const, Nat.nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ (hcap d (mem_Icc.mp hd).1)
    _ = 57798 := by decide

-- Among 258 marks in [1, 772], some positive distance occurs in at least 79 pairs.
private lemma frequent_distance (S : Finset ℕ) (hS : S ⊆ Icc 1 772) (hcard : 257 < S.card) :
    ∃ d, 0 < d ∧ 78 < (S.filter fun x => x + d ∈ S).card := by
  -- Enumerate the marks in order. The extension beyond S.card lets us sum over natural indices.
  let f (i : ℕ) := if hi : i < S.card then S.orderEmbOfFin rfl ⟨i, hi⟩ else 773 + i
  have hmem (i : ℕ) (hi : i < S.card) : f i ∈ S := by
    simpa only [f, dite_eq_left hi] using S.orderEmbOfFin_mem rfl ⟨i, hi⟩
  have hf : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro i
    by_cases hi : i + 1 < S.card
    · have hi' : i < S.card := by omega
      simp only [f, dite_eq_left hi, dite_eq_left hi']
      exact (S.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
    · simp only [f, dite_eq_right hi]
      split_ifs with hi'
      · have := (mem_Icc.mp (hS (S.orderEmbOfFin_mem rfl ⟨i, hi'⟩))).2
        omega
      · omega
  -- A pair (k, i) records the gap from mark i to mark i + k among the first 258 marks.
  let P : Finset (Σ _ : ℕ, ℕ) := (Icc 1 12).sigma fun k => range (258 - k)
  let gap (p : Σ _ : ℕ, ℕ) := f (p.1 + p.2) - f p.2
  have ranks {k i : ℕ} (hp : (⟨k, i⟩ : Σ _ : ℕ, ℕ) ∈ P) :
      0 < k ∧ k ≤ 12 ∧ k + i < 258 := by
    simp only [P, mem_sigma, mem_Icc, mem_range] at hp
    omega
  have hpos : ∀ p ∈ P, 0 < gap p := by
    rintro ⟨k, i⟩ hp
    change 0 < f (k + i) - f i
    exact Nat.sub_pos_of_lt (hf (Nat.lt_add_of_pos_left (ranks hp).1))
  by_contra! hcap
  have cap (d : ℕ) (hd : 0 < d) : (P.filter fun p => gap p = d).card ≤ 78 := by
    refine le_trans (card_le_card_of_injOn (fun p => f p.2) ?_ ?_) (hcap d hd)
    · rintro ⟨k, i⟩ hp
      obtain ⟨hp, heq⟩ := mem_filter.mp hp
      have hr := ranks hp
      change f (k + i) - f i = d at heq
      have hdiff : f i + d = f (k + i) := by omega
      exact mem_filter.mpr ⟨hmem i (by omega), hdiff ▸ hmem (k + i) (by omega)⟩
    · rintro ⟨k, i⟩ hp ⟨l, j⟩ hq heq
      obtain rfl : i = j := hf.injective heq
      have hp' := (mem_filter.mp hp).2
      have hq' := (mem_filter.mp hq).2
      change f (k + i) - f i = d at hp'
      change f (l + i) - f i = d at hq'
      have : k + i = l + i := hf.injective (by omega)
      obtain rfl : k = l := by omega
      rfl
  have hupper : ∑ p ∈ P, gap p ≤ 59566 := by
    dsimp only [P]
    rw [sum_sigma]
    calc
      _ ≤ ∑ k ∈ Icc 1 12, k * (772 - k) := by
        refine sum_le_sum fun k hk => sum_rank_gaps_le f hf ?_ ?_ ?_
        · exact (mem_Icc.mp (hS (hmem 0 (by omega)))).1
        · exact (mem_Icc.mp (hS (hmem 257 hcard))).2
        · have := (mem_Icc.mp hk).2
          omega
      _ = 59566 := by decide
  have hcount : P.card = 3018 := by
    simp only [P, card_sigma, card_range]
    decide
  -- The 3018 gaps contribute at least 39 each after adding their shortfalls.
  -- Their two upper bounds sum to less than 39 * 3018.
  have htotal := sum_le_sum (s := P)
    (fun p _ => show 39 ≤ gap p + (39 - gap p) by omega)
  rw [sum_add_distrib, sum_const, hcount, Nat.nsmul_eq_mul] at htotal
  have := shortfall_le P gap hpos cap
  omega

end gridLRamseyProperty_three_772

open Finset gridLRamseyProperty_three_772

/-- **Three-coloring the 772 × 772 grid forces a monochromatic L.** Write
$[n] = \{1, \dots, n\}$. Every coloring of the grid $[772] \times [772]$ with $3$ colors contains
a monochromatic L: positive integers $x$, $y$, $d$ with $x + d \le 772$ and $y + d \le 772$ such
that the points $(x, y)$, $(x + d, y)$ and $(x + d, y + d)$ have the same color. Equivalently,
the grid Ramsey number $R_3(L)$, the least $n$ for which every coloring of $[n] \times [n]$ with
$3$ colors contains a monochromatic L, is at most $772$.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Theorem 5. -/
public theorem gridLRamseyProperty_three_772 : GridLRamseyProperty 3 772 := by
  intro c
  by_contra h
  -- At least 258 of the main diagonal points have the same color.
  obtain ⟨red, _, hred⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Icc 1 772) (t := univ) (f := fun x => c (x, x)) (n := 257)
    (fun _ _ => mem_univ _) (by simp)
  let S := (Icc 1 772).filter fun x => c (x, x) = red
  obtain ⟨d, hd, hmany⟩ := frequent_distance S (filter_subset _ _) hred
  let X := S.filter fun x => x + d ∈ S
  have endpoints {x : ℕ} (hx : x ∈ X) :
      0 < x ∧ x + d ≤ 772 ∧ c (x, x) = red ∧ c (x + d, x + d) = red := by
    simp only [X, S, mem_filter, mem_Icc] at hx
    exact ⟨hx.1.1.1, hx.2.1.2, hx.1.2, hx.2.2⟩
  -- The corners of these red pairs must use the other two colors. At least 40 agree.
  have other (x : ℕ) (hx : x ∈ X) : c (x + d, x) ∈ univ.erase red := by
    obtain ⟨hx₀, hxd, hx₁, hx₂⟩ := endpoints hx
    refine mem_erase.mpr ⟨fun heq => h ?_, mem_univ _⟩
    exact ⟨x, x, d, hx₀, hx₀, hd, hxd, hxd, hx₁.trans heq.symm, heq.trans hx₂.symm⟩
  obtain ⟨blue, hb, hblue⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    other (n := 39) (by simpa [card_erase_of_mem (mem_univ red), X] using hmany)
  apply h
  apply exists_mono_L_of_forced_blue_diagonal 772 (by decide) c red blue
    (mem_erase.mp hb).1.symm d hd (X.filter fun x => c (x + d, x) = blue)
  · intro x hx
    obtain ⟨hx, heq⟩ := mem_filter.mp hx
    obtain ⟨hx₀, hxd, hx₁, hx₂⟩ := endpoints hx
    exact ⟨hx₀, hxd, heq, hx₁, hx₂⟩
  · exact lt_of_lt_of_le (by decide : 772 - 2 < Nat.choose 40 2)
      (Nat.choose_le_choose 2 hblue)

end MetaMathlibExt
