/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.DiagonalSequences
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Range

/-!
# Diagonal sequences of the maximal and minimal partitions

The two conjugate partitions associated with a diagonal normal form realize that form,
and its entries are the parts of the minimal partition with multiplicity.
-/

namespace MetaMathlibExt

namespace diagonalSequence_max_eq_min_and_multiset

open Finset

-- The rows meeting a fixed column form an initial segment of the row indices.
private theorem lt_count_rows {f : ℕ → ℕ} (hf : Antitone f) (n i b : ℕ) :
    i < ((Multiset.range n).map f).countP (b ≤ ·) ↔ i < n ∧ b ≤ f i := by
  rw [Multiset.countP_map]
  change i < ((range n).filter fun j => b ≤ f j).card ↔ _
  constructor
  · intro h
    have hin := (card_filter_le (range n) (fun j => b ≤ f j)).trans_eq (card_range n)
    refine ⟨by omega, ?_⟩
    by_contra! hlt
    have hsub : ((range n).filter fun j => b ≤ f j) ⊆ range i := by
      intro j hj
      apply mem_range.mpr
      by_contra! hle
      exact hlt.not_ge ((mem_filter.mp hj).2.trans (hf hle))
    have := (card_le_card hsub).trans_eq (card_range i)
    omega
  · rintro ⟨hin, hb⟩
    have hsub : range (i + 1) ⊆ (range n).filter fun j => b ≤ f j := by
      intro j hj
      have hji : j ≤ i := Nat.le_of_lt_succ (mem_range.mp hj)
      exact mem_filter.mpr ⟨mem_range.mpr (hji.trans_lt hin), hb.trans (hf hji)⟩
    simpa using card_le_card hsub

-- Transposing a cell interchanges its row and column while preserving its diagonal.
private theorem conjugate_cell (rows : Multiset ℕ) (i j : ℕ) :
    j < (conjugateParts rows).countP (i + 1 ≤ ·) ↔ i < rows.countP (j < ·) := by
  have anti : Antitone (fun k : ℕ => rows.countP (k < ·)) := by
    intro a b hab
    dsimp only
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
    exact Multiset.card_le_card (Multiset.monotone_filter_right rows fun _ h => hab.trans_lt h)
  rw [conjugateParts, lt_count_rows anti]
  constructor
  · exact And.right
  · intro h
    obtain ⟨x, hx, hj⟩ := Multiset.countP_pos.mp (Nat.zero_lt_of_lt h)
    exact ⟨hj.trans_le (Multiset.le_sup hx), h⟩

private theorem diagonal_conjugate (rows : Multiset ℕ) :
    diagonalSequence rows = diagonalSequence (conjugateParts rows) := by
  funext k
  unfold diagonalSequence
  let flip (i : ℕ) := k + 1 - i
  have flip_mem {i} (hi : i ∈ Icc 1 k) : flip i ∈ Icc 1 k := by
    simp only [mem_Icc, flip] at *
    omega
  have invol {i} (hi : i ∈ Icc 1 k) : flip (flip i) = i := by
    simp only [mem_Icc, flip] at *
    omega
  have cell {i} (hi : i ∈ Icc 1 k) :
      flip i ≤ (conjugateParts rows).countP (i ≤ ·) ↔ i ≤ rows.countP (flip i ≤ ·) := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (mem_Icc.mp hi).1)
    obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (mem_Icc.mp (flip_mem hi)).1)
    rw [hb, ha]
    exact conjugate_cell rows a b
  apply card_bij (fun i _ => flip i)
  · intro i hi
    obtain ⟨hit, hc⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨flip_mem hit, ?_⟩
    change flip i ≤ (conjugateParts rows).countP (flip (flip i) ≤ ·)
    rw [invol hit]
    exact (cell hit).mpr hc
  · intro i hi j hj h
    simpa only [invol (mem_filter.mp hi).1, invol (mem_filter.mp hj).1] using congrArg flip h
  · intro j hj
    obtain ⟨hjt, hc⟩ := mem_filter.mp hj
    refine ⟨flip j, mem_filter.mpr ⟨flip_mem hjt, ?_⟩, invol hjt⟩
    exact (cell (flip_mem hjt)).mp (by simpa only [invol hjt] using hc)

-- The weakly decreasing tail consists of a block of length s j at each height j.
private def blocks (q : ℕ) (s : ℕ → ℕ) : List ℕ :=
  (List.range q).reverse.flatMap fun j => List.replicate (s (j + 1)) (j + 1)

private theorem blocks_succ (q : ℕ) (s : ℕ → ℕ) :
    blocks (q + 1) s = List.replicate (s (q + 1)) (q + 1) ++ blocks q s := by
  simp [blocks, List.range_succ]

private theorem le_blocks_getD (q : ℕ) (s : ℕ → ℕ) (h m : ℕ) (hh : 0 < h) :
    h ≤ (blocks q s).getD m 0 ↔ h ≤ q ∧ m < ∑ j ∈ Icc h q, s j := by
  induction q generalizing m with
  | zero => simp [blocks, hh.ne']
  | succ q ih =>
    rw [blocks_succ]
    by_cases hm : m < s (q + 1)
    · rw [List.getD_append _ _ _ _ (by simpa using hm), List.getD_replicate _ hm]
      refine ⟨fun hq => ⟨hq, ?_⟩, And.left⟩
      rw [sum_Icc_succ_top hq]
      omega
    · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hm),
        List.length_replicate, ih]
      by_cases hq : h ≤ q
      · rw [sum_Icc_succ_top (by omega : h ≤ q + 1)]
        omega
      · by_cases heq : h = q + 1
        · subst h
          simp [hm]
        · omega

-- At height h the normal form occupies exactly the diagonals from h to
-- q + s h + ... + s q, including both endpoints.
private theorem le_normalForm (q : ℕ) (s : ℕ → ℕ) (h k : ℕ) (hh : 0 < h) :
    h ≤ diagonalOfList (diagonalNormalForm q s) k ↔
      h ≤ k ∧ h ≤ q ∧ k ≤ q + ∑ j ∈ Icc h q, s j := by
  cases k with
  | zero => simp [diagonalOfList, hh.ne']
  | succ k =>
    change h ≤ (List.range' 1 q ++ blocks q s).getD k 0 ↔ _
    by_cases hk : k < q
    · have hlen : k < (List.range' 1 q).length := by simpa using hk
      rw [List.getD_append _ _ _ _ hlen, List.getD_eq_getElem _ _ hlen, List.getElem_range'_1]
      omega
    · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hk),
        List.length_range', le_blocks_getD _ _ _ _ hh]
      omega

private theorem diagonal_max (q : ℕ) (s : ℕ → ℕ) :
    diagonalSequence ↑(diagonalMaxPartition q s) = diagonalOfList (diagonalNormalForm q s) := by
  let row (i : ℕ) := q - i + ∑ j ∈ Icc (i + 1) q, s j
  have anti : Antitone row := by
    intro a b hab
    exact Nat.add_le_add (Nat.sub_le_sub_left hab q)
      (sum_le_sum_of_subset (Icc_subset_Icc (by omega) le_rfl))
  funext k
  unfold diagonalSequence
  -- Row i meets diagonal k precisely when the normal form there has height at least i.
  suffices ((Icc 1 k).filter fun i =>
      i ≤ (↑(diagonalMaxPartition q s) : Multiset ℕ).countP (k + 1 - i ≤ ·)) =
      Icc 1 (diagonalOfList (diagonalNormalForm q s) k) by
    rw [this, Nat.card_Icc]
    omega
  ext i
  simp only [mem_filter, mem_Icc]
  cases i with
  | zero => simp
  | succ i =>
    rw [le_normalForm _ _ _ _ (by omega)]
    simp only [diagonalMaxPartition, ← Multiset.map_coe, Multiset.coe_range]
    change (_ ∧ i < ((Multiset.range q).map row).countP (k + 1 - (i + 1) ≤ ·)) ↔ _
    rw [lt_count_rows anti]
    dsimp [row]
    omega

private theorem normalForm_parts (q : ℕ) (s : ℕ → ℕ) :
    (↑(diagonalNormalForm q s) : Multiset ℕ) = ↑(diagonalMinPartition q s) := by
  change ↑(List.range' 1 q ++ blocks q s) = (↑(blocks q fun k => s k + 1) : Multiset ℕ)
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [← Multiset.coe_add] at ih
    rw [List.range'_concat, blocks_succ, blocks_succ]
    simp only [one_mul, Nat.one_add, ← Multiset.coe_add, Multiset.coe_replicate,
      Multiset.replicate_succ, Multiset.coe_singleton, ← Multiset.singleton_add]
    rw [← ih]
    ac_rfl

end diagonalSequence_max_eq_min_and_multiset

open diagonalSequence_max_eq_min_and_multiset in
/-- **Equal diagonal sequences of the maximal and minimal partitions.** Let $q \ge 0$ and
$s_1, \dots, s_q \ge 0$ be natural numbers, write $v^{(m)}$ for $m$ copies of $v$, and let
$\bar\alpha$ and $\underline\alpha$ be the partitions with parts
$\bar\alpha_i = q - i + 1 + s_i + s_{i+1} + \dots + s_q$ for $1 \le i \le q$ and
$\underline\alpha = (q^{(s_q + 1)}, (q-1)^{(s_{q-1} + 1)}, \dots, 1^{(s_1 + 1)})$. Then
$\bar\alpha$ and $\underline\alpha$ have the same diagonal sequence; this diagonal sequence,
indexed from $0$, is $(0, 1, 2, \dots, q, q^{(s_q)}, \dots, 1^{(s_1)}, 0, 0, \dots)$; and the
multiset of its nonzero entries $1, 2, \dots, q, q^{(s_q)}, \dots, 1^{(s_1)}$ equals the multiset
of parts of $\underline\alpha$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 3. -/
public theorem diagonalSequence_max_eq_min_and_multiset (q : ℕ) (s : ℕ → ℕ) :
    diagonalSequence ↑(diagonalMaxPartition q s) =
        diagonalSequence ↑(diagonalMinPartition q s) ∧
      diagonalSequence ↑(diagonalMinPartition q s) = diagonalOfList (diagonalNormalForm q s) ∧
      (↑(diagonalNormalForm q s) : Multiset ℕ) = ↑(diagonalMinPartition q s) := by
  have h := diagonal_conjugate (↑(diagonalMaxPartition q s))
  rw [conjugateParts_diagonalMaxPartition] at h
  exact ⟨h, h.symm.trans (diagonal_max q s), normalForm_parts q s⟩

end MetaMathlibExt
