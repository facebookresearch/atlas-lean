/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.DiagonalSequences
import all MathlibExt.Combinatorics.Enumerative.Partition.ExtremalDiagonalSequences
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort

/-!
# Repeated parts and large gaps in a diagonal class

A partition whose diagonal sequence has the normal form
`(1, 2, …, q, q^(s_q), …, 1^(s_1))` is the maximal partition of that form unless two consecutive
parts are equal, and it is the minimal partition of that form unless two consecutive parts, the
last part followed by `0`, differ by at least `2`. The proof rebuilds the maximal partition from
the gaps of a strictly decreasing list of parts and the minimal partition from the multiplicities
of a list whose parts drop by at most one, and uses that the diagonal sequence of a normal form
determines `q` and `s_1, …, s_q`.
-/

namespace MetaMathlibExt
namespace exists_eq_succ_of_ne_diagonalMaxPartition

open Finset
open diagonalSequence_max_eq_min_and_multiset (le_normalForm)

-- The diagonal sequence of a normal form determines its staircase and its multiplicities.
private theorem normalForm_injective {q q' : ℕ} {s s' : ℕ → ℕ}
    (h : diagonalOfList (diagonalNormalForm q s) = diagonalOfList (diagonalNormalForm q' s')) :
    q = q' ∧ ∀ j ∈ Icc 1 q, s j = s' j := by
  have hle (a k : ℕ) (ha : 0 < a) :
      (a ≤ k ∧ a ≤ q ∧ k ≤ q + ∑ j ∈ Icc a q, s j) ↔
        (a ≤ k ∧ a ≤ q' ∧ k ≤ q' + ∑ j ∈ Icc a q', s' j) := by
    rw [← le_normalForm _ _ _ _ ha, ← le_normalForm _ _ _ _ ha, h]
  have hq : q = q' := by
    have key (a : ℕ) (ha : 0 < a) : a ≤ q ↔ a ≤ q' :=
      ⟨fun hq => ((hle a a ha).mp ⟨le_rfl, hq, by omega⟩).2.1,
        fun hq => ((hle a a ha).mpr ⟨le_rfl, hq, by omega⟩).2.1⟩
    rcases Nat.lt_trichotomy q q' with hlt | heq | hgt
    · exact absurd ((key q' (by omega)).mpr le_rfl) (by omega)
    · exact heq
    · exact absurd ((key q (by omega)).mp le_rfl) (by omega)
  subst hq
  have hsum (a : ℕ) (ha : 0 < a) (haq : a ≤ q) :
      ∑ j ∈ Icc a q, s j = ∑ j ∈ Icc a q, s' j := by
    have h1 := ((hle a (q + ∑ j ∈ Icc a q, s j) ha).mp ⟨by omega, haq, le_rfl⟩).2.2
    have h2 := ((hle a (q + ∑ j ∈ Icc a q, s' j) ha).mpr ⟨by omega, haq, le_rfl⟩).2.2
    omega
  refine ⟨rfl, fun j hj => ?_⟩
  obtain ⟨hj1, hjq⟩ := mem_Icc.mp hj
  have e1 := hsum j hj1 hjq
  rw [← insert_Icc_add_one_left_eq_Icc hjq, sum_insert (by simp), sum_insert (by simp)] at e1
  rcases Nat.lt_or_ge j q with hlt | hge
  · have e2 := hsum (j + 1) (by omega) hlt
    omega
  · rw [Icc_eq_empty (by omega)] at e1
    simpa using e1

-- Both extremal partitions depend only on the multiplicities `s 1, …, s q`.
private theorem diagonalMaxPartition_congr {q : ℕ} {s s' : ℕ → ℕ}
    (h : ∀ j ∈ Icc 1 q, s j = s' j) :
    diagonalMaxPartition q s = diagonalMaxPartition q s' := by
  unfold diagonalMaxPartition
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  rw [sum_congr rfl fun k hk => h k (by simp only [mem_Icc] at hk ⊢; omega)]

private theorem diagonalMinPartition_congr {q : ℕ} {s s' : ℕ → ℕ}
    (h : ∀ j ∈ Icc 1 q, s j = s' j) :
    diagonalMinPartition q s = diagonalMinPartition q s' := by
  unfold diagonalMinPartition
  refine List.flatMap_congr fun j hj => ?_
  have hj := List.mem_range.mp (List.mem_reverse.mp hj)
  rw [h (j + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)]

-- A strictly decreasing list of positive parts is the maximal partition of its gaps.
private theorem eq_diagonalMaxPartition (α : List ℕ)
    (h : ∀ i < α.length, α.getD (i + 1) 0 < α.getD i 0) :
    α = diagonalMaxPartition α.length fun j => α.getD (j - 1) 0 - α.getD j 0 - 1 := by
  have tele (r : ℕ) : ∀ i, i + r = α.length →
      α.length - i + ∑ k ∈ Icc (i + 1) α.length, (α.getD (k - 1) 0 - α.getD k 0 - 1) =
        α.getD i 0 := by
    induction r with
    | zero =>
      intro i hi
      rw [Icc_eq_empty (by omega), sum_empty, List.getD_eq_default _ _ (by omega)]
      omega
    | succ r ih =>
      intro i hi
      have h1 := ih (i + 1) (by omega)
      have h2 := h i (by omega)
      rw [← insert_Icc_add_one_left_eq_Icc (by omega : i + 1 ≤ α.length), sum_insert (by simp),
        Nat.add_sub_cancel]
      omega
  apply List.ext_getElem
  · simp [diagonalMaxPartition]
  · intro i h1 h2
    simp only [diagonalMaxPartition, List.getElem_map, List.getElem_range]
    rw [tele (α.length - i) i (by omega), List.getD_eq_getElem _ _ h1]

-- The minimal partition starts with its block of largest parts.
private theorem diagonalMinPartition_succ (q : ℕ) (s : ℕ → ℕ) :
    diagonalMinPartition (q + 1) s =
      List.replicate (s (q + 1) + 1) (q + 1) ++ diagonalMinPartition q s := by
  simp [diagonalMinPartition, List.range_succ]

private theorem count_diagonalMinPartition (q : ℕ) (s : ℕ → ℕ) (x : ℕ) :
    (diagonalMinPartition q s).count x = if 1 ≤ x ∧ x ≤ q then s x + 1 else 0 := by
  induction q with
  | zero =>
    simp only [diagonalMinPartition, List.range_zero, List.reverse_nil, List.flatMap_nil,
      List.count_nil]
    split_ifs <;> omega
  | succ q ih =>
    rw [diagonalMinPartition_succ, List.count_append, ih, List.count_replicate]
    simp only [beq_iff_eq]
    by_cases hx : x = q + 1
    · subst hx
      simp
    · simp only [Ne.symm hx, ↓reduceIte, Nat.zero_add]
      split_ifs <;> omega

private theorem pairwise_diagonalMinPartition (q : ℕ) (s : ℕ → ℕ) :
    (diagonalMinPartition q s).Pairwise (· ≥ ·) := by
  induction q with
  | zero => simp [diagonalMinPartition]
  | succ q ih =>
    rw [diagonalMinPartition_succ, List.pairwise_append]
    refine ⟨List.pairwise_replicate.mpr (Or.inr le_rfl), ih, fun a ha b hb => ?_⟩
    rw [List.eq_of_mem_replicate ha]
    have hb := List.count_pos_iff.mpr hb
    rw [count_diagonalMinPartition] at hb
    split_ifs at hb <;> omega

-- A weakly decreasing list of positive parts, in which consecutive parts and the last part
-- drop by at most one, is the minimal partition of its multiplicities.
private theorem eq_diagonalMinPartition (α : List ℕ) (hs : α.Pairwise (· ≥ ·))
    (hpos : ∀ x ∈ α, 0 < x) (h : ∀ i < α.length, α.getD i 0 ≤ α.getD (i + 1) 0 + 1) :
    α = diagonalMinPartition (α.getD 0 0) fun j => α.count j - 1 := by
  have hle : ∀ x ∈ α, x ≤ α.getD 0 0 := by
    intro x hx
    cases α with
    | nil => simp at hx
    | cons b β =>
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact (List.pairwise_cons.mp hs).1 x hx
  have hmem : ∀ x, 1 ≤ x → x ≤ α.getD 0 0 → x ∈ α := by
    intro x hx1 hxa
    have hex : ∃ j, α.getD j 0 < x :=
      ⟨α.length, by rw [List.getD_eq_default _ _ le_rfl]; omega⟩
    classical
    obtain ⟨j, hj, hmin⟩ : ∃ j, α.getD j 0 < x ∧ ∀ k < j, ¬ α.getD k 0 < x :=
      ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (fun h0 : j = 0 => by subst h0; omega)
    have hi : x ≤ α.getD i 0 := not_lt.mp (hmin i (by omega))
    have hilen : i < α.length := by
      by_contra hc
      rw [List.getD_eq_default _ _ (not_lt.mp hc)] at hi
      omega
    have hstep := h i hilen
    have heq : α.getD i 0 = x := by omega
    rw [List.getD_eq_getElem _ _ hilen] at heq
    exact heq ▸ List.getElem_mem hilen
  apply List.Perm.eq_of_pairwise' hs (pairwise_diagonalMinPartition _ _)
  rw [List.perm_iff_count]
  intro x
  rw [count_diagonalMinPartition]
  split_ifs with hx
  · have := List.count_pos_iff.mpr (hmem x hx.1 hx.2)
    omega
  · rw [List.count_eq_zero]
    intro hxα
    exact hx ⟨hpos x hxα, hle x hxα⟩

end exists_eq_succ_of_ne_diagonalMaxPartition

open exists_eq_succ_of_ne_diagonalMaxPartition in
/-- **Repeated parts and large gaps in a diagonal class.** Let $q \ge 0$ and
$s_1, \dots, s_q \ge 0$ be natural numbers, write $v^{(m)}$ for $m$ copies of $v$, and let
$\bar\alpha$ and $\underline\alpha$ be the partitions with parts
$\bar\alpha_i = q - i + 1 + s_i + s_{i+1} + \dots + s_q$ for $1 \le i \le q$ and
$\underline\alpha = (q^{(s_q + 1)}, (q-1)^{(s_{q-1} + 1)}, \dots, 1^{(s_1 + 1)})$. Let $\alpha$
be a partition of $n$ with parts $\alpha_1 \ge \dots \ge \alpha_t$, set $\alpha_{t+1} = 0$, and
suppose that the diagonal sequence of $\alpha$, indexed from $0$, is
$(0, 1, 2, \dots, q, q^{(s_q)}, \dots, 1^{(s_1)}, 0, 0, \dots)$. If $\alpha \ne \bar\alpha$, then
$\alpha_i = \alpha_{i+1}$ for some $i$ with $1 \le i < t$. If $\alpha \ne \underline\alpha$, then
$\alpha_i - \alpha_{i+1} \ge 2$ for some $i$ with $1 \le i \le t$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 4. -/
public theorem exists_eq_succ_of_ne_diagonalMaxPartition {n : ℕ} (p : Nat.Partition n)
    (q : ℕ) (s : ℕ → ℕ)
    (hd : diagonalSequence p.parts = diagonalOfList (diagonalNormalForm q s)) :
    (p.parts.sort (· ≥ ·) ≠ diagonalMaxPartition q s →
      ∃ i, i + 1 < p.parts.card ∧
        (p.parts.sort (· ≥ ·)).getD i 0 = (p.parts.sort (· ≥ ·)).getD (i + 1) 0) ∧
    (p.parts.sort (· ≥ ·) ≠ diagonalMinPartition q s →
      ∃ i, i < p.parts.card ∧
        (p.parts.sort (· ≥ ·)).getD (i + 1) 0 + 1 < (p.parts.sort (· ≥ ·)).getD i 0) := by
  set α := p.parts.sort (· ≥ ·)
  have hsorted : α.Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
  have hcoe : (α : Multiset ℕ) = p.parts := Multiset.sort_eq _ _
  have hlen : α.length = p.parts.card := Multiset.length_sort _
  have hpos : ∀ x ∈ α, 0 < x := fun x hx => p.parts_pos ((Multiset.mem_sort _).mp hx)
  have hext := diagonalSequence_max_eq_min_and_multiset
  constructor
  -- Without two equal consecutive parts, the parts strictly decrease, so they form the maximal
  -- partition of their gaps, and the normal form determines these gaps.
  · intro hne
    by_contra hno
    push Not at hno
    apply hne
    have hstrict : ∀ i < α.length, α.getD (i + 1) 0 < α.getD i 0 := by
      intro i hi
      rcases Nat.lt_or_ge (i + 1) α.length with h1 | h1
      · have hge : α.getD (i + 1) 0 ≤ α.getD i 0 := by
          rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ hi]
          exact List.pairwise_iff_getElem.mp hsorted i (i + 1) hi h1 (by omega)
        have hne' := hno i (by omega)
        omega
      · rw [List.getD_eq_default _ _ h1, List.getD_eq_getElem _ _ hi]
        exact hpos _ (List.getElem_mem hi)
    have hmax := eq_diagonalMaxPartition α hstrict
    have hd' : diagonalOfList (diagonalNormalForm α.length
        fun j => α.getD (j - 1) 0 - α.getD j 0 - 1) =
          diagonalOfList (diagonalNormalForm q s) := by
      rw [← hd, ← hcoe, ← (hext _ _).2.1, ← (hext _ _).1, ← hmax]
    obtain ⟨rfl, hs⟩ := normalForm_injective hd'
    rw [← diagonalMaxPartition_congr hs]
    exact hmax
  -- Without a drop of two or more, the parts form the minimal partition of their
  -- multiplicities, and the normal form determines these multiplicities.
  · intro hne
    by_contra hno
    push Not at hno
    apply hne
    have hmin := eq_diagonalMinPartition α hsorted hpos fun i hi => hno i (hlen ▸ hi)
    have hd' : diagonalOfList (diagonalNormalForm (α.getD 0 0) fun j => α.count j - 1) =
        diagonalOfList (diagonalNormalForm q s) := by
      rw [← hd, ← hcoe, ← (hext _ _).2.1, ← hmin]
    obtain ⟨rfl, hs⟩ := normalForm_injective hd'
    rw [← diagonalMinPartition_congr hs]
    exact hmin

end MetaMathlibExt
