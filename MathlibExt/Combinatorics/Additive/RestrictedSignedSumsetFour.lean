/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases

/-!
# A lower bound for restricted signed four-fold sumsets

A set of $k ≥ 5$ nonnegative integers containing zero has at least $8k - 19$ distinct
signed sums of four distinct elements. We exhibit 21 sums on the first five elements,
then extend the count by eight whenever we adjoin a new largest element.
-/

namespace MetaMathlibExt

namespace card_restrictedSignedSumset_four_nonnegative_ge

private theorem signed_support (l : List ℤ) (hl : (l.map abs).Nodup) :
    ∃ N ⊆ (l.map abs).toFinset, (l.map abs).sum - 2 * ∑ x ∈ N, x = l.sum := by
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    obtain ⟨N, hN, he⟩ := ih hl
    simp only [List.map_cons, List.toFinset_cons]
    by_cases h : 0 ≤ a
    · refine ⟨N, hN.trans (Finset.subset_insert _ _), ?_⟩
      simp only [List.sum_cons, abs_of_nonneg h]
      omega
    · have hn : |a| ∉ N := fun hx => ha (List.mem_toFinset.mp (hN hx))
      refine ⟨insert |a| N, Finset.insert_subset_insert _ hN, ?_⟩
      rw [Finset.sum_insert hn]
      simp only [List.sum_cons, abs_of_neg (lt_of_not_ge h)]
      omega

/-- A row of signed entries specifies a sum when its absolute values are distinct. -/
private theorem row_mem {A : Finset ℤ} {l : List ℤ} (hlen : l.length = 4)
    (hd : (l.map abs).Nodup) (hm : ∀ x ∈ l, |x| ∈ A) :
    l.sum ∈ restrictedSignedSumset 4 A := by
  obtain ⟨N, hN, he⟩ := signed_support l hd
  refine Finset.mem_image.mpr ⟨⟨(l.map abs).toFinset, N⟩, Finset.mem_sigma.mpr
    ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.mem_powerset.mpr hN⟩, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hm y hy
  · simpa only [List.toFinset_card_of_nodup hd, List.length_map] using hlen
  · change ∑ x ∈ (l.map abs).toFinset, id x - 2 * ∑ x ∈ N, x = l.sum
    rw [List.sum_toFinset id hd]
    simpa using he

private theorem count_rows {A S : Finset ℤ} (rows : List (List ℤ))
    (hrows : ∀ l ∈ rows, l.length = 4 ∧ (l.map abs).Nodup ∧ ∀ x ∈ l, |x| ∈ A)
    (hs : ∀ l ∈ rows, l.sum ∈ restrictedSignedSumset 4 A → l.sum ∈ S)
    (hchain : (rows.map List.sum).IsChain (· < ·)) :
    rows.length ≤ S.card := by
  let xs := rows.map List.sum
  have hd : xs.Nodup := (List.isChain_iff_pairwise.mp hchain).imp Int.ne_of_lt
  have hsub : xs.toFinset ⊆ S := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    obtain ⟨hlen, hnodup, hmem⟩ := hrows l hl
    exact hs l hl (row_mem hlen hnodup hmem)
  simpa [List.toFinset_card_of_nodup hd, xs] using Finset.card_le_card hsub

private def window (A : Finset ℤ) (m : ℤ) : Finset ℤ :=
  (restrictedSignedSumset 4 A).filter fun x => -m ≤ x ∧ x ≤ m

private theorem five {A : Finset ℤ} {a b c d : ℤ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h0 : 0 ∈ A) (hma : a ∈ A) (hmb : b ∈ A) (hmc : c ∈ A) (hmd : d ∈ A) :
    21 ≤ (window A (a + b + c + d)).card := by
  have count (rows : List (List ℤ)) (hlen : rows.length = 21)
      (hr : ∀ l ∈ rows, l.length = 4 ∧ (l.map abs).Nodup ∧ ∀ x ∈ l, |x| ∈ A)
      (hb : ∀ l ∈ rows, -(a + b + c + d) ≤ l.sum ∧ l.sum ≤ a + b + c + d)
      (hc : (rows.map List.sum).IsChain (· < ·)) : 21 ≤ (window A (a + b + c + d)).card := by
    rw [← hlen]
    exact count_rows rows hr (fun l hl hm => Finset.mem_filter.mpr ⟨hm, hb l hl⟩) hc
  -- In each range of the gaps, the displayed rows have strictly increasing sums.
  -- A zero entry uses the element zero as one of the four summands.
  by_cases hcb : c < 2 * b
  case' pos =>
    by_cases hba : b < 2 * a
    case' pos =>
      apply count
        [[-a, -b, -c, -d], [0, -b, -c, -d], [0, -a, -c, -d], [a, -b, -c, -d],
         [-a, b, -c, -d], [0, a, -c, -d], [0, b, -c, -d], [0, -a, b, -d],
         [0, -a, c, -d], [a, -b, c, -d], [0, a, b, -d], [0, a, b, -c],
         [0, a, -c, d], [0, b, -c, d], [0, -a, b, d], [0, -a, c, d],
         [a, -b, c, d], [0, a, b, d], [0, a, c, d], [0, b, c, d],
         [a, b, c, d]] rfl
    case' neg =>
      by_cases hcab : c < a + b
      case' pos =>
        apply count
          [[-a, -b, -c, -d], [0, -b, -c, -d], [a, -b, -c, -d], [0, -a, -b, -d],
           [0, a, -c, -d], [0, a, -b, -d], [0, b, -c, -d], [a, b, -c, -d],
           [0, -a, b, -d], [0, -a, b, -c], [0, -a, -c, d], [0, -a, -b, d],
           [0, a, -c, d], [0, a, -b, d], [0, b, -c, d], [a, b, -c, d],
           [0, -a, b, d], [0, -a, c, d], [0, a, b, d], [0, a, c, d],
           [a, b, c, d]] rfl
      case' neg =>
        apply count
          [[-a, -b, -c, -d], [0, -b, -c, -d], [a, -b, -c, -d], [0, -a, -b, -d],
           [-a, b, -c, -d], [0, b, -c, -d], [a, b, -c, -d], [0, -b, c, -d],
           [a, -b, c, -d], [0, a, b, -d], [0, a, b, -c], [0, -a, -b, d],
           [-a, b, -c, d], [0, b, -c, d], [a, b, -c, d], [0, -b, c, d],
           [a, -b, c, d], [0, a, b, d], [0, a, c, d], [0, b, c, d],
           [a, b, c, d]] rfl
  case' neg =>
    by_cases hdac : a + c < d
    case' pos =>
      apply count
        [[-a, -b, -c, -d], [0, -b, -c, -d], [0, -a, -c, -d], [-a, b, -c, -d],
         [0, b, -c, -d], [a, b, -c, -d], [0, -a, b, -d], [0, -b, c, -d],
         [a, -b, c, -d], [-a, -b, -c, d], [0, -b, -c, d], [0, -a, -c, d],
         [-a, b, -c, d], [0, b, -c, d], [a, b, -c, d], [0, -a, b, d],
         [0, -b, c, d], [0, -a, c, d], [-a, b, c, d], [0, b, c, d],
         [a, b, c, d]] rfl
    case' neg =>
      apply count
        [[-a, -b, -c, -d], [0, -b, -c, -d], [0, -a, -c, -d], [-a, b, -c, -d],
         [0, b, -c, -d], [a, b, -c, -d], [0, a, -b, -c], [0, -a, b, -c],
         [-a, -b, -c, d], [0, -b, -c, d], [0, -a, -c, d], [0, -a, -b, c],
         [0, -a, -b, d], [0, a, -b, c], [0, a, -b, d], [0, -a, b, d],
         [0, -b, c, d], [0, -a, c, d], [-a, b, c, d], [0, b, c, d],
         [a, b, c, d]] rfl
  all_goals
    simp [List.isChain_cons_cons, List.nodup_cons, abs_of_pos ha, abs_of_pos (ha.trans hab),
      abs_of_pos (ha.trans (hab.trans hbc)), abs_of_pos (ha.trans (hab.trans (hbc.trans hcd))),
      h0, hma, hmb, hmc, hmd]
    omega

/-- With five successive positive entries, replacing each of the first four in turn
by the fifth gives four sums above the old upper bound. Their negatives give four below. -/
private theorem extend {A : Finset ℤ} {a b c d e : ℤ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (hma : a ∈ A) (hmb : b ∈ A) (hmc : c ∈ A) (hmd : d ∈ A) (hme : e ∈ A) :
    (window A (a + b + c + d)).card + 8 ≤ (window A (b + c + d + e)).card := by
  let old := window A (a + b + c + d)
  let new := window A (b + c + d + e)
  have hsub : old ⊆ new := by
    intro x hx
    obtain ⟨hm, hlo, hhi⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hm, by omega, by omega⟩
  have outside (x : ℤ) (hm : x ∈ restrictedSignedSumset 4 A)
      (hb : -(b + c + d + e) ≤ x ∧ x ≤ b + c + d + e)
      (ho : x < -(a + b + c + d) ∨ a + b + c + d < x) : x ∈ new \ old := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hm, hb⟩, fun hx => ?_⟩
    obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hx
    omega
  have h8 : 8 ≤ (new \ old).card := by
    let rows := [[-b, -c, -d, -e], [-a, -c, -d, -e], [-a, -b, -d, -e], [-a, -b, -c, -e],
                 [a, b, c, e], [a, b, d, e], [a, c, d, e], [b, c, d, e]]
    apply count_rows (A := A) rows
    · simp [rows, List.nodup_cons, abs_of_pos ha, abs_of_pos (ha.trans hab),
        abs_of_pos (ha.trans (hab.trans hbc)), abs_of_pos (ha.trans (hab.trans (hbc.trans hcd))),
        abs_of_pos (ha.trans (hab.trans (hbc.trans (hcd.trans hde)))), hma, hmb, hmc, hmd, hme]
      omega
    · intro l hl hm
      apply outside _ hm
      all_goals
        simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [List.sum_cons, List.sum_nil] <;> omega
    · simp [rows, List.isChain_cons_cons]
      omega
  have he := Finset.card_sdiff_add_card_eq_card hsub
  change old.card + 8 ≤ new.card
  omega

private theorem count_prefix {A : Finset ℤ} (n : ℕ) (f : Fin (n + 5) → ℤ)
    (hf : StrictMono f) (hz : f 0 = 0) (hm : ∀ i, f i ∈ A) :
    8 * n + 21 ≤ (window A (f ⟨n + 1, by omega⟩ + f ⟨n + 2, by omega⟩ +
      f ⟨n + 3, by omega⟩ + f ⟨n + 4, by omega⟩)).card := by
  induction n with
  | zero =>
    have hp : 0 < f 1 := hz ▸ hf (show (0 : Fin 5) < 1 by decide)
    exact five hp (hf (show (1 : Fin 5) < 2 by decide)) (hf (show (2 : Fin 5) < 3 by decide))
      (hf (show (3 : Fin 5) < 4 by decide)) (hz ▸ hm 0) (hm 1) (hm 2) (hm 3) (hm 4)
  | succ n ih =>
    have hold := ih (fun i => f i.castSucc) (hf.comp Fin.strictMono_castSucc) hz
      (fun i => hm i.castSucc)
    let i (j : Fin 5) : Fin (n + 1 + 5) := ⟨n + 1 + j.val, by omega⟩
    have hpos : 0 < f (i 0) := by
      rw [← hz]
      apply hf
      change 0 < n + 1 + 0
      omega
    have hlt {j k : Fin 5} (h : j < k) : f (i j) < f (i k) :=
      hf (show n + 1 + j.val < n + 1 + k.val from Nat.add_lt_add_left h _)
    have hmore := extend hpos (hlt (show 0 < (1 : Fin 5) by decide))
      (hlt (show 1 < (2 : Fin 5) by decide)) (hlt (show 2 < (3 : Fin 5) by decide))
      (hlt (show 3 < (4 : Fin 5) by decide)) (hm _) (hm _) (hm _) (hm _) (hm _)
    exact (show 8 * (n + 1) + 21 = 8 * n + 21 + 8 by omega) ▸
      (Nat.add_le_add_right hold 8).trans hmore

/-- Positive sums of distinct rows can be counted together with their negatives. -/
private theorem count_pos_rows {A : Finset ℤ} (rows : List (List ℤ))
    (hrows : ∀ l ∈ rows, l.length = 4 ∧ (l.map abs).Nodup ∧ ∀ x ∈ l, |x| ∈ A)
    (hchain : (0 :: rows.map List.sum).IsChain (· < ·)) :
    2 * rows.length ≤ (restrictedSignedSumset 4 A).card := by
  have sum_neg (l : List ℤ) : (l.map (fun x => -x)).sum = -l.sum := by
    induction l with
    | nil => simp
    | cons x l ih => simp [ih, add_comm]
  let P := (rows.map List.sum).toFinset
  let N := P.image (fun x => -x)
  obtain ⟨hpos, hlt⟩ := List.pairwise_cons.mp (List.isChain_iff_pairwise.mp hchain)
  have hp (x : ℤ) (hx : x ∈ P) : 0 < x := hpos x (List.mem_toFinset.mp hx)
  have hP : P.card = rows.length := by
    rw [List.toFinset_card_of_nodup (hlt.imp Int.ne_of_lt), List.length_map]
  have hN : N.card = P.card := Finset.card_image_of_injective _ neg_injective
  have hdis : Disjoint P N := by
    refine Finset.disjoint_left.mpr fun x hx hn => ?_
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hn
    have := hp y hy
    have := hp (-y) hx
    omega
  have hsub : P ∪ N ⊆ restrictedSignedSumset 4 A := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      obtain ⟨hlen, hd, hm⟩ := hrows l hl
      exact row_mem hlen hd hm
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
      obtain ⟨hlen, hd, hm⟩ := hrows l hl
      suffices (l.map (fun n => -n)).sum ∈ restrictedSignedSumset 4 A by
        simpa only [sum_neg] using this
      apply row_mem
      · simpa using hlen
      · simpa [List.map_map, Function.comp_def] using hd
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simpa only [abs_neg] using hm y hy
  simpa [Finset.card_union_of_disjoint hdis, hN, hP, two_mul] using Finset.card_le_card hsub

/-- In each of the four possible locations, split on whether the exceptional gap is
less than or greater than twice the minimum. The rows in each branch exhibit thirteen
strictly increasing positive sums; keeping their order avoids any collision checks. -/
private theorem count_one_exceptional_gap {A : Finset ℤ} {a b c d e : ℤ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (hma : a ∈ A) (hmb : b ∈ A) (hmc : c ∈ A) (hmd : d ∈ A) (hme : e ∈ A)
    (hgaps : (b - a ≠ 2 * a ∧ c - b = 2 * a ∧ d - c = 2 * a ∧ e - d = 2 * a) ∨
      (b - a = 2 * a ∧ c - b ≠ 2 * a ∧ d - c = 2 * a ∧ e - d = 2 * a) ∨
      (b - a = 2 * a ∧ c - b = 2 * a ∧ d - c ≠ 2 * a ∧ e - d = 2 * a) ∨
      (b - a = 2 * a ∧ c - b = 2 * a ∧ d - c = 2 * a ∧ e - d ≠ 2 * a)) :
    26 ≤ (restrictedSignedSumset 4 A).card := by
  have count (rows : List (List ℤ)) (hlen : 2 * rows.length = 26)
      (hr : ∀ l ∈ rows, l.length = 4 ∧ (l.map abs).Nodup ∧ ∀ x ∈ l, |x| ∈ A)
      (hc : (0 :: rows.map List.sum).IsChain (· < ·)) : 26 ≤ (restrictedSignedSumset 4 A).card :=
    hlen ▸ count_pos_rows rows hr hc
  have hb := ha.trans hab
  have hc := hb.trans hbc
  have hd := hc.trans hcd
  have he := hd.trans hde
  rcases hgaps with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  case' inl =>
    by_cases h : b - a < 2 * a
    case' pos =>
      apply count
        [[a, b, c, -d], [-a, b, -c, d], [b, c, d, -e], [a, b, -c, d], [-a, -b, c, d],
         [b, c, -d, e], [a, -b, c, d], [-a, b, c, d], [b, -c, d, e], [a, b, c, d],
         [a, b, c, e], [-b, c, d, e], [a, b, d, e]] rfl
    case' neg =>
      apply count
        [[-a, b, c, -d], [a, b, c, -d], [-a, b, -c, d], [a, b, -c, d], [-a, -b, c, d],
         [a, -b, c, d], [a, -b, c, e], [a, -b, d, e], [b, -c, d, e], [-a, b, c, d],
         [a, b, c, d], [a, b, c, e], [a, b, d, e]] rfl
  case' inr.inl =>
    by_cases h : c - b < 2 * a
    case' pos =>
      apply count
        [[-a, c, d, -e], [a, b, c, -d], [a, c, d, -e], [-a, b, -c, d], [-a, c, -d, e],
         [a, b, -c, d], [a, c, -d, e], [a, -b, c, d], [-a, -c, d, e], [a, -b, c, e],
         [a, -c, d, e], [-a, b, c, d], [b, -c, d, e]] rfl
    case' neg =>
      apply count
        [[-b, c, d, -e], [-a, c, d, -e], [a, c, d, -e], [-a, c, -d, e], [a, c, -d, e],
         [-a, -b, c, d], [a, -b, c, d], [a, -b, c, e], [-a, b, c, d], [a, b, c, d],
         [a, b, c, e], [-b, c, d, e], [-a, c, d, e]] rfl
  case' inr.inr.inl =>
    by_cases h : d - c < 2 * a
    case' pos =>
      apply count
        [[-a, b, c, -d], [a, b, d, -e], [a, b, c, -d], [-a, b, -d, e], [a, b, -c, d],
         [a, b, -d, e], [-a, -b, c, d], [a, c, -d, e], [a, -b, c, d], [-a, -b, d, e],
         [a, -b, c, e], [a, -b, d, e], [-a, b, c, d]] rfl
    case' neg =>
      apply count
        [[a, -b, -c, d], [a, -b, -c, e], [-a, b, -c, d], [a, b, -c, d], [-a, -b, c, d],
         [a, -b, c, d], [a, -b, c, e], [-a, b, c, d], [a, b, c, d], [a, b, c, e],
         [-a, b, d, e], [a, b, d, e], [a, c, d, e]] rfl
  case' inr.inr.inr =>
    by_cases h : e - d < 2 * a
    case' pos =>
      apply count
        [[a, b, c, -e], [a, b, c, -d], [a, b, d, -e], [-a, b, -c, d], [-a, b, -c, e],
         [a, b, -c, d], [a, b, -c, e], [-a, -b, c, d], [-a, -b, c, e], [a, -b, c, d],
         [a, -b, c, e], [a, -b, d, e], [-a, b, c, d]] rfl
    case' neg =>
      apply count
        [[-a, -b, -c, e], [a, -b, -c, e], [-a, b, -d, e], [-a, b, -c, e], [a, b, -c, e],
         [-a, -b, c, e], [a, -b, c, e], [a, -b, d, e], [-a, b, c, e], [a, b, c, e],
         [a, b, d, e], [a, c, d, e], [b, c, d, e]] rfl
  all_goals
    simp [List.isChain_cons_cons, List.nodup_cons, abs_of_pos ha, abs_of_pos hb,
      abs_of_pos hc, abs_of_pos hd, abs_of_pos he, hma, hmb, hmc, hmd, hme]
    omega

end card_restrictedSignedSumset_four_nonnegative_ge

open card_restrictedSignedSumset_four_nonnegative_ge

/-- **Lower bound for restricted signed 4-fold sumsets of nonnegative sets containing zero.**
Let $k \ge 5$, let $A$ be a set of $k$ nonnegative integers with $0 \in A$, and write
$4^{\wedge}_{\pm} A$ for the restricted signed 4-fold sumset of $A$. Then
$|4^{\wedge}_{\pm} A| \ge 8k - 19$.

The inverse statement of the source, that equality forces $A = d \cdot \{0, 1, \dots, k - 1\}$
for some integer $d$ (where $d \cdot B = \{db : b \in B\}$), is omitted: $A = \{0, 1, 2, 4, 6\}$
has $|4^{\wedge}_{\pm} A| = 21 = 8 \cdot 5 - 19$ but is not of that form.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the
Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 11. -/
public theorem card_restrictedSignedSumset_four_nonnegative_ge
    (k : ℕ) (A : Finset ℤ) (hk : 5 ≤ k) (hcard : A.card = k)
    (hnonneg : ∀ a ∈ A, 0 ≤ a) (hzero : 0 ∈ A) :
    ((restrictedSignedSumset 4 A).card : ℤ) ≥ 8 * (k : ℤ) - 19 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
  let f := A.orderEmbOfFin hcard
  have hz : f 0 = 0 := by
    have hmin := A.orderEmbOfFin_zero hcard (by omega)
    exact le_antisymm (hmin.trans_le (A.min'_le _ hzero)) (hnonneg _ (A.orderEmbOfFin_mem _ _))
  have h := count_prefix n f f.strictMono hz (A.orderEmbOfFin_mem hcard)
  have hle := h.trans (Finset.card_filter_le (restrictedSignedSumset 4 A) _)
  omega

/-- **Restricted signed 4-fold sumsets when exactly one gap differs from twice the minimum.**
Let $a_1 < a_2 < a_3 < a_4 < a_5$ be integers with $a_1 > 0$, let $A = \{a_1, \dots, a_5\}$,
and write $4^{\wedge}_{\pm} A$ for the restricted signed 4-fold sumset of $A$. If exactly one
of the four gaps $a_{i+1} - a_i$ with $i \in \{1, 2, 3, 4\}$ differs from $2a_1$, then
$|4^{\wedge}_{\pm} A| \ge 26$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the
Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 3. -/
public theorem card_restrictedSignedSumset_four_ge_of_one_exceptional_gap
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hgaps : (Finset.univ.filter fun i : Fin 4 =>
      a i.succ - a i.castSucc ≠ 2 * a 0).card = 1) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26 := by
  let gap (i : Fin 4) := a i.succ - a i.castSucc
  let badGaps := Finset.univ.filter fun i : Fin 4 => gap i ≠ 2 * a 0
  change badGaps.card = 1 at hgaps
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hgaps
  have hbad : gap k ≠ 2 * a 0 := by
    have hm : k ∈ badGaps := hk.symm ▸ Finset.mem_singleton_self k
    exact (Finset.mem_filter.mp hm).2
  have hregular (i : Fin 4) (hi : i ≠ k) : gap i = 2 * a 0 := by
    by_contra hn
    have hm : i ∈ badGaps := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    rw [hk, Finset.mem_singleton] at hm
    exact hi hm
  have hm (i : Fin 5) : a i ∈ orderedFinset a :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hcount := count_one_exceptional_gap hpos (ha (show (0 : Fin 5) < 1 by decide))
    (ha (show (1 : Fin 5) < 2 by decide)) (ha (show (2 : Fin 5) < 3 by decide))
    (ha (show (3 : Fin 5) < 4 by decide)) (hm 0) (hm 1) (hm 2) (hm 3) (hm 4)
  apply Int.ofNat_le.mpr
  apply hcount
  fin_cases k
  · exact Or.inl ⟨hbad, hregular 1 (by decide), hregular 2 (by decide), hregular 3 (by decide)⟩
  · exact Or.inr (Or.inl
      ⟨hregular 0 (by decide), hbad, hregular 2 (by decide), hregular 3 (by decide)⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨hregular 0 (by decide), hregular 1 (by decide), hbad, hregular 3 (by decide)⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨hregular 0 (by decide), hregular 1 (by decide), hregular 2 (by decide), hbad⟩))

end MetaMathlibExt
