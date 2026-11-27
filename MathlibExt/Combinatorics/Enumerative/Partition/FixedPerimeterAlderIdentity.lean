/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterAlder
import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterDistinctArmLeg
import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterResidueArmLeg
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# The fixed-perimeter partition identity

We equate the counts by reindexing the finite sums of the two binomial formulas
for partitions with a prescribed largest part and length.

## References

* Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher,
  *Analogues of Alder-Type Partition Inequalities for Fixed Perimeter Partitions*,
  INTEGERS 24 (2024), Article A102, pp. 1–17, Theorem 1 and Section 3, Lemmas 1 and 2.
-/

namespace MetaMathlibExt

-- A partition of perimeter n with j + 1 parts has largest part n - j.
private theorem card_filter_eq_sum_by_length (n : ℕ) (P : Multiset ℕ → Prop) [DecidablePred P] :
    ((fixedPerimeterPartitions n).filter P).card =
      ∑ j ∈ Finset.range n,
        ((fixedPerimeterPartitions (n - j + (j + 1) - 1)).filter fun s =>
          s.sup = n - j ∧ s.card = j + 1 ∧ P s).card := by
  calc
    _ = ∑ j ∈ Finset.range n,
        (((fixedPerimeterPartitions n).filter P).filter fun s => s.card - 1 = j).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro s hs
      obtain ⟨hpos, hsum⟩ := mem_fixedPerimeterPartitions.mp (Finset.mem_filter.mp hs).1
      have hne : s ≠ 0 := by rintro rfl; simp at hsum
      obtain ⟨x, hx⟩ := Multiset.toFinset_nonempty.mpr hne
      have hmax : 0 < s.sup := by
        rw [Multiset.mem_toFinset] at hx
        exact (hpos x hx).trans_le (Multiset.le_sup hx)
      have hcard := Multiset.card_pos.mpr hne
      change s.card - 1 ∈ Finset.range n
      exact Finset.mem_range.mpr (by omega)
    _ = _ := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjn := Finset.mem_range.mp hj
      rw [show n - j + (j + 1) - 1 = n by omega]
      congr 1
      ext s
      simp only [Finset.mem_filter, mem_fixedPerimeterPartitions]
      constructor
      · rintro ⟨⟨⟨hpos, hsum⟩, hp⟩, hlen⟩
        have hne : s ≠ 0 := by rintro rfl; simp at hsum
        have hcard := Multiset.card_pos.mpr hne
        exact ⟨⟨hpos, hsum⟩, by omega, by omega, hp⟩
      · rintro ⟨hs, -, hlen, hp⟩
        exact ⟨⟨hs, hp⟩, by omega⟩

/-- **Fixed-perimeter identity for $d$-distinct parts.** Let $d$ and $n$ be positive integers and
let $a$ be an integer with $1 \le a \le d + 1$. Then the number $h_d^{(a)}(n)$ of partitions of
perimeter $n$ into $d$-distinct parts (no part repeats and any two parts differ by at least $d$),
all at least $a$, equals the number $f_d^{(a)}(n)$ of partitions of perimeter $n$ into parts
congruent to $a$ modulo $d + 1$. Here the perimeter of a partition is its largest part plus its
number of parts minus $1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Theorem 1. -/
public theorem perimeterDistinctCount_eq_perimeterResidueCount {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 1 ≤ a) (had : a ≤ d + 1) :
    perimeterDistinctCount d a n = perimeterResidueCount d a n := by
  let distinct (j : ℕ) := perimeterDistinctArmLegCount d a (n - j) (j + 1)
  let residue (j : ℕ) := perimeterResidueArmLegCount d a (n - j) (j + 1)
  have hD (j : ℕ) (hj : j < n) :
      (distinct j ≠ 0 ↔ a + d * j ≤ n - j) ∧
        (a + d * j ≤ n - j → distinct j = (n - j - a - (d - 1) * j).choose j) := by
    simpa only [distinct, Nat.add_one_sub_one] using
      (perimeterDistinctArmLegCount_ne_zero_iff_and_eq_choose
        (m := n - j) (k := j + 1) hd ha (by omega) (Nat.succ_pos _) had)
  have hR (i : ℕ) (hi : i < n) :
      (residue i ≠ 0 ↔ a ≤ n - i ∧ n - i ≡ a [MOD d + 1]) ∧
        (a ≤ n - i → n - i ≡ a [MOD d + 1] →
          residue i = ((n - i - a) / (d + 1) + i).choose i) := by
    simpa only [residue, ← Nat.add_assoc, Nat.add_sub_cancel, Nat.add_one_sub_one] using
      (perimeterResidueArmLegCount_ne_zero_iff_and_eq_choose
        (m := n - i) (k := i + 1) hd ha (by omega) (Nat.succ_pos _) had)
  rw [perimeterDistinctCount, perimeterResidueCount, card_filter_eq_sum_by_length,
    card_filter_eq_sum_by_length]
  change (∑ j ∈ Finset.range n, distinct j) = ∑ i ∈ Finset.range n, residue i
  by_cases hna : n < a
  · trans 0
    · refine Finset.sum_eq_zero fun j hj => not_not.mp fun h => ?_
      have := (hD j (Finset.mem_range.mp hj)).1.mp h
      omega
    · symm
      refine Finset.sum_eq_zero fun i hi => not_not.mp fun h => ?_
      have := ((hR i (Finset.mem_range.mp hi)).1.mp h).1
      omega
  -- On both sides the nonzero terms are indexed by (d + 1) * j ≤ n - a.
  let support := (Finset.range n).filter fun j => (d + 1) * j ≤ n - a
  let i (j : ℕ) := n - (a + (d + 1) * j)
  let residues := (Finset.range n).filter fun i => residue i ≠ 0
  have hbound (j : ℕ) (hj : j ∈ support) : a + (d + 1) * j ≤ n := by
    have := (Finset.mem_filter.mp hj).2
    omega
  have hi (j : ℕ) : i j < n := by dsimp [i]; omega
  have hmax (j : ℕ) (hj : j ∈ support) : n - i j = a + (d + 1) * j := by
    have := hbound j hj
    dsimp [i]
    omega
  have hmod (j : ℕ) (hj : j ∈ support) : n - i j ≡ a [MOD d + 1] := by
    rw [hmax j hj]
    simp
  calc
    _ = ∑ j ∈ support, distinct j := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun j hj hj' => not_not.mp fun h => ?_
      have hjn := Finset.mem_range.mp hj
      have hs := (hD j hjn).1.mp h
      apply hj'
      refine Finset.mem_filter.mpr ⟨hj, ?_⟩
      rw [Nat.add_mul, one_mul]
      omega
    _ = ∑ j ∈ support, (n - a - d * j).choose j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjn := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hb := hbound j hj
      rw [Nat.add_mul, one_mul] at hb
      rw [(hD j hjn).2 (by omega)]
      have hmul : (d - 1) * j + j = d * j := by
        rw [← Nat.succ_mul, show (d - 1).succ = d by omega]
      congr 1; omega
    _ = ∑ i ∈ residues, residue i := by
      refine Finset.sum_nbij i (fun j hj => ?_) (fun j hj j' hj' heq => ?_)
        (fun k hk => ?_) (fun j hj => ?_)
      · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hi j), (hR (i j) (hi j)).1.mpr ?_⟩
        exact ⟨hmax j hj ▸ Nat.le_add_right _ _, hmod j hj⟩
      · have h := hmax j hj
        have h' := hmax j' hj'
        rw [heq, h'] at h
        exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos _) (Nat.add_left_cancel h.symm)
      · obtain ⟨hkr, hkne⟩ := Finset.mem_filter.mp hk
        have hkn := Finset.mem_range.mp hkr
        obtain ⟨hak, hmk⟩ := (hR k hkn).1.mp hkne
        obtain ⟨j, hj⟩ := (Nat.modEq_iff_exists_eq_add hak).mp hmk.symm
        have hjle : j ≤ (d + 1) * j := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩,
          by dsimp [i]; omega⟩
      · have hm := hmax j hj
        have hdiv : (n - i j - a) / (d + 1) = j := by
          simp [hm, Nat.mul_div_cancel_left _ (Nat.succ_pos d)]
        rw [(hR (i j) (hi j)).2 (hm ▸ Nat.le_add_right _ _) (hmod j hj), hdiv,
          Nat.choose_symm_of_eq_add (Nat.add_comm j (i j))]
        rw [Nat.add_mul, one_mul] at hm
        congr 1; omega
    _ = _ := Finset.sum_filter_ne_zero _

end MetaMathlibExt
