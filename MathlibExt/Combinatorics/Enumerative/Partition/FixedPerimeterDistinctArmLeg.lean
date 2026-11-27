/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterAlder
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Choose.Sum

/-!
# Counting partitions with separated parts

For a fixed largest part and length, we determine when the number of partitions with
$d$-distinct parts is positive and express it as a binomial coefficient.
-/

namespace MetaMathlibExt

private def armLegPartitions (d a m k : ℕ) : Finset (Multiset ℕ) :=
  (fixedPerimeterPartitions (m + k - 1)).filter fun s =>
    s.sup = m ∧ Multiset.card s = k ∧ IsDDistinctParts d s ∧ ∀ x ∈ s, a ≤ x

private theorem mem_armLegPartitions {d a m k : ℕ} {s : Multiset ℕ} (ha : 0 < a) (hk : 0 < k) :
    s ∈ armLegPartitions d a m k ↔
      s.sup = m ∧ Multiset.card s = k ∧ IsDDistinctParts d s ∧ ∀ x ∈ s, a ≤ x := by
  rw [armLegPartitions, Finset.mem_filter, mem_fixedPerimeterPartitions]
  refine ⟨And.right, fun h => ⟨⟨fun x hx => ha.trans_le (h.2.2.2 x hx), ?_⟩, h⟩⟩
  rw [h.1, h.2.1]
  omega

private theorem sup_mem_of_card_pos {s : Multiset ℕ} (hs : 0 < Multiset.card s) : s.sup ∈ s := by
  have h := s.toFinset.sup_mem_of_nonempty (f := id)
    (Multiset.toFinset_nonempty.mpr (Multiset.card_pos.mp hs))
  simpa [Finset.sup_def] using h

-- Removing the largest part leaves a partition whose largest part is at least d below it.
private theorem cons_mem_armLegPartitions {d a m k : ℕ} {t : Multiset ℕ}
    (hd : 0 < d) (ha : 0 < a) (hk : 0 < k) :
    m ::ₘ t ∈ armLegPartitions d a m (k + 1) ↔
      t ∈ armLegPartitions d a t.sup k ∧ t.sup + d ≤ m := by
  rw [mem_armLegPartitions ha (by omega), mem_armLegPartitions ha hk]
  simp only [Multiset.sup_cons, sup_eq_left, Multiset.card_cons, Nat.add_right_cancel_iff,
    IsDDistinctParts, Multiset.nodup_cons, Multiset.mem_cons, forall_eq_or_imp, lt_irrefl,
    false_implies, true_and]
  constructor
  · rintro ⟨hle, hcard, ⟨⟨hm, hnd⟩, -, hgap⟩, -, hmin⟩
    have ht : t.sup ∈ t := sup_mem_of_card_pos (hcard ▸ hk)
    have hlt := lt_of_le_of_ne hle (fun heq => hm (heq ▸ ht))
    exact ⟨⟨hcard, ⟨hnd, fun x hx => (hgap x hx).2⟩, hmin⟩, (hgap _ ht).1 hlt⟩
  · rintro ⟨⟨hcard, ⟨hnd, hgap⟩, hmin⟩, hle⟩
    have ht : t.sup ∈ t := sup_mem_of_card_pos (hcard ▸ hk)
    have hlt (x : ℕ) (hx : x ∈ t) : x < m :=
      (Multiset.le_sup hx).trans_lt (by omega)
    refine ⟨by omega, hcard, ⟨⟨fun hm => (hlt m hm).false, hnd⟩,
      fun x hx hmx => (lt_asymm hmx (hlt x hx)).elim, fun x hx => ⟨?_, hgap x hx⟩⟩,
      (hmin _ ht).trans (by omega), hmin⟩
    exact fun _ => (Nat.add_le_add_right (Multiset.le_sup hx) d).trans hle

-- Index each possible second-largest part by its excess over the lower bound b.
private theorem card_armLegPartitions_succ {d a m k b : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hk : 0 < k)
    (hb : ∀ j, (armLegPartitions d a j k).Nonempty → b ≤ j) :
    (armLegPartitions d a m (k + 1)).card =
      ∑ i ∈ Finset.range (m + 1 - (b + d)), (armLegPartitions d a (b + i) k).card := by
  rw [← Finset.card_sigma]
  symm
  apply Finset.card_bij (fun p _ => m ::ₘ p.2)
  · rintro ⟨i, t⟩ hp
    obtain ⟨hi, ht⟩ := Finset.mem_sigma.mp hp
    change i ∈ Finset.range _ at hi
    change t ∈ armLegPartitions d a (b + i) k at ht
    have hsup := ((mem_armLegPartitions ha hk).mp ht).1
    rw [cons_mem_armLegPartitions hd ha hk, hsup]
    exact ⟨ht, by have := Finset.mem_range.mp hi; omega⟩
  · rintro ⟨i, s⟩ hs ⟨j, t⟩ ht heq
    have hst : s = t := (Multiset.cons_inj_right m).mp heq
    subst t
    have hi : s.sup = b + i := ((mem_armLegPartitions ha hk).mp (Finset.mem_sigma.mp hs).2).1
    have hj : s.sup = b + j := ((mem_armLegPartitions ha hk).mp (Finset.mem_sigma.mp ht).2).1
    congr 1
    omega
  · intro s hs
    obtain ⟨hsup, hcard, -⟩ := (mem_armLegPartitions ha (by omega)).mp hs
    have hm : m ∈ s := hsup ▸ sup_mem_of_card_pos (s := s) (by omega)
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hm
    obtain ⟨ht, hgap⟩ := (cons_mem_armLegPartitions hd ha hk).mp hs
    have hb' := hb t.sup ⟨t, ht⟩
    have hi : t.sup - b < m + 1 - (b + d) := by omega
    refine ⟨⟨t.sup - b, t⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hi, ?_⟩, rfl⟩
    change t ∈ armLegPartitions d a (b + (t.sup - b)) k
    rwa [Nat.add_sub_of_le hb']

private theorem card_armLegPartitions {d a : ℕ} (hd : 0 < d) (ha : 0 < a) (r m : ℕ) :
    (armLegPartitions d a m (r + 1)).card =
      if a + d * r ≤ m then (m - (a + d * r) + r).choose r else 0 := by
  induction r generalizing m with
  | zero =>
    have hsingle : armLegPartitions d a m 1 =
        ({{m}} : Finset (Multiset ℕ)).filter (fun _ => a ≤ m) := by
      ext s
      rw [mem_armLegPartitions ha (by decide), Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hsup, hcard, -, hmin⟩
        obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hcard
        simp_all
      · rintro ⟨rfl, ham⟩
        simp [IsDDistinctParts, ham]
    by_cases ham : a ≤ m <;> simp [hsingle, ham]
  | succ r ih =>
    let b := a + d * r
    have hb (j : ℕ) (hj : (armLegPartitions d a j (r + 1)).Nonempty) : b ≤ j := by
      by_contra h
      have hc := Finset.card_pos.mpr hj
      rw [ih, ite_eq_right h] at hc
      omega
    rw [card_armLegPartitions_succ hd ha (by omega) hb, Nat.mul_succ, ← Nat.add_assoc]
    change (∑ i ∈ Finset.range (m + 1 - (b + d)), (armLegPartitions d a (b + i) (r + 1)).card) =
      if b + d ≤ m then (m - (b + d) + (r + 1)).choose (r + 1) else 0
    have hterm (i : ℕ) : (armLegPartitions d a (b + i) (r + 1)).card = (i + r).choose r := by
      simp [ih, b]
    simp_rw [hterm]
    by_cases h : b + d ≤ m
    · rw [ite_eq_left h, show m + 1 - (b + d) = (m - (b + d)) + 1 by omega]
      simpa [Nat.add_assoc] using Nat.sum_range_add_choose (m - (b + d)) r
    · simp [h, show m + 1 - (b + d) = 0 by omega]

set_option linter.unusedVariables false in
/-- **Counting d-distinct partitions by largest part and length.** Let $d$, $a$, $m$ and $k$ be
positive integers with $a \le d + 1$, and write $h_d^{(a)}(m, k)$ for the number of partitions into
$d$-distinct parts, all at least $a$, with largest part $m$ and $k$ parts. Then
$h_d^{(a)}(m, k) \ne 0$ if and only if $m \ge a + d(k - 1)$, and in that case
$h_d^{(a)}(m, k) = \binom{m - a - (d - 1)(k - 1)}{k - 1}$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Lemma 1. -/
public theorem perimeterDistinctArmLegCount_ne_zero_iff_and_eq_choose {d a m k : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hm : 0 < m) (hk : 0 < k) (had : a ≤ d + 1) :
    (perimeterDistinctArmLegCount d a m k ≠ 0 ↔ a + d * (k - 1) ≤ m) ∧
      (a + d * (k - 1) ≤ m →
        perimeterDistinctArmLegCount d a m k = (m - a - (d - 1) * (k - 1)).choose (k - 1)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp only [Nat.add_one_sub_one]
  change ((armLegPartitions d a m (r + 1)).card ≠ 0 ↔ _) ∧
    (_ → (armLegPartitions d a m (r + 1)).card = _)
  rw [card_armLegPartitions hd ha]
  by_cases h : a + d * r ≤ m
  · have hmul : (d - 1) * r + r = d * r := by
      rw [← Nat.succ_mul, show (d - 1).succ = d by omega]
    have htop : m - (a + d * r) + r = m - a - (d - 1) * r := by omega
    simp [h, ← htop, (Nat.choose_pos (Nat.le_add_left r (m - (a + d * r)))).ne']
  · simp [h]

end MetaMathlibExt
