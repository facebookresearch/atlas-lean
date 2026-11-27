/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Ring.Int
public import MathlibExt.Combinatorics.Additive.BoundedSubsetSums

/-!
# The Yang–Chen lower bound for generalized sumsets

Moving one summand to the next index gives the sharp Yang–Chen lower bound for the
cardinality of a generalized `h`-fold sumset of integers. The proof follows the adjacent
steps of Yang and Chen, *On the cardinality of general h-fold sumsets*, Section 2.
-/

namespace MetaMathlibExt

namespace YangChen

variable {k : ℕ}

private def Feasible (r : Fin k → ℕ) (h : ℕ) (s : Fin k → ℕ) : Prop :=
  (∀ i, s i ≤ r i) ∧ ∑ i, s i = h

private def weight (a : Fin k → ℤ) (s : Fin k → ℕ) : ℤ := ∑ i, a i * s i

private abbrev idx (i : Fin k) : ℤ := i.val

private lemma mem_sumset {a : Fin k → ℤ} {r : Fin k → ℕ} {h : ℕ} {x : ℤ} :
    x ∈ generalizedHFoldSumset a r h ↔ ∃ s, Feasible r h s ∧ weight a s = x := by
  simp [generalizedHFoldSumset, Feasible, weight, mul_comm, Nat.lt_succ_iff]

-- Centering at the cutoff makes the contribution of each coordinate minimal.
private lemma weight_le_of_packed {r s t : Fin k → ℕ} {h : ℕ} {a : Fin k → ℤ} (c : ℤ)
    (hs : Feasible r h s) (ht : Feasible r h t)
    (hfull : ∀ i, a i < c → s i = r i) (hempty : ∀ i, c < a i → s i = 0) :
    weight a s ≤ weight a t := by
  have centered (v : Fin k → ℕ) (hv : Feasible r h v) :
      ∑ i, (a i - c) * v i = weight a v - c * h := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, weight]
    rw [← Nat.cast_sum, hv.2]
  have hle : ∑ i, (a i - c) * s i ≤ ∑ i, (a i - c) * t i := by
    apply Finset.sum_le_sum
    intro i _
    rcases lt_trichotomy (a i) c with hi | hi | hi
    · rw [hfull i hi]
      exact mul_le_mul_of_nonpos_left (by exact_mod_cast ht.1 i) (by omega)
    · simp [hi]
    · rw [hempty i hi]
      simp only [Nat.cast_zero, mul_zero]
      exact mul_nonneg (by omega) (Int.natCast_nonneg _)
  rwa [centered s hs, centered t ht, sub_le_sub_iff_right] at hle

private def capacity (e : Equiv.Perm (Fin k)) (r : Fin k → ℕ) (n : ℕ) : ℕ :=
  ∑ i : Fin k with (e i).val < n, r i

private def cutoff (e : Equiv.Perm (Fin k)) (r : Fin k → ℕ) (h : ℕ) : ℕ :=
  Nat.findGreatest (fun n => capacity e r n ≤ h) k

-- Fill the coordinates in the order prescribed by e, with at most one partial coordinate.
private lemma exists_packed (e : Equiv.Perm (Fin k)) (r : Fin k → ℕ) (h : ℕ)
    (hhr : h ≤ ∑ i, r i) (a : Fin k → ℤ) (b : ℤ) (ha : ∀ i, a i = idx (e i) + b) :
    let m := cutoff e r h
    ∃ s, Feasible r h s ∧
      weight a s = (∑ i : Fin k with (e i).val < m, a i * r i) +
        ((h : ℤ) - capacity e r m) * (m + b) ∧
      ∀ t, Feasible r h t → weight a s ≤ weight a t := by
  dsimp only
  let m := cutoff e r h
  have hmk : m ≤ k := Nat.findGreatest_le _
  have hpre : capacity e r m ≤ h :=
    Nat.findGreatest_spec (P := fun n => capacity e r n ≤ h) (Nat.zero_le k)
      (by simp [capacity])
  by_cases hm : m = k
  · have hall (i : Fin k) : (e i).val < m := by simpa only [hm] using (e i).isLt
    have hcap : capacity e r m = ∑ i, r i := by simp [capacity, hall]
    have htot : ∑ i, r i = h := by omega
    have hf : Feasible r h r := ⟨fun _ => le_rfl, htot⟩
    refine ⟨r, hf, ?_, fun t ht => weight_le_of_packed ((m : ℤ) + b) hf ht
      (fun _ _ => rfl) (fun i hi => ?_)⟩
    · change weight a r = (∑ i : Fin k with (e i).val < m, _) + ((h : ℤ) - capacity e r m) * _
      simp [weight, hall, hcap.trans htot]
    · have := hall i
      rw [ha] at hi
      unfold idx at hi
      omega
  · let j := e.symm ⟨m, by omega⟩
    have hj : (e j).val = m := by simp [j]
    have heq (i : Fin k) : (e i).val = m ↔ i = j := by
      rw [← hj, Fin.val_inj, e.injective.eq_iff]
    let base := fun i => if (e i).val < m then r i else 0
    have hbase : ∑ i, base i = capacity e r m := by simp [base, capacity, Finset.sum_filter]
    have hnext : capacity e r (m + 1) = capacity e r m + r j := by
      have split_at (i : Fin k) : (if (e i).val < m + 1 then r i else 0) =
          base i + (if i = j then r i else 0) := by
        by_cases hij : i = j
        · subst i
          simp [hj, base]
        · have := (heq i).not.mpr hij
          simp [base, hij, show (e i).val < m + 1 ↔ (e i).val < m by omega]
      simp [capacity, Finset.sum_filter, split_at, Finset.sum_add_distrib, base]
    have hmax : ¬ capacity e r (m + 1) ≤ h :=
      Nat.findGreatest_is_greatest (P := fun n => capacity e r n ≤ h)
        (show m < m + 1 by omega) (by omega)
    let d := h - capacity e r m
    let s := fun i => base i + if i = j then d else 0
    have hs : Feasible r h s := by
      constructor
      · intro i
        by_cases hij : i = j
        · subst i
          simp [s, base, hj, d]
          omega
        · simp [s, base, hij]
          split <;> omega
      · simp [s, Finset.sum_add_distrib, hbase, d, hpre]
    refine ⟨s, hs, ?_, fun t ht => weight_le_of_packed ((m : ℤ) + b) hs ht ?_ ?_⟩
    · change weight a s = (∑ i : Fin k with (e i).val < m, _) + _
      have haj : a j = (m : ℤ) + b := by simp [ha, idx, hj]
      simp [weight, s, base, Finset.sum_filter, mul_add, mul_ite, Finset.sum_add_distrib,
        apply_ite Nat.cast, d, Nat.cast_sub hpre, haj, mul_comm, m]
    · intro i hi
      rw [ha] at hi
      have hlt : (e i).val < m := by simpa [idx] using hi
      have hij := (heq i).not.mp hlt.ne
      simp [s, base, hlt, hij]
    · intro i hi
      rw [ha] at hi
      have hgt : m < (e i).val := by simpa [idx] using hi
      have hij := (heq i).not.mp hgt.ne'
      simp [s, base, hgt.not_gt, hij]

private lemma weight_neg (a : Fin k → ℤ) (s : Fin k → ℕ) :
    weight (-a) s = -weight a s := by simp [weight]

-- Unless the rightmost packing has been reached, one occupied coordinate has room to its right.
private lemma exists_adjacent {r s t : Fin k → ℕ} {h : ℕ} (hr : ∀ i, 0 < r i)
    (hh : 0 < h) (hs : Feasible r h s) (ht : Feasible r h t)
    (hlt : weight idx s < weight idx t) :
    ∃ i j : Fin k, j.val = i.val + 1 ∧ 0 < s i ∧ s j < r j := by
  by_contra! hstop
  let occupied := Finset.univ.filter fun i => 0 < s i
  have hne : occupied.Nonempty :=
    Finset.filter_nonempty_iff.mpr (Finset.sum_pos_iff.mp (hs.2.symm ▸ hh))
  let m := occupied.min' hne
  have hmpos : 0 < s m := (Finset.mem_filter.mp (occupied.min'_mem hne)).2
  have hright (n : ℕ) (hn : m.val ≤ n) (hnk : n < k) :
      0 < s ⟨n, hnk⟩ ∧ (m.val < n → s ⟨n, hnk⟩ = r ⟨n, hnk⟩) := by
    induction n, hn using Nat.le_induction with
    | base => exact ⟨hmpos, fun hlt => (lt_irrefl _ hlt).elim⟩
    | succ n hn ih =>
      let i : Fin k := ⟨n, by omega⟩
      let j : Fin k := ⟨n + 1, hnk⟩
      have hfull : s j = r j := le_antisymm (hs.1 j) (hstop i j rfl (ih i.isLt).1)
      exact ⟨hfull ▸ hr j, fun _ => hfull⟩
  have hle := weight_le_of_packed (a := -idx) (-idx m) hs ht (by
    intro i hi
    exact (hright i.val (by simpa [idx] using hi.le) i.isLt).2 (by simpa [idx] using hi)) (by
    intro i hi
    by_contra! hn
    have hmi : m ≤ i := occupied.min'_le i
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hn⟩)
    have : i < m := by simpa [idx] using hi
    omega)
  rw [weight_neg, weight_neg] at hle
  omega

private lemma move_one {r s : Fin k → ℕ} {h : ℕ} (hs : Feasible r h s)
    {i j : Fin k} (hij : i ≠ j) (hi : 0 < s i) (hj : s j < r j) :
    ∃ u, Feasible r h u ∧ ∀ a, weight a u + a i = weight a s + a j := by
  let u := fun l => (s l - if l = i then 1 else 0) + if l = j then 1 else 0
  have balance (l : Fin k) :
      u l + (if l = i then 1 else 0) = s l + (if l = j then 1 else 0) := by
    by_cases hli : l = i
    · subst l
      simp [u, hij]
      omega
    · simp [u, hli]
  refine ⟨u, ⟨?_, ?_⟩, ?_⟩
  · intro l
    by_cases hlj : l = j
    · subst l
      simpa [u, Ne.symm hij] using Nat.succ_le_of_lt hj
    · simpa [u, hlj] using (Nat.sub_le (s l) (if l = i then 1 else 0)).trans (hs.1 l)
  · have heq := Finset.sum_congr (s₁ := Finset.univ) rfl (fun l _ => balance l)
    simpa [Finset.sum_add_distrib, hs.2] using heq
  · intro a
    have heq (l : Fin k) := congrArg (fun n : ℕ => a l * (n : ℤ)) (balance l)
    have := Finset.sum_congr (s₁ := Finset.univ) rfl (fun l _ => heq l)
    simpa [weight, Nat.cast_add, mul_add, mul_ite, apply_ite Nat.cast, Finset.sum_add_distrib]
      using this

private lemma count_steps {r t : Fin k → ℕ} {h : ℕ} {a : Fin k → ℤ}
    (hr : ∀ i, 0 < r i) (hh : 0 < h) (ha : StrictMono a) (ht : Feasible r h t)
    (n : ℕ) (s : Fin k → ℕ) (hs : Feasible r h s) (hn : weight idx s + n ≤ weight idx t) :
    n + 1 ≤ ((generalizedHFoldSumset a r h).filter fun x => weight a s ≤ x).card := by
  have mem (v : Fin k → ℕ) (hv : Feasible r h v) : weight a v ∈ generalizedHFoldSumset a r h :=
    mem_sumset.mpr ⟨v, hv, rfl⟩
  induction n generalizing s with
  | zero => exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨mem s hs, le_rfl⟩⟩
  | succ n ih =>
    obtain ⟨i, j, hij, hi, hj⟩ := exists_adjacent hr hh hs ht (by omega)
    have hlt : i < j := Fin.mk_lt_mk.mpr (by omega)
    obtain ⟨u, hu, hmove⟩ := move_one hs hlt.ne hi hj
    have hidx := hmove idx
    change weight idx u + (i.val : ℤ) = weight idx s + (j.val : ℤ) at hidx
    have hinc : weight a s < weight a u := by
      have := hmove a
      have := ha hlt
      omega
    have hcount := ih u hu (by omega)
    refine hcount.trans_lt (Finset.card_lt_card ?_)
    apply (Finset.ssubset_iff_of_subset (Finset.monotone_filter_right _ fun _ _ hx =>
      hinc.le.trans hx)).mpr
    exact ⟨weight a s, Finset.mem_filter.mpr ⟨mem s hs, le_rfl⟩,
      fun hx => hinc.not_ge (Finset.mem_filter.mp hx).2⟩

end YangChen

open YangChen

/-- **Yang–Chen lower bound for generalized $h$-fold sumsets.** Let $k, h \in \mathbb{N}$ and let
$\bar r = (r_0, \dots, r_{k-1})$ be positive integers with $2 \le h \le r_0 + \dots + r_{k-1}$, and
let $L(\bar r, h)$ be the Yang–Chen bound. For all integers $a_0 < a_1 < \dots < a_{k-1}$, the
generalized $h$-fold sumset $h^{(\bar r)}A$ of $A = (a_0, \dots, a_{k-1})$ has at least
$L(\bar r, h)$ elements; and there exist integers $a_0 < a_1 < \dots < a_{k-1}$ for which
$h^{(\bar r)}A$ has exactly $L(\bar r, h)$ elements.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 2 (Yang and Chen) (`integers-2024-A116-thm-2`). -/
public theorem yangChen_card_generalizedHFoldSumset_ge {k : ℕ} (r : Fin k → ℕ)
    (hr : ∀ i, 0 < r i) (h : ℕ) (hh : 2 ≤ h) (hhr : h ≤ ∑ i, r i) :
    (∀ a : Fin k → ℤ, StrictMono a →
      yangChenBound r h ≤ (generalizedHFoldSumset a r h).card) ∧
    ∃ a : Fin k → ℤ, StrictMono a ∧
      ((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h := by
  let m := cutoff (Equiv.refl _) r h
  let n := cutoff Fin.revPerm r h
  obtain ⟨lo, hlo, hlo_val, hlo_min⟩ := exists_packed (Equiv.refl _) r h hhr idx 0 (by simp)
  obtain ⟨hi, hhi, hhi_val, hhi_min⟩ := exists_packed Fin.revPerm r h hhr (-idx) (1 - k) (by
    intro i
    simp only [Pi.neg_apply, idx, Fin.revPerm_apply, Fin.val_rev]
    omega)
  simp only [weight_neg, neg_le_neg_iff] at hhi_min
  have suffix (v : ℕ) : (Finset.univ.filter fun i : Fin k => (Fin.revPerm i).val < v) =
      Finset.univ.filter fun i : Fin k => k - v ≤ i.val := by
    apply Finset.filter_congr
    intro i _
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  have hcap (v : ℕ) : capacity Fin.revPerm r v = ∑ i : Fin k with k - v ≤ i.val, r i := by
    rw [capacity, suffix]
  have hcut : n = Nat.findGreatest (fun v => (∑ i : Fin k with k - v ≤ i.val, r i) ≤ h) k := by
    simp only [n, cutoff, hcap]
  have hn : n ≤ k := Nat.findGreatest_le _
  have hedge : ((k - n : ℕ) : ℤ) - 1 = -((n : ℤ) + (1 - k)) := by omega
  have hbound : yangChenBound r h = weight idx hi - weight idx lo + 1 := by
    change weight idx lo = _ + ((h : ℤ) - capacity _ r m) * ((m : ℤ) + 0) at hlo_val
    change weight (-idx) hi = (∑ i : Fin k with (Fin.revPerm i).val < n, _) +
      ((h : ℤ) - capacity _ r n) * ((n : ℤ) + (1 - k)) at hhi_val
    simp only [weight_neg, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, suffix, hcap] at hhi_val
    simp only [Equiv.refl_apply, add_zero] at hlo_val
    dsimp only [yangChenBound]
    rw [← hcut, hedge, mul_neg]
    let leftSum := ∑ i : Fin k with i.val < m, idx i * r i
    let rightSum := ∑ i : Fin k with k - n ≤ i.val, idx i * r i
    change weight idx lo = leftSum + ((h : ℤ) - capacity (Equiv.refl _) r m) * m at hlo_val
    change -weight idx hi = -rightSum + _ at hhi_val
    change rightSum - leftSum + _ - (((h : ℤ) - capacity (Equiv.refl _) r m) * m) + 1 = _
    omega
  have lower (a : Fin k → ℤ) (ha : StrictMono a) :
      yangChenBound r h ≤ (generalizedHFoldSumset a r h).card := by
    have hle := hlo_min hi hhi
    have hsteps := count_steps hr (by omega) ha hhi (weight idx hi - weight idx lo).toNat lo hlo
      (by omega)
    have hcard := Finset.card_filter_le (generalizedHFoldSumset a r h) (fun x => weight a lo ≤ x)
    omega
  have hmono : StrictMono (idx (k := k)) := fun _ _ hij => by exact_mod_cast hij
  refine ⟨lower, idx, hmono, le_antisymm ?_ (lower idx hmono)⟩
  have hsub : generalizedHFoldSumset idx r h ⊆ Finset.Icc (weight idx lo) (weight idx hi) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_sumset.mp hx
    exact Finset.mem_Icc.mpr ⟨hlo_min s hs, hhi_min s hs⟩
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have := hlo_min hi hhi
  omega

end MetaMathlibExt
