/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Combinatorics/BalanceableBoundedPartitions.lean`
(leanprover/lean-eval, revision 38361be884302c7edce1908c4aef8296eb2cb27e):
the two definitions and the statement of the balanceable bounded partitions theorem.
Copyright 2026 Lean FRO, LLC.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Julia M. Himmel (lean-eval submission).

ATLAS placed these declarations in their present namespace and moved them from
`WantedExt/Combinatorics/BalanceableBoundedPartitionsWanted.lean` when the theorem was proved.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import MathlibExt.Combinatorics.Additive.ConsecutiveZeroSum

/-!
# Balanceable bounded partitions

This module defines bounded and balanceable partitions and proves that the first positive size
forcing all `k`-bounded partitions to be balanceable is twice the least common multiple of
the integers from `1` to `k`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.BalanceableBoundedPartitionsWanted
namespace Combinatorics

set_option linter.dupNamespace false in
/--
**$k$-bounded partition.** A partition of $n$ is $k$-bounded if each of its parts is at most $k$.

For example, $12 = 3 + 2 + 2 + 2 + 2 + 1$ is a $3$-bounded partition of $12$.
-/
def Bounded {n : ℕ} (k : ℕ) (p : n.Partition) : Prop :=
  ∀ i ∈ p.parts, i ≤ k

set_option linter.dupNamespace false in
/--
**Balanceable partition.** A partition of $n$ is balanceable if its multiset of parts can be split
as $s_1 + s_2$ into two multisets $s_1$ and $s_2$ whose elements have equal sums.

For example, $12 = (3 + 2 + 1) + (2 + 2 + 2)$ is a balanceable partition of $12$.
-/
def Balanceable {n : ℕ} (p : n.Partition) : Prop :=
  ∃ s₁ s₂, s₁ + s₂ = p.parts ∧ s₁.sum = s₂.sum

open Finset

private theorem dvd_interval_lcm {a k : ℕ} (ha : 0 < a) (hak : a ≤ k) :
    a ∣ (Icc 1 k).lcm id :=
  Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨ha, hak⟩)

private theorem interval_lcm_pos (k : ℕ) : 0 < (Icc 1 k).lcm id := by
  apply Nat.pos_of_ne_zero
  rw [Ne, Finset.lcm_eq_zero_iff]
  simp

private theorem consecutive_coprime (j : ℕ) : Nat.Coprime j (j + 1) :=
  Nat.coprime_self_add_right.mpr (Nat.coprime_one_right j)

private theorem reserve_le_lcm {a k : ℕ} (hak : a ≤ k) :
    (k - 1) * a ≤ (Icc 1 k).lcm id := by
  by_cases hk : 2 ≤ k
  · have hcop : Nat.Coprime (k - 1) k := by
      simpa only [show k - 1 + 1 = k by omega] using consecutive_coprime (k - 1)
    refine (Nat.mul_le_mul_left _ hak).trans (Nat.le_of_dvd (interval_lcm_pos k) ?_)
    exact hcop.mul_dvd_of_dvd_of_dvd
      (dvd_interval_lcm (by omega) (by omega)) (dvd_interval_lcm (by omega) le_rfl)
  · simp [show k - 1 = 0 by omega]

-- The middle of three consecutive numbers is coprime to the LCM of the other two.
private theorem triple_le_twice_lcm (j : ℕ) (hj : 0 < j) :
    j * (j + 2) * (j + 1) ≤ 2 * (Icc 1 (j + 2)).lcm id := by
  have hcop : Nat.Coprime (j.lcm (j + 2)) (j + 1) := by
    apply Nat.Coprime.of_dvd_left
      (Nat.lcm_dvd (Nat.dvd_mul_right j (j + 2)) (Nat.dvd_mul_left (j + 2) j))
    exact (consecutive_coprime j).mul_left (consecutive_coprime (j + 1)).symm
  have hdvd : j.lcm (j + 2) * (j + 1) ∣ (Icc 1 (j + 2)).lcm id :=
    hcop.mul_dvd_of_dvd_of_dvd
      (Nat.lcm_dvd (dvd_interval_lcm hj (by omega)) (dvd_interval_lcm (by omega) le_rfl))
      (dvd_interval_lcm (by omega) (by omega))
  have hgcd : j.gcd (j + 2) ≤ 2 :=
    Nat.le_of_dvd (by decide) (Nat.dvd_add_iff_right (Nat.gcd_dvd_left _ _)
      |>.mpr (Nat.gcd_dvd_right _ _))
  calc
    j * (j + 2) * (j + 1) = j.gcd (j + 2) * j.lcm (j + 2) * (j + 1) := by
      rw [Nat.gcd_mul_lcm]
    _ ≤ 2 * (j.lcm (j + 2) * (j + 1)) := by
      rw [← mul_assoc]
      gcongr
    _ ≤ 2 * (Icc 1 (j + 2)).lcm id :=
      Nat.mul_le_mul_left _ (Nat.le_of_dvd (interval_lcm_pos _) hdvd)

private theorem few_copies_bound (k : ℕ) :
    (k - 2) * (∑ a ∈ Icc 1 k, a) < 2 * (Icc 1 k).lcm id := by
  by_cases hk : 4 ≤ k
  · have hsum : (∑ a ∈ Icc 1 k, a) * 2 = (k + 1) * k := by
      have hr : range (k + 1) = insert 0 (Icc 1 k) := by
        ext a
        simp only [mem_range, mem_insert, mem_Icc]
        omega
      have hzero : 0 ∉ Icc 1 k := by simp
      simpa [hr, sum_insert hzero] using Finset.sum_range_id_mul_two (k + 1)
    have htriple := triple_le_twice_lcm (k - 2) (by omega)
    rw [show k - 2 + 2 = k by omega, show k - 2 + 1 = k - 1 by omega] at htriple
    have hlt : (k + 1) * ((k - 2) * k) < (2 * (k - 1)) * ((k - 2) * k) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (Nat.mul_pos (by omega) (by omega))
    apply Nat.lt_of_mul_lt_mul_right (a := 2)
    calc
      (k - 2) * (∑ a ∈ Icc 1 k, a) * 2 = (k + 1) * ((k - 2) * k) := by
        rw [mul_assoc, hsum]
        ac_rfl
      _ < (2 * (k - 1)) * ((k - 2) * k) := hlt
      _ = ((k - 2) * k * (k - 1)) * 2 := by ac_rfl
      _ ≤ (2 * (Icc 1 k).lcm id) * 2 := Nat.mul_le_mul_right _ htriple
  · interval_cases k <;> decide

private theorem exists_many_copies {k : ℕ}
    (p : (2 * (Icc 1 k).lcm id).Partition) (hp : Bounded k p) :
    ∃ a ∈ Icc 1 k, k - 1 ≤ p.parts.count a := by
  by_contra! h
  have hsub : p.parts.toFinset ⊆ Icc 1 k := by
    intro a ha
    have ha' := Multiset.mem_toFinset.mp ha
    exact mem_Icc.mpr ⟨p.parts_pos ha', hp a ha'⟩
  have hsum : p.parts.sum = ∑ a ∈ p.parts.toFinset, p.parts.count a * a := by
    simpa [nsmul_eq_mul] using Finset.sum_multiset_count p.parts
  have hle : p.parts.sum ≤ (k - 2) * (∑ a ∈ Icc 1 k, a) := calc
    p.parts.sum = ∑ a ∈ p.parts.toFinset, p.parts.count a * a := hsum
    _ ≤ ∑ a ∈ p.parts.toFinset, (k - 2) * a := by
      apply Finset.sum_le_sum
      intro a ha
      have := h a (hsub ha)
      exact Nat.mul_le_mul_right _ (by omega)
    _ ≤ ∑ a ∈ Icc 1 k, (k - 2) * a :=
      Finset.sum_le_sum_of_subset hsub
    _ = (k - 2) * (∑ a ∈ Icc 1 k, a) := by rw [Finset.mul_sum]
  rw [p.parts_sum] at hle
  exact (few_copies_bound k).not_ge hle

-- Apply the consecutive zero-sum theorem to the first `a` terms, indexed by position.
private theorem exists_small_dvd_sum {a : ℕ} (ha : 0 < a) {u : Multiset ℕ}
    (hu : a ≤ u.card) :
    ∃ w ≤ u, 0 < w.card ∧ w.card ≤ a ∧ a ∣ w.sum := by
  obtain ⟨l, rfl⟩ := Quotient.mk_surjective u
  have hlen : a ≤ l.length := hu
  have : NeZero a := ⟨ha.ne'⟩
  let f : Fin a → ℕ := fun i => l.get (Fin.castLE hlen i)
  have h := (MetaMathlibExt.consecutive_constant_eq_card (ZMod a)).1.2
  rw [ZMod.card] at h
  obtain ⟨i, j, hij, weights, hweights, hzero⟩ := h (fun i => (f i : ZMod a))
  let I := Icc i j
  let w := I.val.map f
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · let e : Fin a ↪ Fin l.length := ⟨Fin.castLE hlen, Fin.castLE_injective hlen⟩
    have he : I.map e ⊆ (univ : Finset (Fin l.length)) := subset_univ _
    have hmap := Multiset.map_le_map (f := l.get) (Finset.val_le_iff.mpr he)
    simpa [w, f, e, Finset.map_val, Finset.val_univ_fin, List.map_get_finRange] using hmap
  · have hI : I.Nonempty := ⟨i, mem_Icc.mpr ⟨le_rfl, hij⟩⟩
    simpa [w] using hI.card_pos
  · simpa [w] using I.card_le_univ
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    have hsum : ∑ t ∈ I, (f t : ZMod a) = 0 := by
      rw [← hzero]
      apply Finset.sum_congr rfl
      intro t ht
      have ht' : weights t = 1 := Set.mem_singleton_iff.mp (hweights t ht)
      rw [ht', one_zsmul]
    rw [Nat.cast_multiset_sum]
    change (((I.val.map f).map fun x : ℕ => (x : ZMod a)).sum) = 0
    rw [Multiset.map_map]
    exact hsum

private theorem exists_half_sum {a k m : ℕ} (ha : 0 < a) (hk : 0 < k)
    {s : Multiset ℕ} (hs : s.sum = 2 * m) (hparts : ∀ x ∈ s, 0 < x ∧ x ≤ k)
    (ham : a ∣ m) (hcount : k - 1 ≤ s.count a) (hreserve : (k - 1) * a ≤ m) :
    ∃ t ≤ s, t.sum = m := by
  let reserve := Multiset.replicate (k - 1) a
  have hr : reserve ≤ s := Multiset.le_count_iff_replicate_le.mp hcount
  let rest := s - reserve
  have hrest : rest + reserve = s := tsub_add_cancel_of_le hr
  have hrest_sum : m ≤ rest.sum := by
    have h := congrArg Multiset.sum hrest
    rw [Multiset.sum_add, hs] at h
    have hrsum : reserve.sum = (k - 1) * a := by simp [reserve]
    omega
  -- Maximize the multiple of `a` obtained without using the reserved copies.
  let candidates := rest.powerset.toFinset.filter (fun t => a ∣ t.sum ∧ t.sum ≤ m)
  have hmem (t : Multiset ℕ) : t ∈ candidates ↔ t ≤ rest ∧ a ∣ t.sum ∧ t.sum ≤ m := by
    simp [candidates]
  obtain ⟨t, ht, hmax⟩ :=
    Finset.exists_max_image candidates Multiset.sum ⟨0, (hmem 0).mpr (by simp)⟩
  obtain ⟨htle, htdvd, htm⟩ := (hmem t).mp ht
  obtain ⟨d, hd⟩ := Nat.dvd_sub ham htdvd
  have hm : m = t.sum + a * d := by omega
  have hdle : d ≤ k - 1 := by
    by_contra! hdk
    have hkd : k ≤ d := by omega
    let u := rest - t
    have hu : t + u = rest := add_tsub_cancel_of_le htle
    have hule : u ≤ s := (tsub_le_self).trans (tsub_le_self)
    have huparts : ∀ x ∈ u, 0 < x ∧ x ≤ k := fun x hx =>
      hparts x (Multiset.mem_of_le hule hx)
    have husum : a * k ≤ u.sum := by
      have h := congrArg Multiset.sum hu
      rw [Multiset.sum_add] at h
      have hmul := Nat.mul_le_mul_left a hkd
      omega
    have hcard : a ≤ u.card := by
      by_contra! hlt
      have h := Multiset.sum_le_card_nsmul u k (fun x hx => (huparts x hx).2)
      exact (Nat.mul_lt_mul_of_pos_right hlt hk).not_ge
        (husum.trans (by simpa [nsmul_eq_mul] using h))
    obtain ⟨w, hw, hwpos, hwcard, hwdvd⟩ := exists_small_dvd_sum ha hcard
    have hwle : w.sum ≤ a * d := calc
      w.sum ≤ w.card * k := by
        simpa [nsmul_eq_mul] using
          Multiset.sum_le_card_nsmul w k (fun x hx => (huparts x (Multiset.mem_of_le hw hx)).2)
      _ ≤ a * k := Nat.mul_le_mul_right _ hwcard
      _ ≤ a * d := Nat.mul_le_mul_left _ hkd
    have hwpos' : 0 < w.sum := by
      obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp hwpos
      exact (huparts x (Multiset.mem_of_le hw hx)).1.trans_le (Multiset.le_sum_of_mem hx)
    have ht' : t + w ∈ candidates := (hmem _).mpr
      ⟨(Multiset.add_le_add_left hw).trans_eq hu, by
        rw [Multiset.sum_add]
        exact dvd_add htdvd hwdvd, by rw [Multiset.sum_add, hm]; omega⟩
    have h := hmax _ ht'
    rw [Multiset.sum_add] at h
    omega
  refine ⟨t + Multiset.replicate d a, ?_, ?_⟩
  · exact (add_le_add htle ((Multiset.replicate_le_replicate a).mpr hdle)).trans_eq hrest
  · simpa [Multiset.sum_add, nsmul_eq_mul, mul_comm d a] using hm.symm

-- A partition formed by copies of `a` and one remainder forces `a` to divide the half-sum.
private theorem dvd_half_of_all_balanceable {n k a : ℕ} (ha : 0 < a) (hak : a ≤ k)
    (h : ∀ p : n.Partition, Bounded k p → Balanceable p) :
    ∃ m, n = 2 * m ∧ a ∣ m := by
  let r := n % a
  let copies := Multiset.replicate (n / a) a
  let parts := r ::ₘ copies
  have hsum : parts.sum = n := by
    simpa [parts, r, copies, nsmul_eq_mul, mul_comm (n / a)] using Nat.mod_add_div n a
  let p := Nat.Partition.ofSums n parts hsum
  have hr : r < a := Nat.mod_lt _ ha
  have hp : Bounded k p := by
    intro x hx
    change x ∈ parts.filter (· ≠ 0) at hx
    have hx' := (Multiset.mem_filter.mp hx).1
    rcases Multiset.mem_cons.mp hx' with heq | hcopies
    · exact heq ▸ hr.le.trans hak
    · have heq := Multiset.eq_of_mem_replicate hcopies
      exact heq ▸ hak
  obtain ⟨s, t, hst, heq⟩ := h p hp
  have hle : s + t ≤ parts := hst ▸ Multiset.filter_le _ _
  have hnot : r ∉ s ∨ r ∉ t := by
    by_contra! hb
    have hcr : parts.count r = 1 := by
      simp [parts, copies, Multiset.count_replicate, hr.ne']
    have hc := Multiset.count_le_of_le r hle
    rw [Multiset.count_add, hcr] at hc
    have hs := Multiset.count_pos.mpr hb.1
    have ht := Multiset.count_pos.mpr hb.2
    omega
  have hdvd (v : Multiset ℕ) (hv : v ≤ parts) (hvr : r ∉ v) : a ∣ v.sum := by
    have hv' : v ≤ copies := (Multiset.le_cons_of_notMem hvr).mp hv
    obtain ⟨i, -, hi⟩ := Multiset.le_replicate_iff.mp hv'
    rw [hi, Multiset.sum_replicate, nsmul_eq_mul]
    exact Nat.dvd_mul_left _ _
  refine ⟨s.sum, ?_, ?_⟩
  · have ht := congrArg Multiset.sum hst
    rw [Multiset.sum_add, p.parts_sum, ← heq] at ht
    omega
  · rcases hnot with hs | ht
    · exact hdvd s ((Multiset.le_add_right _ _).trans hle) hs
    · rw [heq]
      exact hdvd t ((Multiset.le_add_left _ _).trans hle) ht

set_option linter.dupNamespace false in
/--
**Smallest size forcing bounded partitions to be balanceable.** For every integer $k \ge 1$, the
smallest positive integer $n$ such that every $k$-bounded partition of $n$ is balanceable is
$2 \operatorname{lcm}(1, 2, \ldots, k)$.

Source: https://projecteuler.net/problem=772 Via leanprover/lean-eval@38361be,
problem `balanceable_bounded_partitions`.
-/
public theorem minimal_balanceable_of_bounded (k : ℕ) (hk : 0 < k) :
    Minimal (fun n => 0 < n ∧ ∀ p : n.Partition, Bounded k p → Balanceable p)
      (2 * (Finset.Icc 1 k).lcm id) := by
  let L := (Icc 1 k).lcm id
  refine ⟨⟨Nat.mul_pos (by decide) (interval_lcm_pos k), ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨a, ha, hcount⟩ := exists_many_copies p hp
    obtain ⟨ha₁, ha₂⟩ := mem_Icc.mp ha
    obtain ⟨t, ht, hsum⟩ := exists_half_sum ha₁ hk p.parts_sum
      (fun x hx => ⟨p.parts_pos hx, hp x hx⟩) (dvd_interval_lcm ha₁ ha₂)
      hcount (reserve_le_lcm ha₂)
    have hsplit : t + (p.parts - t) = p.parts := add_tsub_cancel_of_le ht
    refine ⟨t, p.parts - t, hsplit, ?_⟩
    have hs := congrArg Multiset.sum hsplit
    rw [Multiset.sum_add, p.parts_sum, hsum] at hs
    omega
  · intro n hn _
    obtain ⟨m, hm, -⟩ := dvd_half_of_all_balanceable (a := 1) (by decide) hk hn.2
    have hdvd : L ∣ m := by
      refine Finset.lcm_dvd fun a ha => ?_
      obtain ⟨ha₁, ha₂⟩ := mem_Icc.mp ha
      obtain ⟨m', hm', h⟩ := dvd_half_of_all_balanceable ha₁ ha₂ hn.2
      rwa [show m = m' by omega]
    have hmpos : 0 < m := by have := hn.1; omega
    rw [hm]
    exact Nat.mul_le_mul_left _ (Nat.le_of_dvd hmpos hdvd)

end Combinatorics

end MathlibExt.Combinatorics.BalanceableBoundedPartitionsWanted
