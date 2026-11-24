/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators

/-!
# The sum of least gaps over overpartitions

For positive `r`, summing the least `r`-gaps of the overpartitions of `n` gives the sum of
overpartition counts at shifts by `r` times the triangular numbers. Removing a staircase of
non-overlined parts gives the bijection for each shift.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of overpartitions.** For a natural number $n$, $\overline{p}(n)$ is the number of
overpartitions of $n$, that is, of pairs consisting of a partition $p$ of $n$ and a set of
overlined part sizes, each of which occurs as a part of $p$. For example, $\overline{p}(3) = 8$.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Section 1. -/
public noncomputable def overpartitionCount (n : ℕ) : ℕ :=
  Fintype.card (Nat.Overpartition n)

/--
**Number of non-overlined copies of a part size.** For an overpartition $O$ of $n$ and a natural
number $a$, the number of non-overlined parts of size $a$ in $O$ is the multiplicity of $a$ in the
underlying partition of $O$, minus $1$ if $a$ is overlined in $O$ and minus $0$ otherwise.

This matches the convention that only the first occurrence of a part size may be overlined: an
overpartition records each overlined size once.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `mex̄_r`.
-/
public def nonOverlinedCount {n : ℕ} (O : Nat.Overpartition n) (a : ℕ) : ℕ :=
  O.toPartition.parts.count a - if a ∈ O.overlines then 1 else 0

/--
**Minimal excludant of an overpartition with a multiplicity bound.** For natural numbers $r \ge 1$
and $n$ and an overpartition $O$ of $n$, $\overline{\mathrm{mex}}_r(O)$ is the least positive
integer $k$ that occurs fewer than $r$ times among the non-overlined parts of $O$. Such a $k$
exists, since $n + 1$ is not a part of $O$. For $r = 0$, which the paper does not use, the value
is $0$ by convention.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `mex̄_r`.
-/
public def leastGapOverpartition (r : ℕ) {n : ℕ} (O : Nat.Overpartition n) : ℕ :=
  if hr : r = 0 then 0
  else
    Nat.find (show ∃ k : ℕ,
        1 ≤ k ∧ nonOverlinedCount O k < r from by
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have hnotmem : n + 1 ∉ O.toPartition.parts := by
        intro hmem
        have hle : n + 1 ≤ O.toPartition.parts.sum :=
          Multiset.le_sum_of_mem hmem
        rw [O.toPartition.parts_sum] at hle
        omega
      have hcount : O.toPartition.parts.count (n + 1) = 0 :=
        Multiset.count_eq_zero.mpr hnotmem
      exact ⟨n + 1, Nat.zero_lt_succ n, by
        simp [nonOverlinedCount, hcount, hrpos]⟩)

/-- **Sums of minimal excludants over overpartitions.** For natural numbers $r$ and $n$,
$\sigma_r\overline{\mathrm{mex}}(n)$ is the sum, over all overpartitions $\pi$ of $n$, of
$\overline{\mathrm{mex}}_r(\pi)$, the least positive integer occurring fewer than $r$ times
among the non-overlined parts of $\pi$; for $r = 0$ the value $\overline{\mathrm{mex}}_0(\pi)$
is $0$ by convention, so $\sigma_0\overline{\mathrm{mex}}(n) = 0$. We write
$\sigma\overline{\mathrm{mex}}(n) = \sigma_1\overline{\mathrm{mex}}(n)$.

By direct enumeration, $\sigma\overline{\mathrm{mex}}(n) = 1, 3, 6, 13, 24$ for $n = 0, \dots, 4$,
and $\sigma_2\overline{\mathrm{mex}}(2) = 5$.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definitions of `σmex̄` and `σ_r mex̄`. -/
public noncomputable def sigmaMexOverpartition (r n : ℕ) : ℕ :=
  ∑ O : Nat.Overpartition n, leastGapOverpartition r O

/-- **The number of overpartitions of zero.** The number $\overline{p}(0)$ of overpartitions of
$0$ equals $1$: the empty overpartition is the only one.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Section 1 (`p̄(0) = 1`). -/
public theorem overpartitionCount_zero : overpartitionCount 0 = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨Nat.Overpartition.ofPartition default, fun _ =>
    Nat.Overpartition.eq_of_zero _ _⟩

namespace sigmaMexOverpartition_eq_sum_shifted_count

open Finset

private abbrev staircase (r k : ℕ) : Multiset ℕ := r • (Icc 1 k).val

private theorem staircase_sum (r k : ℕ) : (staircase r k).sum = r * (k * (k + 1) / 2) := by
  rw [staircase, Multiset.sum_nsmul, smul_eq_mul, sum_val]
  congr 1
  have h := sum_range_eq_add_Ico id (Nat.zero_lt_succ k)
  simpa [sum_range_id, Ico_add_one_right_eq_Icc, Nat.mul_comm] using h.symm

private theorem overlines_le {n : ℕ} (O : Nat.Overpartition n) :
    O.overlines.val ≤ O.toPartition.parts :=
  (Multiset.le_iff_subset O.overlines.nodup).2 fun _ ha =>
    Multiset.mem_toFinset.mp (O.overlines_subset ha)

-- Reserve one copy of each overlined size before removing the repeated staircase.
private theorem lt_gap_iff {n r k : ℕ} (hr : 1 ≤ r) (O : Nat.Overpartition n) :
    k < leastGapOverpartition r O ↔ O.overlines.val + staircase r k ≤ O.toPartition.parts := by
  rw [leastGapOverpartition, dite_eq_right (by omega : r ≠ 0), Nat.lt_find_iff,
    Multiset.le_iff_count]
  simp only [staircase, Multiset.count_add, Multiset.count_nsmul,
    Multiset.count_eq_of_nodup O.overlines.nodup, Multiset.count_eq_of_nodup (Icc 1 k).nodup,
    Finset.mem_val, mem_Icc, nonOverlinedCount]
  constructor
  · intro h a
    by_cases ha : 1 ≤ a ∧ a ≤ k
    · have hpos := h a ha.2
      simp only [ite_eq_left ha, Nat.mul_one]
      split_ifs at * <;> omega
    · have := Multiset.count_le_of_le a (overlines_le O)
      simpa [ha, Multiset.count_eq_of_nodup O.overlines.nodup] using this
  · intro h a hak ⟨ha, hcount⟩
    specialize h a
    simp only [ite_eq_left (And.intro ha hak), Nat.mul_one] at h
    split_ifs at * <;> omega

private theorem staircase_le {n r k : ℕ} (hr : 1 ≤ r) {O : Nat.Overpartition n}
    (h : k < leastGapOverpartition r O) : staircase r k ≤ O.toPartition.parts :=
  le_add_self.trans ((lt_gap_iff hr O).mp h)

private theorem remainder_sum {n r k : ℕ} (hr : 1 ≤ r) {O : Nat.Overpartition n}
    (h : k < leastGapOverpartition r O) :
    (O.toPartition.parts - staircase r k).sum + (staircase r k).sum = n := by
  rw [← Multiset.sum_add, Multiset.sub_add_cancel (staircase_le hr h), O.toPartition.parts_sum]

private def removeStaircase {n r k m : ℕ} (hr : 1 ≤ r) (hn : m + (staircase r k).sum = n) :
    {O : Nat.Overpartition n // k < leastGapOverpartition r O} ≃ Nat.Overpartition m where
  toFun x := {
    toPartition := {
      parts := x.val.toPartition.parts - staircase r k
      parts_pos := fun ha => x.val.toPartition.parts_pos
        (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)
      parts_sum := Nat.add_right_cancel ((remainder_sum hr x.property).trans hn.symm) }
    overlines := x.val.overlines
    overlines_subset := by
      intro a ha
      apply Multiset.mem_toFinset.mpr
      apply Multiset.mem_sub.mpr
      have h := Multiset.count_le_of_le a ((lt_gap_iff hr x.val).mp x.property)
      rw [Multiset.count_add, Multiset.count_eq_one_of_mem x.val.overlines.nodup ha] at h
      omega }
  invFun O := ⟨{
    toPartition := {
      parts := O.toPartition.parts + staircase r k
      parts_pos := by
        intro a ha
        rcases Multiset.mem_add.mp ha with h | h
        · exact O.toPartition.parts_pos h
        · exact (mem_Icc.mp (show a ∈ Icc 1 k from Multiset.mem_of_mem_nsmul h)).1
      parts_sum := by rw [Multiset.sum_add, O.toPartition.parts_sum, hn] }
    overlines := O.overlines
    overlines_subset := fun a ha => Multiset.mem_toFinset.mpr
      (Multiset.mem_add.mpr (.inl (O.isOverlined_mem_parts ha))) },
    (lt_gap_iff hr _).mpr (add_le_add_left (overlines_le O) _)⟩
  left_inv x := Subtype.ext (Nat.Overpartition.ext
    (Nat.Partition.ext (Multiset.sub_add_cancel (staircase_le hr x.property))) rfl)
  right_inv _ := Nat.Overpartition.ext (Nat.Partition.ext Multiset.add_sub_cancel_right) rfl

private abbrev tailCount (n r k : ℕ) :=
  Fintype.card {O : Nat.Overpartition n // k < leastGapOverpartition r O}

private theorem tailCount_eq (n r k : ℕ) (hr : 1 ≤ r) :
    tailCount n r k = if (staircase r k).sum ≤ n then
      overpartitionCount (n - (staircase r k).sum) else 0 := by
  split_ifs with h
  · exact Fintype.card_congr (removeStaircase hr (Nat.sub_add_cancel h))
  · have : IsEmpty {O : Nat.Overpartition n // k < leastGapOverpartition r O} := by
      refine ⟨fun x => ?_⟩
      have := remainder_sum hr x.property
      omega
    exact Fintype.card_eq_zero

private theorem sum_tails (n r : ℕ) (hr : 1 ≤ r) :
    sigmaMexOverpartition r n = ∑ k ∈ range (n + 1), tailCount n r k := by
  classical
  have hbound (O : Nat.Overpartition n) : leastGapOverpartition r O ≤ n + 1 := by
    rw [leastGapOverpartition, dite_eq_right (by omega : r ≠ 0)]
    apply Nat.find_min'
    refine ⟨by omega, ?_⟩
    have hnot : n + 1 ∉ O.toPartition.parts := fun h => by
      have := Multiset.le_sum_of_mem h
      rw [O.toPartition.parts_sum] at this
      omega
    simp [nonOverlinedCount, Multiset.count_eq_zero.mpr hnot, show 0 < r from hr]
  have hgap (O : Nat.Overpartition n) : leastGapOverpartition r O =
      ∑ k ∈ range (n + 1), if k < leastGapOverpartition r O then 1 else 0 := by
    simpa only [mem_range, card_range] using card_eq_sum_ite
      (range_mono (hbound O))
  unfold sigmaMexOverpartition
  conv_lhs => enter [2, O]; rw [hgap O]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  simp [tailCount, Fintype.card_subtype]

end sigmaMexOverpartition_eq_sum_shifted_count

open sigmaMexOverpartition_eq_sum_shifted_count Finset in
/--
**The r-mex sum of overpartitions as a sum of overpartition counts.** Let $n$ and $r$ be
natural numbers with $r \ge 1$, let $\overline{p}(m)$ be the number of overpartitions of $m$, let
$T_k = k(k+1)/2$ be the $k$-th triangular number, and let $\sigma_r\overline{\mathrm{mex}}(n)$ be
the sum over all overpartitions $\pi$ of $n$ of $\overline{\mathrm{mex}}_r(\pi)$, the least
positive integer occurring fewer than $r$ times among the non-overlined parts of $\pi$. Then
$$\sigma_r\overline{\mathrm{mex}}(n) = \sum_{k \ge 0,\; rT_k \le n} \overline{p}(n - rT_k).$$

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Proposition 10.
-/
public theorem sigmaMexOverpartition_eq_sum_shifted_count
    (n r : ℕ) (hr : 1 ≤ r) :
    (∑ k ∈ (Finset.range (n + 1)).filter
      (fun k => r * (k * (k + 1) / 2) ≤ n),
      overpartitionCount (n - r * (k * (k + 1) / 2))) =
      sigmaMexOverpartition r n := by
  rw [sum_tails n r hr, sum_filter]
  exact sum_congr rfl fun k _ => by rw [tailCount_eq n r k hr, staircase_sum]

end

end MetaMathlibExt
