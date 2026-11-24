/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Fintype.BigOperators

/-!
# Minimal excludants of overpartitions

The sum of the least missing non-overlined parts of the overpartitions of a positive integer
is odd exactly at triangular numbers.
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

/--
**Three-colored distinct-part partitions.** For a natural number $n$, $D_3(n)$ is the number of
triples $(A, B, C)$ of subsets of $\{1, \dots, n\}$ such that the sum of the elements of $A$, the
sum of the elements of $B$ and the sum of the elements of $C$ add up to $n$. Here $A$, $B$, $C$
are the parts of the three colors of a partition of $n$ whose parts of each color are distinct.

A size may occur in several colors but at most once in each, as in the product
$\prod_{m \ge 1} (1 + q^m)^3$.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public def D3 (n : ℕ) : ℕ :=
  ((((Finset.Icc 1 n).powerset.product (Finset.Icc 1 n).powerset).product
    (Finset.Icc 1 n).powerset).filter fun p =>
      p.1.1.sum id + p.1.2.sum id + p.2.sum id = n).card

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

/--
**Three-colored distinct-part partitions of $0$.** The number $D_3(0)$ of partitions of $0$ into
parts of three colors, with the parts of each color distinct, equals $1$: the empty partition is
the only one.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public theorem D3_zero : D3 0 = 1 := by
  decide

/--
**Three-colored distinct-part partitions of $1$.** The number $D_3(1)$ of partitions of $1$ into
parts of three colors, with the parts of each color distinct, equals $3$: the single part $1$
takes one of the three colors.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public theorem D3_one : D3 1 = 3 := by
  decide

/--
**Three-colored distinct-part partitions of $2$.** The number $D_3(2)$ of partitions of $2$ into
parts of three colors, with the parts of each color distinct, equals $6$: the single part $2$ in
one of three colors, or two parts $1$ in two different colors.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public theorem D3_two : D3 2 = 6 := by
  decide

namespace sigmaMexOverpartition_parity

open Finset

private abbrev staircase (k : ℕ) := (Icc 1 k).val

private theorem staircase_sum_succ (k : ℕ) :
    (staircase (k + 1)).sum = (staircase k).sum + (k + 1) := by
  simpa only [staircase, sum_val, id_eq] using sum_Icc_succ_top (a := 1) (b := k) (by omega) id

private theorem staircase_sum (k : ℕ) : (staircase k).sum = k * (k + 1) / 2 := by
  have h : (staircase k).sum * 2 = k * (k + 1) := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [staircase_sum_succ, Nat.add_mul, ih]
      simp [Nat.succ_mul, Nat.mul_succ]
      omega
  rw [← h, Nat.mul_div_cancel _ (by decide : 0 < 2)]

private theorem staircase_strictMono : StrictMono (fun k => (staircase k).sum) :=
  strictMono_nat_of_lt_succ fun k => by rw [staircase_sum_succ]; omega

private theorem overlines_le {n : ℕ} (O : Nat.Overpartition n) :
    O.overlines.val ≤ O.toPartition.parts :=
  (Multiset.le_iff_subset O.overlines.nodup).2 fun _ ha =>
    Multiset.mem_toFinset.mp (O.overlines_subset ha)

-- The mex exceeds k precisely when the staircase can be removed while retaining the overlines.
private theorem lt_gap_iff {n k : ℕ} (O : Nat.Overpartition n) :
    k < leastGapOverpartition 1 O ↔ O.overlines.val + staircase k ≤ O.toPartition.parts := by
  rw [leastGapOverpartition, dite_eq_right (by decide : 1 ≠ 0), Nat.lt_find_iff,
    Multiset.le_iff_count]
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup O.overlines.nodup,
    Multiset.count_eq_of_nodup (Icc 1 k).nodup, Finset.mem_val, mem_Icc, nonOverlinedCount]
  constructor
  · intro h a
    by_cases ha : 1 ≤ a ∧ a ≤ k
    · have hpos := h a ha.2
      rw [ite_eq_left ha]
      by_cases ho : a ∈ O.overlines <;> simp only [ho, ite_true, ite_false] at hpos ⊢ <;> omega
    · have := Multiset.count_le_of_le a (overlines_le O)
      simpa [ha, Multiset.count_eq_of_nodup O.overlines.nodup] using this
  · intro h a hak ⟨ha, hcount⟩
    specialize h a
    split_ifs at * <;> omega

private theorem staircase_le {n k : ℕ} {O : Nat.Overpartition n}
    (h : k < leastGapOverpartition 1 O) : staircase k ≤ O.toPartition.parts :=
  le_add_self.trans ((lt_gap_iff O).mp h)

private theorem remainder_sum {n k : ℕ} {O : Nat.Overpartition n}
    (h : k < leastGapOverpartition 1 O) :
    (O.toPartition.parts - staircase k).sum + (staircase k).sum = n := by
  rw [← Multiset.sum_add, Multiset.sub_add_cancel (staircase_le h), O.toPartition.parts_sum]

private def removeStaircase {n k m : ℕ} (hn : m + (staircase k).sum = n) :
    {O : Nat.Overpartition n // k < leastGapOverpartition 1 O} ≃ Nat.Overpartition m where
  toFun x := {
    toPartition := {
      parts := x.val.toPartition.parts - staircase k
      parts_pos := fun ha => x.val.toPartition.parts_pos
        (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)
      parts_sum := Nat.add_right_cancel ((remainder_sum x.property).trans hn.symm) }
    overlines := x.val.overlines
    overlines_subset := by
      intro a ha
      apply Multiset.mem_toFinset.mpr
      apply Multiset.mem_sub.mpr
      have h := Multiset.count_le_of_le a ((lt_gap_iff x.val).mp x.property)
      rw [Multiset.count_add, Multiset.count_eq_one_of_mem x.val.overlines.nodup ha] at h
      omega }
  invFun O := ⟨{
    toPartition := {
      parts := O.toPartition.parts + staircase k
      parts_pos := by
        intro a ha
        rcases Multiset.mem_add.mp ha with h | h
        · exact O.toPartition.parts_pos h
        · exact (mem_Icc.mp (show a ∈ Icc 1 k from h)).1
      parts_sum := by rw [Multiset.sum_add, O.toPartition.parts_sum, hn] }
    overlines := O.overlines
    overlines_subset := fun a ha => Multiset.mem_toFinset.mpr
      (Multiset.mem_add.mpr (.inl (O.isOverlined_mem_parts ha))) },
    (lt_gap_iff _).mpr (add_le_add_left (overlines_le O) _)⟩
  left_inv x := Subtype.ext (Nat.Overpartition.ext
    (Nat.Partition.ext (Multiset.sub_add_cancel (staircase_le x.property))) rfl)
  right_inv _ := Nat.Overpartition.ext (Nat.Partition.ext Multiset.add_sub_cancel_right) rfl

private theorem count_even {n : ℕ} (hn : 0 < n) : overpartitionCount n ≡ 0 [MOD 2] := by
  unfold overpartitionCount Nat.Overpartition.instFintype
  rw [Fintype.ofEquiv_card, Fintype.card_sigma]
  apply Nat.ModEq.sum_zero
  intro p _
  rw [Fintype.card_coe, card_powerset]
  apply Nat.modEq_zero_iff_dvd.mpr
  apply dvd_pow_self
  intro h
  have hempty : p.parts = 0 := by simpa using card_eq_zero.mp h
  have := p.parts_sum
  simp [hempty] at this
  omega

private abbrev tailCount (n k : ℕ) :=
  Fintype.card {O : Nat.Overpartition n // k < leastGapOverpartition 1 O}

private theorem tail_parity (n k : ℕ) :
    tailCount n k ≡ (if n = (staircase k).sum then 1 else 0) [MOD 2] := by
  by_cases h : (staircase k).sum ≤ n
  · rw [tailCount, Fintype.card_congr (removeStaircase (Nat.sub_add_cancel h))]
    change overpartitionCount (n - (staircase k).sum) ≡ _ [MOD 2]
    split_ifs with heq
    · rw [heq, Nat.sub_self, overpartitionCount_zero]
    · exact count_even (by omega)
  · have empty : IsEmpty {O : Nat.Overpartition n // k < leastGapOverpartition 1 O} := by
      refine ⟨fun x => ?_⟩
      have := remainder_sum x.property
      omega
    rw [ite_eq_right (show n ≠ (staircase k).sum by omega), tailCount, Fintype.card_eq_zero]

private theorem sum_tails (n : ℕ) :
    sigmaMexOverpartition 1 n = ∑ k ∈ range (n + 1), tailCount n k := by
  classical
  have hbound (O : Nat.Overpartition n) : leastGapOverpartition 1 O ≤ n + 1 := by
    by_contra! h
    have hs := remainder_sum h
    have hle : n + 1 ≤ (staircase (n + 1)).sum := staircase_strictMono.id_le _
    omega
  have hgap (O : Nat.Overpartition n) : leastGapOverpartition 1 O =
      ∑ k ∈ range (n + 1), if k < leastGapOverpartition 1 O then 1 else 0 := by
    simpa only [mem_range, card_range] using card_eq_sum_ite
      (range_mono (hbound O))
  unfold sigmaMexOverpartition
  conv_lhs => enter [2, O]; rw [hgap O]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  simp [tailCount, Fintype.card_subtype]

end sigmaMexOverpartition_parity

open sigmaMexOverpartition_parity Finset in
/--
**Parity of the overpartition mex sum.** For an overpartition $\pi$, let
$\overline{\mathrm{mex}}(\pi)$ be the least positive integer that does not occur among the
non-overlined parts of $\pi$, and let $\sigma\overline{\mathrm{mex}}(n)$ be the sum of
$\overline{\mathrm{mex}}(\pi)$ over all overpartitions $\pi$ of $n$. For every positive integer
$n$, $\sigma\overline{\mathrm{mex}}(n)$ is odd if $n = j(j+1)/2$ is a triangular number for some
natural number $j$, and even otherwise.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 4.
-/
public theorem sigmaMexOverpartition_parity (n : ℕ) (hn : 0 < n) :
    ((∃ j : ℕ, n = (j * (j + 1) / 2)) →
      Nat.ModEq 2 (sigmaMexOverpartition 1 n) 1) ∧
    ((¬∃ j : ℕ, n = (j * (j + 1) / 2)) →
      Nat.ModEq 2 (sigmaMexOverpartition 1 n) 0) := by
  have hzero : tailCount n 0 ≡ 0 [MOD 2] := by
    simpa only [show (staircase 0).sum = 0 by decide, ite_eq_right hn.ne'] using tail_parity n 0
  have hsum : sigmaMexOverpartition 1 n ≡
      ∑ k ∈ range n, (if n = (staircase (k + 1)).sum then 1 else 0) [MOD 2] := by
    rw [sum_tails, sum_range_succ']
    simpa only [Nat.add_zero] using
      (Nat.ModEq.sum (s := range n) (fun k _ => tail_parity n (k + 1))).add hzero
  simp_rw [← staircase_sum]
  constructor
  · rintro ⟨j | j, hj⟩
    · have : n = 0 := hj.trans (by decide)
      omega
    · have hmem : j ∈ range n := mem_range.mpr (hj ▸ staircase_strictMono.id_le (j + 1))
      have heq (k : ℕ) : n = (staircase (k + 1)).sum ↔ j = k := by
        rw [hj, staircase_strictMono.injective.eq_iff, Nat.add_right_cancel_iff]
      simpa only [heq, sum_ite_eq, hmem, ite_true] using hsum
  · intro h
    have hne (k : ℕ) : n ≠ (staircase (k + 1)).sum := fun hk => h ⟨k + 1, hk⟩
    simpa only [ite_eq_right (hne _), sum_const_zero] using hsum

end

end MetaMathlibExt
