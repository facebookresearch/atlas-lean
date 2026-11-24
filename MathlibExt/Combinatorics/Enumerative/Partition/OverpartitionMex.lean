/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import MathlibExt.Combinatorics.Enumerative.Partition.OverpartitionMexSum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Fintype.BigOperators

/-!
# Minimal excludants of overpartitions

The sum of the least missing non-overlined parts of the overpartitions of a positive integer
is odd exactly at triangular numbers.
-/

namespace MetaMathlibExt

@[expose] public section

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
  let triangular (k : ℕ) := k * (k + 1) / 2
  have triangular_strictMono : StrictMono triangular := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h : triangular (k + 1) = triangular k + (k + 1) := by
      simpa [triangular, Nat.mul_comm] using Nat.triangle_succ (k + 1)
    omega
  have shifted_count_parity (m : ℕ) :
      (if m ≤ n then overpartitionCount (n - m) else 0) ≡ (if n = m then 1 else 0) [MOD 2] := by
    split_ifs with h heq heq
    · rw [heq, Nat.sub_self, overpartitionCount_zero]
    · exact count_even (by omega)
    · omega
    · rfl
  have hsum : sigmaMexOverpartition 1 n ≡
      ∑ k ∈ range (n + 1), (if n = triangular k then 1 else 0) [MOD 2] := by
    rw [← sigmaMexOverpartition_eq_sum_shifted_count n 1 le_rfl, sum_filter]
    simp only [one_mul]
    exact Nat.ModEq.sum fun k _ => shifted_count_parity (triangular k)
  constructor
  · rintro ⟨j | j, hj⟩
    · have : n = 0 := hj.trans (by decide)
      omega
    · have hmem : j + 1 ∈ range (n + 1) := mem_range.mpr
        (Nat.lt_succ_of_le (hj ▸ triangular_strictMono.id_le (j + 1)))
      have heq (k : ℕ) : n = triangular k ↔ j + 1 = k := by
        rw [hj, triangular_strictMono.injective.eq_iff]
      simpa only [heq, sum_ite_eq, hmem, ite_true] using hsum
  · intro h
    have hne (k : ℕ) : n ≠ triangular k := fun hk => h ⟨k, hk⟩
    simpa only [ite_eq_right (hne _), sum_const_zero] using hsum

end

end MetaMathlibExt
