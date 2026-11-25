/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.NumberTheory.FloorQuotientOddCount
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The floor parity count through the divisor summatory function

Count the divisor pairs by their product or by their first factor. The alternating
floor sum then subtracts twice the contribution of the even denominators.
-/

namespace MetaMathlibExt

open Finset

private theorem filter_dvd_Icc (n : ℕ) {d : ℕ} (hd : 0 < d) :
    (Icc 1 n).filter (d ∣ ·) =
      (Icc 1 (n / d)).map ⟨fun k => d * k, fun _ _ h => Nat.eq_of_mul_eq_mul_left hd h⟩ := by
  ext m
  simp only [mem_filter, mem_map, mem_Icc]
  constructor
  · rintro ⟨⟨hm, hmn⟩, k, rfl⟩
    refine ⟨k, ⟨?_, (Nat.le_div_iff_mul_le hd).2 (by simpa [Nat.mul_comm] using hmn)⟩, rfl⟩
    by_contra! hk
    obtain rfl : k = 0 := by omega
    simp at hm
  · rintro ⟨k, ⟨hk, hkn⟩, rfl⟩
    change (1 ≤ d * k ∧ d * k ≤ n) ∧ d ∣ d * k
    refine ⟨⟨Nat.mul_pos hd hk, ?_⟩, dvd_mul_right d k⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).1 hkn

private theorem sum_divisors_card_eq_sum_div (n : ℕ) :
    (∑ m ∈ Icc 1 n, (m.divisors.card : ℤ)) = ∑ d ∈ Icc 1 n, ((n / d : ℕ) : ℤ) := by
  calc
    (∑ m ∈ Icc 1 n, (m.divisors.card : ℤ)) =
        ∑ m ∈ Icc 1 n, ∑ d ∈ Icc 1 n, (if d ∣ m then 1 else 0 : ℤ) := by
      refine sum_congr rfl fun m hm => ?_
      obtain ⟨hm₀, hmn⟩ := mem_Icc.mp hm
      have hdivisors : (Icc 1 n).filter (· ∣ m) = m.divisors := by
        ext d
        refine ⟨fun h => Nat.mem_divisors.mpr ⟨(mem_filter.mp h).2, by omega⟩, fun h => ?_⟩
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors h,
          (Nat.divisor_le h).trans hmn⟩, Nat.dvd_of_mem_divisors h⟩
      rw [sum_boole, hdivisors]
    _ = ∑ d ∈ Icc 1 n, ∑ m ∈ Icc 1 n, (if d ∣ m then 1 else 0 : ℤ) := sum_comm
    _ = _ := by
      refine sum_congr rfl fun d hd => ?_
      rw [sum_boole, filter_dvd_Icc n (mem_Icc.mp hd).1, card_map, Nat.card_Icc]
      simp

private theorem sum_even_floor_div (n : ℕ) :
    (∑ d ∈ (Icc 1 n).filter (Even ·), ((n / d : ℕ) : ℤ)) =
      ∑ k ∈ Icc 1 (n / 2), (((n / 2) / k : ℕ) : ℤ) := by
  simp only [even_iff_two_dvd]
  rw [filter_dvd_Icc n (by decide : 0 < (2 : ℕ)), sum_map]
  refine sum_congr rfl fun k _ => ?_
  change ((n / (2 * k) : ℕ) : ℤ) = (((n / 2) / k : ℕ) : ℤ)
  rw [Nat.div_div_eq_div_mul]

/-- **The floor parity count through the divisor summatory function.** Let $\tau(m)$ be the
number of positive divisors of $m$, let $D(x) = \sum_{1 \le m \le x} \tau(m)$, and let
$\mathcal{F}_n$ be the number of integers $k$ with $1 \le k \le n$ for which
$\lfloor n/k \rfloor$ is odd. For every natural number $n$, $\mathcal{F}_n = D(n) - 2D(n/2)$,
where $D(n/2) = D(\lfloor n/2 \rfloor)$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 3 (`jis-2024-24.2.5-cor-3`). -/
public theorem floorQuotientOddCount_eq_divisor_summatory_sub (n : ℕ) :
    (floorQuotientOddCount n : ℤ) =
      ∑ m ∈ Finset.Icc 1 n, (m.divisors.card : ℤ) -
        2 * ∑ m ∈ Finset.Icc 1 (n / 2), (m.divisors.card : ℤ) := by
  rw [floorQuotientOddCount_eq_alternating_sum, sum_divisors_card_eq_sum_div,
    sum_divisors_card_eq_sum_div, ← sum_even_floor_div, sum_filter, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  by_cases hd : Even d
  · have h : Odd (d + 1) := Nat.odd_add_one.mpr (Nat.not_odd_iff_even.mpr hd)
    simp [h.neg_one_pow, hd]
    omega
  · have h : Even (d + 1) := Nat.even_add_one.mpr hd
    simp [h.neg_one_pow, hd]

-- Partition the positive pairs by their product, using Mathlib's finite factor-pair fibers.
private def positiveProductLE (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc 1 n).biUnion Nat.divisorsAntidiagonal).map
    (.prodMap ⟨Int.ofNat, fun _ _ h => Int.ofNat.inj h⟩ ⟨Int.ofNat, fun _ _ h => Int.ofNat.inj h⟩)

private theorem mem_positiveProductLE {n : ℕ} {p : ℤ × ℤ} :
    p ∈ positiveProductLE n ↔ 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 * p.2 ≤ n := by
  rw [positiveProductLE, mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨m, hm, hq⟩ := mem_biUnion.mp hq
    have hx : 1 ≤ q.1 := Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hq)
    have hy : 1 ≤ q.2 := Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hq)
    have hxy : q.1 * q.2 ≤ n :=
      (Nat.mem_divisorsAntidiagonal.mp hq).1.le.trans (mem_Icc.mp hm).2
    change 1 ≤ (q.1 : ℤ) ∧ 1 ≤ (q.2 : ℤ) ∧ (q.1 : ℤ) * (q.2 : ℤ) ≤ n
    exact ⟨by exact_mod_cast hx, by exact_mod_cast hy, by exact_mod_cast hxy⟩
  · rintro ⟨hx, hy, hxy⟩
    let q : ℕ × ℕ := (p.1.toNat, p.2.toNat)
    have hx' : (q.1 : ℤ) = p.1 := Int.toNat_of_nonneg (by omega)
    have hy' : (q.2 : ℤ) = p.2 := Int.toNat_of_nonneg (by omega)
    have hle : (q.1 : ℤ) * (q.2 : ℤ) ≤ n := by rwa [hx', hy']
    have hpos : 0 < q.1 * q.2 := Nat.mul_pos (by omega) (by omega)
    exact ⟨q, mem_biUnion.mpr ⟨q.1 * q.2, mem_Icc.mpr ⟨hpos, by exact_mod_cast hle⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hpos.ne'⟩⟩, Prod.ext hx' hy'⟩

private theorem card_positiveProductLE (n : ℕ) :
    ((positiveProductLE n).card : ℤ) = ∑ m ∈ Icc 1 n, (m.divisors.card : ℤ) := by
  rw [positiveProductLE, card_map, card_biUnion]
  · push_cast
    simp only [← Nat.map_div_right_divisors, card_map]
  · intro m _ k _ hmk
    exact disjoint_left.mpr fun p hp hq =>
      hmk ((Nat.mem_divisorsAntidiagonal.mp hp).1.symm.trans
        (Nat.mem_divisorsAntidiagonal.mp hq).1)

/-- **Odd floor quotients as a hyperbolic lattice-point difference.** For every natural number
$n$, the floor sequence parity count $\mathcal{F}_n$ equals the number of integer pairs $(x, y)$
with $x, y \ge 1$ and $n/2 < xy \le n$ minus the number of integer pairs $(x, y)$ with
$x, y \ge 1$ and $xy \le n/2$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 4 (`jis-2024-24.2.5-prop-4`). -/
public theorem floorQuotientOddCount_eq_hyperbolic_lattice_difference
    (n : ℕ) :
    (floorQuotientOddCount n : ℤ) =
      (Nat.card {p : ℤ × ℤ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧
          (n : ℤ) < 2 * (p.1 * p.2) ∧ p.1 * p.2 ≤ n} : ℤ) -
        Nat.card {p : ℤ × ℤ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 2 * (p.1 * p.2) ≤ n} := by
  have half_le (z : ℤ) : z ≤ ((n / 2 : ℕ) : ℤ) ↔ 2 * z ≤ n := by omega
  have lower_mem (p : ℤ × ℤ) : p ∈ positiveProductLE (n / 2) ↔
      1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 2 * (p.1 * p.2) ≤ n := by
    rw [mem_positiveProductLE, half_le]
  have upper_mem (p : ℤ × ℤ) : p ∈ positiveProductLE n \ positiveProductLE (n / 2) ↔
      1 ≤ p.1 ∧ 1 ≤ p.2 ∧ (n : ℤ) < 2 * (p.1 * p.2) ∧ p.1 * p.2 ≤ n := by
    rw [mem_sdiff, mem_positiveProductLE, lower_mem p]
    constructor
    · rintro ⟨⟨hx, hy, hxy⟩, h⟩
      exact ⟨hx, hy, lt_of_not_ge (fun hle => h ⟨hx, hy, hle⟩), hxy⟩
    · rintro ⟨hx, hy, hlt, hxy⟩
      exact ⟨⟨hx, hy, hxy⟩, fun h => hlt.not_ge h.2.2⟩
  have hsub : positiveProductLE (n / 2) ⊆ positiveProductLE n := by
    intro p hp
    obtain ⟨hx, hy, hxy⟩ := (lower_mem p).mp hp
    exact mem_positiveProductLE.mpr ⟨hx, hy, by omega⟩
  have hcard := card_sdiff_add_card_eq_card hsub
  rw [Nat.subtype_card _ upper_mem, Nat.subtype_card _ lower_mem,
    floorQuotientOddCount_eq_divisor_summatory_sub,
    ← card_positiveProductLE, ← card_positiveProductLE]
  omega

end MetaMathlibExt
