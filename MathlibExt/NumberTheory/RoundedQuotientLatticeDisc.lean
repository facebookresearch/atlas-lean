/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.NumberTheory.RoundQuotientOddCount
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import MathlibExt.NumberTheory.JacobiTwoSquareCount

/-!
# Lattice points in a closed disc

Partition the disc by squared radius. The origin contributes one point; Jacobi's formula
counts each positive-radius fiber. Summing first over divisors then gives the alternating
floor sum for odd rounded quotients.
-/

namespace MetaMathlibExt

open Finset

private abbrev SquareFiber (j : ℕ) := {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = (j : ℤ)}

private def discEquivSigma (N : ℕ) :
    {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ (N : ℤ)} ≃
      (j : Fin (N + 1)) × SquareFiber (j : ℕ) where
  toFun p := by
    have h : 0 ≤ p.1.1 ^ 2 + p.1.2 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hcast := Int.toNat_of_nonneg h
    exact ⟨⟨(p.1.1 ^ 2 + p.1.2 ^ 2).toNat, by have := p.2; omega⟩, ⟨p.1, hcast.symm⟩⟩
  invFun q := ⟨q.2.1, by rw [q.2.2]; have := q.1.isLt; omega⟩
  left_inv _ := Subtype.ext rfl
  right_inv := by
    rintro ⟨j, p, hp⟩
    have hj : (p.1 ^ 2 + p.2 ^ 2).toNat = (j : ℕ) := by rw [hp, Int.toNat_natCast]
    exact Sigma.subtype_ext (Fin.ext hj) rfl

private theorem representationNumber_two_zero : SumSquares.representationNumber 2 0 = 1 := by
  rw [SumSquares.representationNumber_two_eq]
  let _ : Unique (SquareFiber 0) := {
    default := ⟨(0, 0), by simp⟩
    uniq p := by
      have hp : p.1.1 ^ 2 + p.1.2 ^ 2 = 0 := p.2
      have hx : p.1.1 ^ 2 = 0 := by nlinarith only [hp, sq_nonneg p.1.1, sq_nonneg p.1.2]
      have hy : p.1.2 ^ 2 = 0 := by nlinarith only [hp, sq_nonneg p.1.1, sq_nonneg p.1.2]
      apply Subtype.ext
      exact Prod.ext (by simpa [pow_two] using hx) (by simpa [pow_two] using hy) }
  exact Fintype.card_unique

private theorem card_disc_eq_sum (N : ℕ) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ (N : ℤ)} : ℤ) =
      1 + 4 * ∑ j ∈ Icc 1 N, ∑ d ∈ j.divisors, ZMod.χ₄ d := by
  have hcard : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ (N : ℤ)} =
      ∑ j ∈ range (N + 1), SumSquares.representationNumber 2 j := by
    rw [Nat.card_congr (discEquivSigma N), Nat.card_eq_fintype_card, Fintype.card_sigma,
      ← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun j _ => (SumSquares.representationNumber_two_eq (j : ℕ)).symm
  have hrange : range (N + 1) = insert 0 (Icc 1 N) := by
    ext j
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hcard, hrange, sum_insert (by simp : (0 : ℕ) ∉ Icc 1 N), representationNumber_two_zero]
  push_cast
  rw [mul_sum]
  apply congrArg (1 + ·)
  exact sum_congr rfl fun j hj =>
    SumSquares.representationNumber_two_jacobi_count j (mem_Icc.mp hj).1

-- The multiples parametrization and divisor-sum interchange follow the private proofs in
-- `MathlibExt.NumberTheory.FloorQuotientDivisorSummatory`, with a weight for each divisor.
private theorem multiples_Icc (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (Icc 1 N).filter (d ∣ ·) =
      (Icc 1 (N / d)).map ⟨fun k => d * k, fun _ _ h => Nat.eq_of_mul_eq_mul_left hd h⟩ := by
  ext m
  simp only [mem_filter, mem_map, mem_Icc]
  constructor
  · rintro ⟨⟨hm, hmn⟩, k, rfl⟩
    refine ⟨k, ⟨?_, (Nat.le_div_iff_mul_le hd).2 (by simpa [Nat.mul_comm] using hmn)⟩, rfl⟩
    by_contra! hk
    obtain rfl : k = 0 := by omega
    simp at hm
  · rintro ⟨k, ⟨hk, hkn⟩, rfl⟩
    change (1 ≤ d * k ∧ d * k ≤ N) ∧ d ∣ d * k
    refine ⟨⟨Nat.mul_pos hd hk, ?_⟩, dvd_mul_right d k⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).1 hkn

private theorem sum_divisor_chi (N : ℕ) :
    (∑ j ∈ Icc 1 N, ∑ d ∈ j.divisors, ZMod.χ₄ d) =
      ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℤ) * ZMod.χ₄ d := by
  calc
    _ = ∑ j ∈ Icc 1 N, ∑ d ∈ Icc 1 N, if d ∣ j then ZMod.χ₄ d else 0 := by
      refine sum_congr rfl fun j hj => ?_
      have hdivisors : (Icc 1 N).filter (· ∣ j) = j.divisors := by
        ext d
        refine ⟨fun h => Nat.mem_divisors.mpr ⟨(mem_filter.mp h).2, by
          have := (mem_Icc.mp hj).1
          omega⟩, fun h => ?_⟩
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors h,
          (Nat.divisor_le h).trans (mem_Icc.mp hj).2⟩, Nat.dvd_of_mem_divisors h⟩
      rw [← sum_filter, hdivisors]
    _ = ∑ d ∈ Icc 1 N, ∑ j ∈ Icc 1 N, if d ∣ j then ZMod.χ₄ d else 0 := sum_comm
    _ = _ := by
      refine sum_congr rfl fun d hd => ?_
      rw [← sum_filter, sum_const, multiples_Icc N (mem_Icc.mp hd).1, card_map, Nat.card_Icc,
        nsmul_eq_mul]
      simp

private theorem chi_odd_denominator {d : ℕ} (hd : 1 ≤ d) :
    ZMod.χ₄ ((2 * d - 1 : ℕ) : ZMod 4) = (-1 : ℤ) ^ (d + 1) := by
  rw [ZMod.χ₄_nat_eq_if_mod_four, ite_eq_right (by omega)]
  by_cases h : (d + 1) % 2 = 0
  · rw [ite_eq_left (by omega), (Nat.even_iff.mpr h).neg_one_pow]
  · rw [ite_eq_right (by omega), (Nat.odd_iff.mpr (by omega : (d + 1) % 2 = 1)).neg_one_pow]

private theorem sum_chi_even_bound (n : ℕ) :
    (∑ d ∈ Icc 1 (2 * n), ((2 * n / d : ℕ) : ℤ) * ZMod.χ₄ d) =
      ∑ d ∈ Icc 1 n, ((2 * n / (2 * d - 1) : ℕ) : ℤ) * (-1) ^ (d + 1) := by
  let oddDenominator : ℕ ↪ ℕ := ⟨fun d => 2 * d - 1, by
    intro a b h
    change 2 * a - 1 = 2 * b - 1 at h
    omega⟩
  have hodd : (Icc 1 (2 * n)).filter (fun d => d % 2 ≠ 0) = (Icc 1 n).map oddDenominator := by
    ext d
    simp only [mem_filter, mem_Icc, mem_map]
    change (1 ≤ d ∧ d ≤ 2 * n) ∧ d % 2 ≠ 0 ↔
      ∃ k, (1 ≤ k ∧ k ≤ n) ∧ 2 * k - 1 = d
    constructor
    · intro h
      exact ⟨d / 2 + 1, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  calc
    _ = ∑ d ∈ (Icc 1 (2 * n)).filter (fun d => d % 2 ≠ 0),
          ((2 * n / d : ℕ) : ℤ) * ZMod.χ₄ d := by
      rw [sum_filter]
      refine sum_congr rfl fun d _ => ?_
      by_cases hd : d % 2 = 0
      · have hχ : ZMod.χ₄ (d : ZMod 4) = 0 := by
          rw [ZMod.χ₄_nat_eq_if_mod_four, ite_eq_left hd]
        simp [hd, hχ]
      · simp [hd]
    _ = _ := by
      rw [hodd, sum_map]
      refine sum_congr rfl fun d hd => ?_
      change ((2 * n / (2 * d - 1) : ℕ) : ℤ) * ZMod.χ₄ ((2 * d - 1 : ℕ) : ZMod 4) = _
      rw [chi_odd_denominator (mem_Icc.mp hd).1]

/-- **Lattice points in the disc of radius $\sqrt{2n}$.** For every natural number $n$, the
number of pairs $(x, y) \in \mathbb{Z}^2$ with $x^2 + y^2 \le 2n$ equals
$4\,\mathcal{R}_n + 4n + 1$, where $\mathcal{R}_n$ is the number of $k \in \{1, \dots, n\}$ for
which the nearest integer to $n/k$, with half-integers rounded up, is odd. At $n = 0$ both sides
are $1$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 17 (`jis-2024-24.2.5-prop-17`). -/
public theorem card_lattice_disc_two_mul (n : ℕ) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ 2 * n} =
      4 * roundQuotientOddCount n + 4 * n + 1 := by
  have h := card_disc_eq_sum (2 * n)
  rw [sum_divisor_chi, sum_chi_even_bound] at h
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  have hr := roundQuotientOddCount_eq_alternating_sum n
  exact_mod_cast (show (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ 2 * n} : ℤ) =
    4 * (roundQuotientOddCount n : ℤ) + 4 * (n : ℤ) + 1 by omega)

end MetaMathlibExt
