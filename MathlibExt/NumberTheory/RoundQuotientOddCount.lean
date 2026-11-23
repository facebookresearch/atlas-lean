/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Ring.GeomSum

/-!
# Odd terms in the rounded quotient sequence

The alternating sum of the thresholds reached by a rounded quotient is its oddness indicator.
Summing over denominators first counts how many rounded quotients reach each threshold.
At the first threshold all `n` denominators contribute, whereas the first floor term is `2 * n`.
This accounts for the correction `-n`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Rounding sequence parity count.** For a natural number $n$, the rounding sequence parity
count $\mathcal R_n$ is the number of integers $k$ with $1 \le k \le n$ for which the nearest
integer to $n/k$ is odd, where half-integers are rounded up: the nearest integer to a rational
number $x$ is taken to be $\lfloor x + 1/2 \rfloor$.

Rounding half-integers up is the paper's convention for $\mathrm{nint}$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 1 (definition of `𝓡_n` and the footnote on `nint`). -/
public def roundQuotientOddCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k : ℕ => Odd (round ((n : ℚ) / (k : ℚ))))).card

/-- **The rounding sequence parity count at $10$.** The number $\mathcal{R}_{10}$ of integers $k$
with $1 \le k \le 10$ for which the nearest integer to $10/k$ (half-integers rounded up) is odd
equals $7$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Figure 1. -/
public theorem roundQuotientOddCount_ten : roundQuotientOddCount 10 = 7 := by
  decide +kernel

namespace roundQuotientOddCount_eq_alternating_sum

open Finset

private theorem round_div_eq (n k : ℕ) :
    round ((n : ℚ) / k) = (((2 * n / k + 1) / 2 : ℕ) : ℤ) := by
  have h : 2 * ((n : ℚ) / k) = ((2 * n : ℕ) : ℚ) / k := by
    simp [mul_div_assoc]
  rw [round_eq_div, h, Rat.floor_natCast_div_natCast]
  push_cast
  rfl

private theorem sum_thresholds {q n : ℕ} (hq : q ≤ n) :
    (∑ d ∈ Icc 1 n, if d ≤ q then (-1 : ℤ) ^ (d + 1) else 0) =
      if Odd q then 1 else 0 := by
  have hs : (Icc 1 n).filter (· ≤ q) = Icc 1 q := by
    ext d
    simp only [mem_filter, mem_Icc]
    omega
  rw [← sum_filter, hs, ← Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [Nat.add_comm 1, pow_succ, ← Nat.not_even_iff_odd]

private theorem threshold_set (n d : ℕ) (hd : 1 ≤ d) :
    ((Icc 1 n).filter fun k => d ≤ (2 * n / k + 1) / 2) =
      Icc 1 (min n (2 * n / (2 * d - 1))) := by
  ext k
  simp only [mem_filter, mem_Icc, le_min_iff]
  by_cases hk : 0 < k
  · rw [Nat.le_div_iff_mul_le (by omega : 0 < 2 * d - 1),
      Nat.mul_comm k (2 * d - 1), ← Nat.le_div_iff_mul_le hk]
    omega
  · omega

end roundQuotientOddCount_eq_alternating_sum

open roundQuotientOddCount_eq_alternating_sum Finset in
/-- **Alternating-sum formula for the rounding sequence parity count.** For every natural
number $n$, the rounding sequence parity count $\mathcal{R}_n$ satisfies
$\mathcal{R}_n = -n + \sum_{d=1}^{n} (-1)^{d+1} \lfloor 2n/(2d-1) \rfloor$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 14 (`jis-2024-24.2.5-prop-14`). -/
public theorem roundQuotientOddCount_eq_alternating_sum (n : ℕ) :
    (roundQuotientOddCount n : ℤ) =
      -n + ∑ d ∈ Finset.Icc 1 n, ((2 * n / (2 * d - 1) : ℕ) : ℤ) * (-1) ^ (d + 1) := by
  let q (k : ℕ) := (2 * n / k + 1) / 2
  have hq (k : ℕ) : q k ≤ n := by
    dsimp [q]
    have := Nat.div_le_self (2 * n) k
    omega
  calc
    (roundQuotientOddCount n : ℤ) = ∑ k ∈ Icc 1 n, (if Odd (q k) then 1 else 0) := by
      simp only [roundQuotientOddCount, round_div_eq, Int.odd_coe_nat, q, sum_boole]
    _ = ∑ d ∈ Icc 1 n, ∑ k ∈ Icc 1 n, if d ≤ q k then (-1 : ℤ) ^ (d + 1) else 0 := by
      rw [sum_comm]
      exact sum_congr rfl fun k _ => (sum_thresholds (hq k)).symm
    _ = ∑ d ∈ Icc 1 n, (min n (2 * n / (2 * d - 1)) : ℕ) * (-1 : ℤ) ^ (d + 1) := by
      refine sum_congr rfl fun d hd => ?_
      rw [← sum_filter, sum_const, threshold_set n d (mem_Icc.mp hd).1]
      simp
    _ = _ := by
      cases n with
      | zero => simp
      | succ n =>
        have hsplit : Icc 1 (n + 1) = insert 1 (Icc 2 (n + 1)) :=
          (insert_Icc_succ_left_eq_Icc (Nat.succ_le_succ (Nat.zero_le n))).symm
        have hone : (1 : ℕ) ∉ Icc 2 (n + 1) := by simp
        rw [hsplit, sum_insert hone, sum_insert hone]
        have hmin (d : ℕ) (hd : d ∈ Icc 2 (n + 1)) :
            min (n + 1) (2 * (n + 1) / (2 * d - 1)) = 2 * (n + 1) / (2 * d - 1) := by
          apply min_eq_right
          apply Nat.div_le_of_le_mul
          have hd₂ := (mem_Icc.mp hd).1
          exact Nat.mul_le_mul_right _ (by omega)
        rw [sum_congr rfl (fun d hd => by rw [hmin d hd])]
        simp
        ring

end

end MetaMathlibExt
