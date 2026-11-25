/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Binomial
import Mathlib.Data.Nat.Choose.Sum

/-!
# Alternating sum of binomial row sums

`alternating_choose_mul_sum_choose` expresses a weighted sum of binomial row sums as
an alternating sum of binomial coefficients with integer upper indices.
-/

namespace MetaMathlibExt

open Finset

/-- **Alternating sum of binomial row sums.** For all natural numbers $\ell$ and $n$,
$$\sum_{i=0}^{n} (-1)^i \binom{\ell}{i} \sum_{j=0}^{n-i} \binom{n-i}{j}
  = \sum_{i=0}^{n} (-1)^i \binom{i+\ell-n-1}{i},$$
where on the right $\binom{a}{i} = a(a-1)\cdots(a-i+1)/i!$ is the binomial coefficient with
integer upper index $a$. For $n < \ell$ the upper index $i + \ell - n - 1$ is nonnegative and this
is the ordinary binomial coefficient, the case used in Theorem 4.4.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 4.3 (`fq-2024-florez11012023-lem-4.3`). -/
public theorem alternating_choose_mul_sum_choose (ℓ n : ℕ) :
    ∑ i ∈ range (n + 1), (ℓ.choose i : ℤ) * (-1) ^ i *
        ∑ j ∈ range (n - i + 1), ((n - i).choose j : ℤ) =
      ∑ i ∈ range (n + 1), (-1) ^ i * Ring.choose ((i : ℤ) + ℓ - n - 1) i := by
  have reflect (n i : ℕ) : Ring.choose ((n : ℤ) - ℓ) i =
      (-1) ^ i * Ring.choose ((i : ℤ) + ℓ - n - 1) i := by
    simpa only [neg_sub, show (ℓ : ℤ) - n + i - 1 = i + ℓ - n - 1 by omega,
      Units.smul_def, zsmul_eq_mul, Int.cast_id, Int.coe_negOnePow_natCast]
      using Ring.choose_neg ((ℓ : ℤ) - n) i
  simp_rw [← reflect, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
  induction n with
  | zero => simp
  | succ n ih =>
    -- In the old range each row sum doubles. The last row contributes just its weight.
    have doubleRows :
        ∑ i ∈ range (n + 1), (ℓ.choose i : ℤ) * (-1) ^ i * 2 ^ (n + 1 - i) =
          (∑ i ∈ range (n + 1), (ℓ.choose i : ℤ) * (-1) ^ i * 2 ^ (n - i)) * 2 := by
      rw [sum_mul]
      refine sum_congr rfl fun i hi ↦ ?_
      have hin : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
      rw [Nat.succ_sub hin, pow_succ, ← mul_assoc]
    -- Pascal's rule doubles the partial row sum and leaves one boundary coefficient.
    have pascal (a : ℤ) :
        ∑ i ∈ range (n + 2), Ring.choose (a + 1) i =
          (∑ i ∈ range (n + 1), Ring.choose a i) * 2 + Ring.choose a (n + 1) := by
      rw [sum_range_succ', Ring.choose_zero_right]
      simp_rw [Ring.choose_succ_succ]
      rw [sum_add_distrib, add_assoc, ← Ring.choose_zero_right a, ← sum_range_succ',
        sum_range_succ (Ring.choose a) (n + 1)]
      ring
    rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one, doubleRows, ih, Nat.cast_succ,
      show (n : ℤ) + 1 - ℓ = (n - ℓ) + 1 by omega, pascal, reflect n (n + 1),
      show ((n + 1 : ℕ) : ℤ) + ℓ - n - 1 = ℓ by omega, Ring.choose_natCast,
      mul_comm (ℓ.choose (n + 1) : ℤ)]

end MetaMathlibExt
