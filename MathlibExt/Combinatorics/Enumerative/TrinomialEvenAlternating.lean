/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TrinomialCoefficient
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.Ring

/-!
# Alternating binomial sums over even trinomial rows

The alternating sum is the coefficient of `X ^ n` in `((1 + X + X ^ 2) ^ 2 - 1) ^ n`.
After factoring out `X ^ n`, only the constant coefficient of the remaining power matters.
-/

open Polynomial

namespace MetaMathlibExt

/-- **Alternating binomial sum of trinomial coefficients over even rows.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. For
every natural number $n$, $\sum_{k=0}^{n} (-1)^k \binom{n}{k} \binom{2n-2k}{n}_2 = 2^n$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 19 (`jis-2025-25.3.5-thm-19`). -/
public theorem sum_trinomialCoefficient_two_mul_sub (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (trinomialCoefficient (2 * n - 2 * k) n : ℤ) * n.choose k * (-1) ^ k = 2 ^ n := by
  let P : ℤ[X] := 1 + X + X ^ 2
  let Q : ℤ[X] := 2 + 3 * X + 2 * X ^ 2 + X ^ 3
  have hcoeff (r : ℕ) : (trinomialCoefficient r n : ℤ) = (P ^ r).coeff n := by
    change (Nat.castRingHom ℤ) (((1 + X + X ^ 2 : ℕ[X]) ^ r).coeff n) = _
    rw [← coeff_map, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_add,
      Polynomial.map_pow, Polynomial.map_one, map_X]
  have hfactor : C (-1 : ℤ) + P ^ 2 = X * Q := by
    simp only [P, Q, map_neg, map_one]
    ring
  calc
    _ = ((C (-1 : ℤ) + P ^ 2) ^ n).coeff n := by
      rw [add_pow, finsetSum_coeff]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coeff_mul_natCast, ← C_pow, coeff_C_mul, ← pow_mul, ← hcoeff,
        Nat.mul_sub_left_distrib]
      ring
    _ = _ := by
      rw [hfactor, mul_pow, coeff_X_pow_mul']
      simp only [le_refl, ite_true, Nat.sub_self]
      change constantCoeff (Q ^ n) = _
      rw [map_pow]
      simp [Q]

end MetaMathlibExt
