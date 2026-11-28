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
# Alternating binomial sums down trinomial columns

The alternating binomial sum down column `m` is the coefficient of `X ^ m` in
`X ^ n * (1 + X) ^ n`, hence equals `n.choose (m - n)` when `n ≤ m`.
-/

open Polynomial

namespace MetaMathlibExt

/-- **Alternating binomial sum down a trinomial column.** Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. For natural numbers $n \le m$,
$\sum_{k=0}^{n} (-1)^k \binom{n}{k} \binom{n-k}{m}_2 = \binom{n}{m-n}$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 18 (`jis-2025-25.3.5-thm-18`). -/
public theorem sum_trinomialCoefficient_sub_mul_choose (n m : ℕ) (h : n ≤ m) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient (n - k) m : ℤ) * n.choose k * (-1) ^ k =
      (n.choose (m - n) : ℤ) := by
  let P : ℤ[X] := 1 + X + X ^ 2
  have hcoeff (r : ℕ) : (trinomialCoefficient r m : ℤ) = (P ^ r).coeff m := by
    change (Nat.castRingHom ℤ) (((1 + X + X ^ 2 : ℕ[X]) ^ r).coeff m) = _
    rw [← coeff_map, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_add,
      Polynomial.map_pow, Polynomial.map_one, map_X]
  have hfactor : C (-1 : ℤ) + P = X * (1 + X) := by
    simp only [P, map_neg, map_one]
    ring
  calc
    _ = ((C (-1 : ℤ) + P) ^ n).coeff m := by
      rw [add_pow, finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro k _
      rw [coeff_mul_natCast, ← C_pow, coeff_C_mul, hcoeff]
      ring
    _ = _ := by
      rw [hfactor, mul_pow, coeff_X_pow_mul', ite_eq_left h, coeff_one_add_X_pow]

end MetaMathlibExt
