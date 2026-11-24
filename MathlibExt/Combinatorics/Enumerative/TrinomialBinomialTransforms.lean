/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TrinomialCoefficient
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

/-!
# Two binomial transforms of a trinomial row

The main result, `sum_trinomialCoefficient_mul_choose_eq`, says that the binomial transform
`∑ k, T(n, k) * m.choose k` of the `n`-th row of trinomial coefficients equals the alternating
transform `∑ k, T(n, k) * (m + k).choose k * (-1) ^ k`.

Both sides are the coefficient of `X ^ m` in `(1 + X + X ^ 2) ^ n * (1 + X) ^ m`. For the second
side, substitute `-(1 + X)` for `X` in `(1 + X + X ^ 2) ^ n`; this leaves `1 + X + X ^ 2`
unchanged, because `1 - (1 + X) + (1 + X) ^ 2 = 1 + X + X ^ 2`.
-/

open Polynomial

namespace MetaMathlibExt

/-- **Two binomial transforms of a row of trinomial coefficients agree.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. For all
$n, m \in \mathbb{N}$
$$\sum_{k=0}^{m} \binom{n}{k}_2 \binom{m}{k} =
\sum_{k=0}^{2n} \binom{n}{k}_2 \binom{m+k}{k} (-1)^k.$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 17 (`jis-2025-25.3.5-thm-17`). -/
public theorem sum_trinomialCoefficient_mul_choose_eq (n m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (trinomialCoefficient n k : ℤ) * m.choose k =
      ∑ k ∈ Finset.range (2 * n + 1),
        (trinomialCoefficient n k : ℤ) * (m + k).choose k * (-1) ^ k := by
  set Q : ℤ[X] := (1 + X + X ^ 2) ^ n with hQ
  have hcoeff (k : ℕ) : (trinomialCoefficient n k : ℤ) = Q.coeff k := by
    change (Nat.castRingHom ℤ) (((1 + X + X ^ 2 : ℕ[X]) ^ n).coeff k) = _
    rw [← coeff_map, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_add,
      Polynomial.map_pow, Polynomial.map_one, map_X]
  have hdeg : Q.natDegree < 2 * n + 1 := by
    have h : Q.natDegree ≤ n * 2 := by
      rw [hQ]
      compute_degree
    omega
  -- The trinomial `1 + X + X ^ 2` is invariant under `X ↦ -(1 + X)`.
  have hsymm : Q.comp (-(1 + X)) = Q := by
    rw [hQ, pow_comp]
    congr 1
    simp only [add_comp, one_comp, X_comp, X_pow_comp]
    ring
  -- The left side is the coefficient of `X ^ m` in `Q * (1 + X) ^ m`.
  have hleft : ∑ k ∈ Finset.range (m + 1), (trinomialCoefficient n k : ℤ) * m.choose k =
      (Q * (1 + X) ^ m).coeff m := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hcoeff, coeff_one_add_X_pow,
      Nat.choose_symm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  -- The right side is the same coefficient after substituting `-(1 + X)` in `Q`.
  have hright : ∑ k ∈ Finset.range (2 * n + 1),
      (trinomialCoefficient n k : ℤ) * (m + k).choose k * (-1) ^ k =
      (Q.comp (-(1 + X)) * (1 + X) ^ m).coeff m := by
    rw [comp_eq_sum_left, sum_over_range' _ (fun _ => by simp) _ hdeg, Finset.sum_mul,
      finsetSum_coeff]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hterm : C (Q.coeff k) * (-(1 + X)) ^ k * (1 + X) ^ m =
        C (Q.coeff k * (-1) ^ k) * (1 + X) ^ (m + k) := by
      rw [neg_pow, map_mul, map_pow, map_neg, map_one]
      ring
    rw [hterm, coeff_C_mul, coeff_one_add_X_pow, Nat.choose_symm_add, hcoeff]
    ring
  rw [hleft, hright, hsymm]

end MetaMathlibExt
