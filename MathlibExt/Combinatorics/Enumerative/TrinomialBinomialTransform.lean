/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TrinomialCoefficient
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

/-!
# Two binomial transforms of a trinomial row

The substitution `X ↦ -1 - X` preserves `1 + X + X ^ 2`. Extracting a coefficient of the
substituted row gives the alternating transform. Multiplying by `(1 + X) ^ m` before taking
that coefficient gives the identity between the two binomial sums.
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
  let p : ℤ[X] := 1 + X + X ^ 2
  let q : ℤ[X] := 1 + X
  have hmap : (1 + X + X ^ 2 : ℕ[X]).map (Nat.castRingHom ℤ) = p := by simp [p]
  have hcoeff (k : ℕ) : (p ^ n).coeff k = (trinomialCoefficient n k : ℤ) := by
    rw [← hmap, ← Polynomial.map_pow, coeff_map, trinomialCoefficient]
    rfl
  have hdeg : (p ^ n).natDegree < 2 * n + 1 := by
    apply Nat.lt_succ_of_le
    dsimp [p]
    rw [Nat.mul_comm]
    compute_degree
  have hp : p.comp (-1 - X) = p := by
    simp only [p, add_comp, one_comp, X_comp, X_pow_comp]
    ring
  have hsign : (-1 - X : ℤ[X]) = C (-1) * q := by
    simp [q, sub_eq_add_neg, add_comm]
  calc
    _ = (p ^ n * q ^ m).coeff m := by
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      refine Finset.sum_congr rfl fun k hk => ?_
      dsimp only [q]
      have hk' : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [hcoeff, coeff_one_add_X_pow, Nat.choose_symm hk']
    _ = ((p ^ n).comp (-1 - X) * q ^ m).coeff m := by rw [pow_comp, hp]
    _ = _ := by
      change (eval₂ C (-1 - X) (p ^ n) * q ^ m).coeff m = _
      rw [eval₂_eq_sum_range' C hdeg, Finset.sum_mul, finsetSum_coeff]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsign, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, mul_assoc, ← pow_add]
      dsimp only [q]
      rw [coeff_C_mul, coeff_one_add_X_pow, hcoeff, Nat.add_comm k m, Nat.choose_symm_add]
      ac_rfl

/-- **Alternating binomial transform of a row of trinomial coefficients.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. For all
$n, m \in \mathbb{N}$
$$\sum_{k=m}^{2n} \binom{n}{k}_2 \binom{k}{m} (-1)^k = \binom{n}{m}_2.$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 16 (`jis-2025-25.3.5-thm-16`). -/
public theorem sum_trinomialCoefficient_mul_choose_alternating (n m : ℕ) :
    ∑ k ∈ Finset.Icc m (2 * n), (trinomialCoefficient n k : ℤ) * k.choose m * (-1) ^ k =
      (trinomialCoefficient n m : ℤ) := by
  let p : ℤ[X] := 1 + X + X ^ 2
  have hmap : (1 + X + X ^ 2 : ℕ[X]).map (Nat.castRingHom ℤ) = p := by simp [p]
  have hcoeff (k : ℕ) : (p ^ n).coeff k = (trinomialCoefficient n k : ℤ) := by
    rw [← hmap, ← Polynomial.map_pow, coeff_map, trinomialCoefficient]
    rfl
  have hdeg : (p ^ n).natDegree < 2 * n + 1 := by
    apply Nat.lt_succ_of_le
    dsimp [p]
    rw [Nat.mul_comm]
    compute_degree
  have hp : p.comp (-1 - X) = p := by
    simp only [p, add_comp, one_comp, X_comp, X_pow_comp]
    ring
  have hsign : (-1 - X : ℤ[X]) = C (-1) * (1 + X) := by
    simp [sub_eq_add_neg, add_comm]
  calc
    _ = ∑ k ∈ Finset.range (2 * n + 1), (trinomialCoefficient n k : ℤ) * k.choose m * (-1) ^ k := by
      refine Finset.sum_subset ?_ ?_
      · intro k hk
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2)
      · intro k hk hk'
        have hkm : k < m := by
          simp only [Finset.mem_range, Finset.mem_Icc, not_and] at hk hk'
          omega
        simp [Nat.choose_eq_zero_of_lt hkm]
    _ = ((p ^ n).comp (-1 - X)).coeff m := by
      change _ = (eval₂ C (-1 - X) (p ^ n)).coeff m
      rw [eval₂_eq_sum_range' C hdeg, finsetSum_coeff]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsign, mul_pow, ← C_pow, coeff_C_mul, coeff_C_mul, coeff_one_add_X_pow, hcoeff]
      ac_rfl
    _ = _ := by rw [pow_comp, hp, hcoeff]

end MetaMathlibExt
