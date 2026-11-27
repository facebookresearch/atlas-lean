/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.BinomialPowerRealizability
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination

/-! # A binomial sum through central Delannoy numbers -/

namespace MathlibExt.NumberTheory.DelannoyTriangleWanted

open Polynomial

private noncomputable def delannoyPolynomial : ℤ[X] := (X + 1) * (X + 2)

-- Expand the second factor as ((X + 1) + 1) to read off the binomial sums.
private theorem coeff_delannoyPolynomial_pow (k m : ℕ) :
    (delannoyPolynomial ^ k).coeff m = ∑ j ∈ Finset.range (k + 1),
      (Nat.choose k j * Nat.choose (k + j) m : ℤ) := by
  rw [delannoyPolynomial, mul_pow, show (X + 2 : ℤ[X]) = (X + 1) + 1 by ring,
    add_pow (X + 1 : ℤ[X]) 1, Finset.mul_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  simp only [one_pow, mul_one, ← mul_assoc, ← pow_add, coeff_mul_natCast, coeff_X_add_one_pow]
  exact mul_comm _ _

private theorem central_coeff (k : ℕ) :
    (delannoyPolynomial ^ k).coeff k = (MetaMathlibExt.binomialPowerSeq 1 1 k : ℤ) := by
  rw [coeff_delannoyPolynomial_pow, MetaMathlibExt.binomialPowerSeq, Nat.cast_sum]
  simp only [pow_one, Nat.cast_mul, Nat.choose_symm_add (a := k)]

-- Take the coefficient of X^(k+1) in the identity obtained from 2P - XP' = 3X + 4.
private theorem adjacent_coeff (k : ℕ) :
    4 * (delannoyPolynomial ^ k).coeff (k + 1) =
      (delannoyPolynomial ^ (k + 1)).coeff (k + 1) - 3 * (delannoyPolynomial ^ k).coeff k := by
  let P := delannoyPolynomial
  have hquad : 2 * P - X * derivative P = 3 * X + 4 := by
    simp [P, delannoyPolynomial, derivative_mul]
    ring
  have h : C ((k : ℤ) + 1) * (2 * P ^ (k + 1)) - X * derivative (P ^ (k + 1)) =
      C ((k : ℤ) + 1) * (3 * (X * P ^ k) + 4 * P ^ k) := by
    rw [derivative_pow_succ, pow_succ]
    linear_combination C ((k : ℤ) + 1) * P ^ k * hquad
  have hc := congrArg (fun f : ℤ[X] ↦ f.coeff (k + 1)) h
  simp only [coeff_sub, coeff_C_mul, coeff_ofNat_mul, coeff_X_mul, coeff_derivative,
    coeff_add] at hc
  apply mul_left_cancel₀ (show (k : ℤ) + 1 ≠ 0 by positivity)
  linear_combination -hc

/-- **A binomial sum through central Delannoy numbers.** For every natural number $k$,
$$4 \sum_{j=0}^{k} \binom{k}{j} \binom{k+j}{k+1} = D_{k+1} - 3 D_k,$$
where $D_n = A_{1,1}(n) = \sum_{i=0}^{n} \binom{n}{i} \binom{n+i}{i}$ is the binomial-power
number with $r = s = 1$, that is, the $n$-th central Delannoy number.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 13. -/
public theorem sum_choose_choose_binomialPowerSeq (k : ℕ) :
    4 * (∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j * Nat.choose (k + j) (k + 1) : ℤ)) =
      (MetaMathlibExt.binomialPowerSeq 1 1 (k + 1) : ℤ) -
        3 * (MetaMathlibExt.binomialPowerSeq 1 1 k : ℤ) := by
  rw [← coeff_delannoyPolynomial_pow, ← central_coeff, ← central_coeff]
  exact adjacent_coeff k

end MathlibExt.NumberTheory.DelannoyTriangleWanted
