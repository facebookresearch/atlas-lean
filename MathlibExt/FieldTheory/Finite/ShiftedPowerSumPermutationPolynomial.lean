/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import MathlibExt.FieldTheory.Finite.PermutationPolynomial
import MathlibExt.FieldTheory.Finite.MonomialPermutationPolynomial
import all MathlibExt.FieldTheory.Finite.OrderedPartitionCongruence

/-!
# Shifted power-sum permutation polynomials over prime fields

`isPermutationPolynomial_sum_pow_mul_X_pow_add` follows by showing that the shifted power
sum induces the same function as the monomial `X ^ (a + 1)`.
-/

namespace MetaMathlibExt

open Finset Polynomial

-- The odd-prime and positive-shift hypotheses are retained from the source statement.
set_option linter.unusedVariables false in
/-- **Shifted power-sum permutation polynomials of a prime field.** Let $p$ be an odd prime and
let $k, t, a$ be positive integers with $\gcd(a + 1, p - 1) = 1$ and $k \equiv 1 \pmod{p(p-1)}$.
Suppose that $p - 1 \nmid t$ or $p^2 \mid k - 1$. Then the polynomial
$\sum_{n=1}^{k} n^t X^{n+a}$, with coefficients reduced modulo $p$, is a permutation polynomial
of $\mathbb{F}_p$.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 1
(`integers-2024-A12-cor-1`). -/
public theorem isPermutationPolynomial_sum_pow_mul_X_pow_add {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {k t a : ℕ} (hk : 0 < k) (ht : 0 < t) (ha : 0 < a)
    (hka : (a + 1).Coprime (p - 1)) (hkcong : k ≡ 1 [MOD p * (p - 1)])
    (hcases : ¬(p - 1) ∣ t ∨ p ^ 2 ∣ k - 1) :
    (∑ n ∈ Finset.Icc 1 k, C ((n : ZMod p) ^ t) * X ^ (n + a)).IsPermutationPolynomial := by
  have hsum (x : ZMod p) : ∑ n ∈ Icc 1 k, (n : ZMod p) ^ t * x ^ n = x := by
    by_cases hx : x = 0
    · subst x
      exact sum_eq_zero fun n hn => by
        rw [zero_pow (Nat.ne_of_gt (mem_Icc.mp hn).1), mul_zero]
    · exact OrderedPartitionCongruence.weighted_sum_eq_self hk ht hkcong
        (fun hd => hcases.resolve_left fun h => h hd) (Units.mk0 x hx)
  have heval (x : ZMod p) :
      (∑ n ∈ Icc 1 k, C ((n : ZMod p) ^ t) * X ^ (n + a)).eval x =
        (X ^ (a + 1) : (ZMod p)[X]).eval x := by
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, pow_add, pow_one,
      ← mul_assoc, ← sum_mul, hsum, mul_comm x (x ^ a)]
  rw [IsPermutationPolynomial, funext heval]
  exact (isPermutationPolynomial_X_pow_iff_coprime (Nat.succ_pos a)).2
    (by simpa [ZMod.card] using hka)

end MetaMathlibExt
