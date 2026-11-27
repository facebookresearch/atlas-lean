/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import MathlibExt.FieldTheory.Finite.PermutationPolynomial
import Mathlib.FieldTheory.Finite.Basic
import MathlibExt.FieldTheory.Finite.MonomialPermutationPolynomial
import MathlibExt.FieldTheory.Finite.ShiftedPowerSumPermutationPolynomial

/-!
# Dilated power-sum permutation polynomials over prime fields

The dilated power sum acts by a power map, the undilated power sum, and a nonzero scalar.
The undilated sum induces the same function as the sum shifted by `p - 1`.

## References

* Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered Partitions
  Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, pp. 1–11, Corollaries 1 and 3
  and Lemma 5. <https://math.colgate.edu/~integers/y12/y12.pdf>
* Rudolf Lidl and Harald Niederreiter, *Finite Fields*, 2nd ed., Encyclopedia of Mathematics
  and its Applications 20, Cambridge University Press (1997), Lemma 7.3 and Theorem 7.8
  (the finite-field power sums and monomial criterion cited by Vishwakarma and Singh).
-/

namespace MetaMathlibExt

open Finset Polynomial

/-- **Dilated power-sum permutation polynomials of a prime field.** Let $p$ be an odd prime and
let $k, t, a$ be positive integers with $p \nmid a$, $\gcd(a, p - 1) = 1$ and
$k \equiv 1 \pmod{p(p-1)}$. Suppose that $p - 1 \nmid t$ or $p^2 \mid k - 1$. Then the
polynomial $\sum_{n=1}^{k} (an)^t X^{an}$, with coefficients reduced modulo $p$, is a
permutation polynomial of $\mathbb{F}_p$.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 3
(`integers-2024-A12-cor-3`). -/
public theorem isPermutationPolynomial_sum_mul_pow_mul_X_pow_mul {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) {k t a : ℕ} (hk : 0 < k) (ht : 0 < t) (ha : 0 < a)
    (hpa : ¬p ∣ a) (hap : a.Coprime (p - 1)) (hkcong : k ≡ 1 [MOD p * (p - 1)])
    (hcases : ¬(p - 1) ∣ t ∨ p ^ 2 ∣ k - 1) :
    (∑ n ∈ Finset.Icc 1 k,
      C (((a * n : ℕ) : ZMod p) ^ t) * X ^ (a * n)).IsPermutationPolynomial := by
  have hprime : p.Prime := Fact.out
  have hshift : 0 < p - 1 := Nat.sub_pos_of_lt hprime.one_lt
  have hcop : (p - 1 + 1).Coprime (p - 1) := by
    rw [Nat.coprime_self_add_left]
    exact Nat.coprime_one_left _
  have hbij : Function.Bijective
      (fun x : ZMod p => ∑ n ∈ Icc 1 k, (n : ZMod p) ^ t * x ^ (n + (p - 1))) := by
    simpa only [IsPermutationPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] using
      isPermutationPolynomial_sum_pow_mul_X_pow_add hp hk ht hshift hcop hkcong hcases
  have hremove (x : ZMod p) :
      (∑ n ∈ Icc 1 k, (n : ZMod p) ^ t * x ^ (n + (p - 1))) =
        ∑ n ∈ Icc 1 k, (n : ZMod p) ^ t * x ^ n := by
    refine sum_congr rfl fun n hn => ?_
    by_cases hx : x = 0
    · have hn0 : 0 < n := (mem_Icc.mp hn).1
      have hadd : n + (p - 1) ≠ 0 := by omega
      rw [hx, zero_pow hadd, zero_pow hn0.ne']
    · have hxpow : x ^ (p - 1) = 1 := by
        simpa only [ZMod.card] using FiniteField.pow_card_sub_one_eq_one x hx
      rw [pow_add, hxpow, mul_one]
  have haBij : Function.Bijective (fun x : ZMod p => x ^ a) := by
    simpa only [IsPermutationPolynomial, eval_pow, eval_X] using
      (isPermutationPolynomial_X_pow_iff_coprime (K := ZMod p) ha).2
        (by simpa only [ZMod.card] using hap)
  have ha0 : (a : ZMod p) ≠ 0 := fun h => hpa ((ZMod.natCast_eq_zero_iff a p).mp h)
  have hscale : Function.Bijective (fun x : ZMod p => (a : ZMod p) ^ t * x) :=
    (Equiv.mulLeft₀ _ (pow_ne_zero t ha0)).bijective
  have heval (x : ZMod p) :
      (∑ n ∈ Icc 1 k, C (((a * n : ℕ) : ZMod p) ^ t) * X ^ (a * n)).eval x =
        (a : ZMod p) ^ t * ∑ n ∈ Icc 1 k, (n : ZMod p) ^ t * (x ^ a) ^ n := by
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Nat.cast_mul, mul_pow,
      pow_mul, mul_sum, mul_assoc]
  rw [IsPermutationPolynomial, funext heval]
  simpa only [Function.comp_def, hremove] using hscale.comp (hbij.comp haBij)

end MetaMathlibExt
