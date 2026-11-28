/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import MathlibExt.FieldTheory.Finite.PermutationPolynomial
import Mathlib.Data.Nat.Prime.Basic
import MathlibExt.Algebra.ZModPermutationPolynomial
import MathlibExt.FieldTheory.Finite.MonomialPermutationPolynomial

/-!
# Dilated power-sum permutation polynomials over prime fields

The dilated power sum acts by a power map, the undilated power sum, and a nonzero scalar.
The undilated sum is bijective by `bijective_sum_pow_mul_pow_zmod`.

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
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hprime.odd_of_ne_two hp)
  have hmodulus : 1 < p * (p - 1) :=
    hprime.one_lt.trans_le (Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hprime.one_lt))
  have hkrem : k % (p * (p - 1)) = 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hmodulus] using hkcong
  have hcases' : k % (p ^ 2) = 1 ∨ ¬(p - 1) ∣ t := by
    refine hcases.symm.imp (fun hd => ?_) id
    have hmod : 1 ≡ k [MOD p ^ 2] := Nat.modEq_of_dvd' hk hd
    have hsq : 1 < p ^ 2 := Nat.one_lt_pow (by decide) hprime.one_lt
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hsq] using hmod.symm
  have hbij :=
    MathlibExt.Algebra.PermutationPolynomialsWanted.bijective_sum_pow_mul_pow_zmod
      p k t hprime hpodd hk ht hkrem hcases'
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
  exact hscale.comp (hbij.comp haBij)

end MetaMathlibExt
