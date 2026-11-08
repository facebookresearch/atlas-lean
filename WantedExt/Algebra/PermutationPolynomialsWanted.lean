/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Permutation polynomials of the form `∑ n ∈ [1,k], h n * X ^ n`

Statements from Zhiguo Ding and Michael E. Zieve, "Permutation
Polynomials of the Form `∑_{n=1}^k h(n) X^n`", *INTEGERS* 24
(2024), Article A90 (<https://math.colgate.edu/~integers/y90/y90.pdf>).

The finite field `F_q` in Theorem 2 is represented by an arbitrary
finite field `K` of characteristic `p` and cardinality `p ^ ℓ`.
The action of the displayed polynomial is written directly as its
evaluated finite sum.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Algebra.PermutationPolynomialsWanted

/-- Ding and Zieve's Lemma 1: for a prime `p` and positive `t`,
`∑ a : ZMod p, a ^ t` is `-1` if `p - 1 ∣ t`, and `0` otherwise.

Source: Zhiguo Ding and Michael E. Zieve, "Permutation
Polynomials of the Form `∑_{n=1}^k h(n) X^n`", Lemma 1. -/
theorem_wanted sum_zmod_pow_eq_ite
    (p t : ℕ) [NeZero p] (hp : p.Prime) (ht : 0 < t) :
    (∑ a : ZMod p, a ^ t) = if (p - 1) ∣ t then -1 else 0

/-- Ding and Zieve's Theorem 1 (the result quoted from the earlier
paper): under the displayed congruences, the function
`c ↦ ∑ n ∈ [1,k], n ^ t * c ^ n` permutes `ZMod p`.

Source: Zhiguo Ding and Michael E. Zieve, "Permutation
Polynomials of the Form `∑_{n=1}^k h(n) X^n`", Theorem 1. -/
theorem_wanted bijective_sum_pow_mul_pow_zmod
    (p k t : ℕ) (hp : p.Prime) (hpodd : p % 2 = 1)
    (hk : 0 < k) (ht : 0 < t)
    (hkcong : k % (p * (p - 1)) = 1)
    (hcases : k % (p ^ 2) = 1 ∨ ¬(p - 1) ∣ t) :
    Function.Bijective
      (fun c : ZMod p =>
        ∑ n ∈ Finset.Icc 1 k, (n : ZMod p) ^ t * c ^ n)

/-- Ding and Zieve's Theorem 2: for `q = p ^ ℓ > 2` and
`k % (p * (q - 1)) = 1`, the polynomial action
`c ↦ ∑ n ∈ [1,k], h.eval n * c ^ n` is the identity on a finite
field of cardinality `q` if and only if `h.eval 1 = 1` and either
`k % p ^ 2 = 1` or
`∑ j ∈ [1, h.natDegree / (p - 1)], h.coeff (j * (p - 1)) = 0`.

Source: Zhiguo Ding and Michael E. Zieve, "Permutation
Polynomials of the Form `∑_{n=1}^k h(n) X^n`", Theorem 2. -/
theorem_wanted finiteField_sum_eval_mul_pow_eq_id_iff
    (K : Type*) [Field K] [Fintype K] (p ℓ : ℕ) [CharP K p]
    (hp : p.Prime) (hℓ : 0 < ℓ)
    (hcard : Fintype.card K = p ^ ℓ) (hq : 2 < p ^ ℓ)
    (k : ℕ) (hk : 0 < k)
    (hkcong : k % (p * (p ^ ℓ - 1)) = 1)
    (h : Polynomial K) :
    (∀ c : K, (∑ n ∈ Finset.Icc 1 k, h.eval (n : K) * c ^ n) = c) ↔
      h.eval 1 = 1 ∧
        (k % (p ^ 2) = 1 ∨
          (∑ j ∈ Finset.Icc 1 (h.natDegree / (p - 1)),
            h.coeff (j * (p - 1))) = 0)

end MathlibExt.Algebra.PermutationPolynomialsWanted
