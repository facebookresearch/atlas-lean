/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Factorization into composed cyclotomic polynomials

For a product of prime powers `n`, we factor `X ^ n - 1` by successively composing
prime cyclotomic polynomials with powers of `X`.
-/

namespace MetaMathlibExt

open Polynomial

private theorem factor_prime_power {p : ℕ} [Fact p.Prime] (r a : ℕ) :
    (X ^ (r * p ^ a) - 1 : ℤ[X]) =
      (X ^ r - 1) * ∏ j ∈ Finset.Icc 1 a,
        (cyclotomic p ℤ).comp (X ^ (r * p ^ (j - 1))) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.prod_Icc_succ_top (Nat.succ_pos a), ← mul_assoc, ← ih, Nat.add_sub_cancel,
      pow_succ p a, ← Nat.mul_assoc, pow_mul (X : ℤ[X]) (r * p ^ a) p]
    simpa only [mul_comp, sub_comp, X_comp, pow_comp, one_comp, mul_comm] using
      (congrArg (fun f : ℤ[X] => f.comp (X ^ (r * p ^ a)))
        (cyclotomic_prime_mul_X_sub_one ℤ p)).symm

/-- **Factorization into composed cyclotomic polynomials.** Let $x$ be the indeterminate of the
polynomial ring $\mathbb{Z}[x]$. Let $m$ be a natural number, let $p_1, \dots, p_m$ be primes,
not necessarily distinct, let $a_1, \dots, a_m$ be natural numbers, and put
$n = \prod_{i=1}^m p_i^{a_i}$. For $1 \le i \le m$ let $x_i = x^{N_i}$ with
$N_i = \prod_{1 \le r < i} p_r^{a_r}$. Then
$$x^n - 1 = (x - 1) \prod_{i=1}^m \prod_{j=1}^{a_i} \Phi_{p_i}(x_i^{p_i^{j-1}}),$$
where $\Phi_p$ is the $p$-th cyclotomic polynomial over $\mathbb{Z}$ and $\Phi_{p_i}(\cdot)$
denotes composition of polynomials.

The source takes the prime factorization of $n$; the identity needs only that each $p_i$ is
prime. The definition of $x_i$ follows the arXiv version of the source (arXiv:2412.00010),
which the journal statement refers to as "$x_k$ as above".

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 4 (`integers-2026-A95-prop-4`). -/
public theorem X_pow_sub_one_eq_mul_prod_cyclotomic_comp (m : ℕ) (p a : ℕ → ℕ)
    (hp : ∀ i ∈ Finset.Icc 1 m, (p i).Prime) :
    (X ^ (∏ i ∈ Finset.Icc 1 m, p i ^ a i) - 1 : ℤ[X]) =
      (X - 1) * ∏ i ∈ Finset.Icc 1 m, ∏ j ∈ Finset.Icc 1 (a i),
        (cyclotomic (p i) ℤ).comp (X ^ ((∏ r ∈ Finset.Ico 1 i, p r ^ a r) * p i ^ (j - 1))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have : Fact (p (m + 1)).Prime := ⟨hp _ (Finset.mem_Icc.mpr ⟨Nat.succ_pos m, le_rfl⟩)⟩
    have hprev := ih fun i hi => hp i (Finset.Icc_subset_Icc_right (Nat.le_succ m) hi)
    rw [Finset.prod_Icc_succ_top (Nat.succ_pos m), Finset.prod_Icc_succ_top (Nat.succ_pos m),
      Finset.Ico_add_one_right_eq_Icc, ← mul_assoc, ← hprev]
    exact factor_prime_power _ _

end MetaMathlibExt
