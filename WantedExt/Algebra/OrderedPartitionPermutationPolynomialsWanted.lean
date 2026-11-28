/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSum
public import MathlibExt.FieldTheory.Finite.DilatedPowerSumPermutationPolynomial
public import MathlibExt.FieldTheory.Finite.MonomialPermutationPolynomial
public import MathlibExt.FieldTheory.Finite.OrderedPartitionCongruence
public import MathlibExt.FieldTheory.Finite.PermutationPolynomial
public import MathlibExt.FieldTheory.Finite.PowerSumCriterion
public import MathlibExt.FieldTheory.Finite.PowerWeightedGeometricSum
public import MathlibExt.FieldTheory.Finite.ShiftedPowerSumPermutationPolynomial

/-!
# Permutation polynomials of the form `∑ n^t X^(n+a)` and related lemmas

Statements from Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on
Ordered Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, about
permutation polynomials over `𝔽_p`. Permutation polynomials use MathlibExt's
`Polynomial.IsPermutationPolynomial` (bijective evaluation map).

The power-sum criterion `injective_iff_sum_pow_eq` is proved in
`MathlibExt.FieldTheory.Finite.PowerSumCriterion`, which this module imports.
Proved in `MathlibExt.FieldTheory.Finite.MonomialPermutationPolynomial`, also imported here:
the monomial criterion the paper quotes (`isPermutationPolynomial_X_pow_iff_coprime`).
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Vishwakarma–Singh congruence for ordered partitions into multiples.** Let $p$ be an odd
prime and let $a, k, s, t$ be positive integers with $\gcd(a, p - 1) = 1$, $s \le p - 2$ and
$k \equiv 1 \pmod{p(p-1)}$, such that $p^2 \mid k - 1$ whenever $p - 1 \mid t$. Let
$\mu = \lfloor aks/(p - 1) \rfloor$. Then

$$\sum_{j=1}^{\mu} \sum_{\omega} (\omega_1 \cdots \omega_s)^t \equiv 0 \pmod{p},$$

where for each $j$ the inner sum runs over all $s$-tuples $\omega = (\omega_1, \dots, \omega_s)$
with entries in $\{an : 1 \le n \le k\}$ and $\omega_1 + \cdots + \omega_s = j(p - 1)$.

The source states this with two differences. It assumes $s \not\equiv 0 \pmod{p}$ in place of
$s \le p - 2$; with that hypothesis the claim fails, e.g. for $a = 1$, $p = 3$, $k = 7$, $s = 2$,
$t = 1$. It takes $\mu = \lfloor ks/(p - 1) \rfloor$; with that bound the claim fails for $a > 1$,
e.g. for $p = 5$, $a = 3$, $k = 21$, $s = t = 1$ the sum is $12$. The bound
$\lfloor aks/(p - 1) \rfloor$ covers every multiple of $p - 1$ up to $aks$, the degree of the
$s$-th power of $\sum_{n=1}^{k} (an)^t X^{an}$, to which the proof applies Hermite's criterion.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 4
(`integers-2024-A12-cor-4`). -/
public theorem_wanted prime_dvd_sum_compositions_mul_prod_pow {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {a k s t : ℕ} (ha : 0 < a) (hap : a.Coprime (p - 1)) (hk : 0 < k) (hs : 0 < s)
    (hsp : s ≤ p - 2) (ht : 0 < t) (hkcong : k ≡ 1 [MOD p * (p - 1)])
    (hcases : (p - 1) ∣ t → p ^ 2 ∣ k - 1) :
    p ∣ ∑ j ∈ Finset.Icc 1 (a * k * s / (p - 1)),
      ∑ ω ∈ (Fintype.piFinset fun _ : Fin s => (Finset.Icc 1 k).image (a * ·)).filter
          (fun ω => ∑ i, ω i = j * (p - 1)),
        (∏ i, ω i) ^ t

end

end MetaMathlibExt
