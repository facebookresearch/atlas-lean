/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rigged horse numbers and the modular periodicity of Fubini numbers

Statements from Benjamin Schreyer, "Rigged Horse Numbers and their Modular
Periodicity", *Journal of Integer Sequences* 28 (2025), Article 25.4.1
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Schreyer/schreyer7.html>; arXiv:2409.03799v2).

Fubini numbers are MathlibExt's `fubiniNumber`, the signed Stirling numbers of the first kind
are MathlibExt's `signedStirlingFirst`, and the Carmichael function `λ` is Mathlib's
`ArithmeticFunction.carmichael`. For `K = p₁^R₁ ⋯ p_N^R_N`, the paper's
`R = max(R₁, …, R_N)` is `K.factorization.support.sup K.factorization` (so `R = 0` for
`K = 1`). The paper's `r`-Fubini number `F_r(n)` (Definition 3: weak orderings of an
`n`-element set in which `r` distinguished elements are pairwise untied) is the number of
surjections `f : Fin n → Fin k`, summed over `k`, that are injective on the elements of value
`< r`.

Already in the library and not restated: Proposition 1 is
`MetaMathlibExt.stirlingMatrices_mutualInverse_and_lowerTriangular`, Lemma 3 is
`MetaMathlibExt.stirlingSecond_mul_factorial_eq_sum`, Proposition 5 is
`ArithmeticFunction.pow_carmichael`, Theorem 7 is
`MetaMathlibExt.rHorseNumber_eq_stirlingFirst_sum_fubini`, Corollary 8 is
`MetaMathlibExt.fubiniNumber_eq_factorial_sub_sum_signed_stirling`, and Corollary 9 is the
definition `MetaMathlibExt.fubiniNumber_eq_sum` together with Corollary 8.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.FubiniNumber
public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst

namespace MetaMathlibExt

@[expose] public section

open Polynomial ArithmeticFunction

/-- **Falling factorial in terms of signed Stirling numbers.** For every natural number $n$, the
identity of polynomials with integer coefficients
$$x (x - 1) \cdots (x - n + 1) = \sum_{k=0}^{n} s(n, k)\, x^k$$
holds, where $s(n, k)$ is the signed Stirling number of the first kind.

Source: Benjamin Schreyer, *Rigged Horse Numbers and their Modular Periodicity*, Journal of
Integer Sequences 28 (2025), Article 25.4.1, Proposition 2 (`jis-2025-25.4.1-prop-2`). -/
public theorem_wanted descPochhammer_eq_sum_signedStirlingFirst (n : ℕ) :
    descPochhammer ℤ n =
      ∑ k ∈ Finset.range (n + 1), C (signedStirlingFirst n k) * X ^ k

/-- **A Carmichael congruence for all residues modulo $K$.** Let $K$ be a natural number, let
$\lambda(K)$ be the value of the Carmichael function at $K$, and let $R$ be the largest exponent
in the prime factorization of $K$ ($R = 0$ for $K \le 1$). Then
$a^R \equiv a^{\lambda(K) + R} \pmod K$ for every natural number $a < K$.

Source: Benjamin Schreyer, *Rigged Horse Numbers and their Modular Periodicity*, Journal of
Integer Sequences 28 (2025), Article 25.4.1, Proposition 4 (`jis-2025-25.4.1-prop-4`). -/
public theorem_wanted pow_add_carmichael_modEq_of_lt (K a : ℕ) (ha : a < K) :
    let R := K.factorization.support.sup K.factorization
    a ^ R ≡ a ^ (carmichael K + R) [MOD K]

/-- **Eventual periodicity of the Fubini numbers modulo $K$.** Let $K$ be a natural number, let
$\lambda(K)$ be the value of the Carmichael function at $K$, and let $R$ be the largest exponent
in the prime factorization of $K$ ($R = 0$ for $K \le 1$). Then the Fubini numbers $F(n)$
satisfy $F(n + \lambda(K)) \equiv F(n) \pmod K$ for every natural number $n \ge R$.

Source: Benjamin Schreyer, *Rigged Horse Numbers and their Modular Periodicity*, Journal of
Integer Sequences 28 (2025), Article 25.4.1, Corollary 10 (`jis-2025-25.4.1-cor-10`). -/
public theorem_wanted fubiniNumber_add_carmichael_modEq (K n : ℕ)
    (hn : K.factorization.support.sup K.factorization ≤ n) :
    fubiniNumber (n + carmichael K) ≡ fubiniNumber n [MOD K]

/-- **Eventual periods of the Fubini numbers modulo an odd number.** Let $K$ be an odd natural
number and let $\lambda(K)$ be the value of the Carmichael function at $K$. Then a natural number
$p$ is divisible by $\lambda(K)$ if and only if there is a natural number $N$ such that the Fubini
numbers $F(n)$ satisfy $F(n + p) \equiv F(n) \pmod K$ for all $n \ge N$. In particular, the
eventual period of the Fubini numbers modulo $K$ is exactly $\lambda(K)$.

Source: Benjamin Schreyer, *Rigged Horse Numbers and their Modular Periodicity*, Journal of
Integer Sequences 28 (2025), Article 25.4.1, Corollary 11 (`jis-2025-25.4.1-cor-11`). -/
public theorem_wanted fubiniNumber_eventuallyPeriodic_iff_carmichael_dvd (K : ℕ) (hK : Odd K)
    (p : ℕ) :
    (∃ N, ∀ n ≥ N, fubiniNumber (n + p) ≡ fubiniNumber n [MOD K]) ↔ carmichael K ∣ p

/-- **Eventual periodicity of the $r$-Fubini numbers modulo $K$.** For a natural number $r \ge 1$
and a natural number $m$, let $F_r(m)$ be the number of pairs $(k, f)$ of a natural number
$k \le m$ and a surjection $f : \{0, \dots, m - 1\} \to \{0, \dots, k - 1\}$ that is injective on
the elements less than $r$; equivalently, $F_r(m)$ counts the weak orderings of $m$ elements in
which the elements less than $r$ are pairwise untied. Let $K$ be a natural number, let
$\lambda(K)$ be the value of the Carmichael function at $K$, and let $R$ be the largest exponent
in the prime factorization of $K$ ($R = 0$ for $K \le 1$). Then
$F_r(n + \lambda(K)) \equiv F_r(n) \pmod K$ for every natural number $n \ge r - 1 + R$.

Source: Benjamin Schreyer, *Rigged Horse Numbers and their Modular Periodicity*, Journal of
Integer Sequences 28 (2025), Article 25.4.1, Corollary 12 (`jis-2025-25.4.1-cor-12`). -/
public theorem_wanted rFubini_add_carmichael_modEq (K r n : ℕ) (hr : 1 ≤ r)
    (hn : r - 1 + K.factorization.support.sup K.factorization ≤ n) :
    let rFubini : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1),
      Nat.card { f : Fin m → Fin k // Function.Surjective f ∧
        ∀ i j : Fin m, (i : ℕ) < r → (j : ℕ) < r → f i = f j → i = j }
    rFubini (n + carmichael K) ≡ rFubini n [MOD K]

end

end MetaMathlibExt
