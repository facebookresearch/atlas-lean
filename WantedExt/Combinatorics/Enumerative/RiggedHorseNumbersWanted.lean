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
`K = 1`).

Already in the library and not restated: Proposition 1 is
`MetaMathlibExt.stirlingMatrices_mutualInverse_and_lowerTriangular`, Lemma 3 is
`MetaMathlibExt.stirlingSecond_mul_factorial_eq_sum`, Proposition 5 is
`ArithmeticFunction.pow_carmichael`, Theorem 7 is
`MetaMathlibExt.rHorseNumber_eq_stirlingFirst_sum_fubini`, Corollary 8 is
`MetaMathlibExt.fubiniNumber_eq_factorial_sub_sum_signed_stirling`, and Corollary 9 is the
definition `MetaMathlibExt.fubiniNumber_eq_sum` together with Corollary 8. Corollary 12, the
eventual periodicity of the `r`-Fubini numbers modulo `K`, is proved as
`MetaMathlibExt.rFubini_add_carmichael_modEq` in
`MathlibExt.Combinatorics.Enumerative.RFubiniPeriodicity`, which this file re-exports.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import MathlibExt.Combinatorics.Enumerative.FubiniPeriods
public import MathlibExt.Combinatorics.Enumerative.RFubiniPeriodicity
public import MathlibExt.Combinatorics.Enumerative.StirlingDescPochhammer

namespace MetaMathlibExt

@[expose] public section

open ArithmeticFunction

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

end

end MetaMathlibExt
