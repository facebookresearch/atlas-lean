/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Quotients of a more general theorem of Wilson

Statements from Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", *INTEGERS* 25 (2025), Article A93
(<https://math.colgate.edu/~integers/z93/z93.pdf>).

Non-composite means `1` or prime.  Congruences for the rational
numbers `Z` and `Z+` are stated through the integer values whose
existence is asserted in the corresponding integrality theorems;
Theorem 6 is stated in the usual rational form that the numerator
of the difference is divisible by `p`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import MathlibExt.NumberTheory.WilsonQuotientPrimality
public import MathlibExt.NumberTheory.WilsonQuotients
public import MathlibExt.NumberTheory.WilsonQuotientsExistsIntEqWilsonQuotientZPlusTwoMulAndModEq
public import MathlibExt.NumberTheory.WilsonQuotientsExistsNatEqWilsonQuotientZPlusIff
public import MathlibExt.NumberTheory.WilsonQuotientsExistsIntEqWilsonQuotientZAndModEq

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.WilsonQuotientsWanted

/-- **The Wilson quotient sum is an integer.** For every natural number $n \ge 1$, Morozov's
Wilson quotient sum $Z(n)$ is an integer.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 1. -/
theorem_wanted exists_int_eq_wilsonQuotientZ
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ n

/-- **A Bernoulli–harmonic congruence for the sign-adjusted Wilson quotient sum.** Let $p$ be an
odd prime, let $B_m$ denote the Bernoulli numbers, and let $H_k = \sum_{j=1}^{k} 1/j$ denote the
harmonic numbers, with $H_0 = 0$. Then $p$ divides the numerator, in lowest terms, of the
rational number

$$Z^+(p) - \Bigl(B_{2(p-1)} - B_{p-1} - \sum_{k=0}^{p-1} (-1)^k H_k\Bigr),$$

where $Z^+(p)$ is Morozov's sign-adjusted Wilson quotient sum.

This is the congruence obtained by summing the paper's Equation (7). The printed simplification
of the alternating harmonic sum to $H_{p-1}/2$ is false already at $p = 3$.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 6 and Equation (7). -/
theorem_wanted prime_dvd_num_wilsonQuotientZPlus_sub_bernoulli_alternating
    (p : ℕ) (hp : p.Prime) (hpodd : p % 2 = 1) :
    (p : ℤ) ∣ (wilsonQuotientZPlus p -
      (bernoulli (2 * (p - 1)) - bernoulli (p - 1) -
        ∑ k ∈ Finset.range p, (-1 : ℚ) ^ k * harmonic k)).num

end MathlibExt.NumberTheory.WilsonQuotientsWanted
