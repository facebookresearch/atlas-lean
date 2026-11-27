/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Fermat
public import Mathlib.NumberTheory.FermatPsp
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import MathlibExt.Data.Set.Density
public import MathlibExt.NumberTheory.FermatNumberStrongPseudoprimeAddSub
public import MathlibExt.NumberTheory.FermatNumberStrongPseudoprimeTwoPow
public import MathlibExt.NumberTheory.FermatPseudoprimeBaseCount
public import MathlibExt.NumberTheory.StrongPseudoprime
public import MathlibExt.NumberTheory.StrongPseudoprimeBaseCount
public import MathlibExt.NumberTheory.StrongPseudoprimePrimitivePart
public import MathlibExt.NumberTheory.StrongPseudoprimePrimitivePartPowers
public import MathlibExt.NumberTheory.StrongPseudoprimeZPowNeg
public import MathlibExt.NumberTheory.PseudoprimeBasesFermatNumbersFermatNumberStrongPseudoprimeBasesSubgroup

/-!
# Pseudoprime bases and Fermat numbers

Statements from Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24
(2024), Article A23. The paper's `F_n` (pseudoprime bases `1 ≤ b < n`) is written with
Mathlib's `Nat.FermatPsp`, and its `R_n` (strong pseudoprime bases `1 ≤ b < n`) with the
predicate `MetaMathlibExt.IsStrongPseudoprime` (`MathlibExt/NumberTheory/StrongPseudoprime.lean`),
which follows the paper's Congruences (2) and (3). Theorem 8
(`MetaMathlibExt.fermatNumber_strongPseudoprime_bases_subgroup`) is proved in
`MathlibExt.NumberTheory.PseudoprimeBasesFermatNumbersFermatNumberStrongPseudoprimeBasesSubgroup`.
Theorems 1 and 9 (polynomial-time factoring algorithms) are not
stated; see the source audit table.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Products of two distinct primes have a square number of Fermat pseudoprime bases.** Let
$p$ and $q$ be distinct primes. Then the number of integers $b$ with $1 \le b < pq$ such that
$pq$ is a Fermat pseudoprime to the base $b$, that is, $b^{pq-1} \equiv 1 \pmod{pq}$, is a perfect
square.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 1 (`integers-2024-A23-cor-1`). -/
public theorem_wanted isSquare_card_fermatPsp_bases_mul_of_prime {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) :
    IsSquare {b : ℕ | 1 ≤ b ∧ b < p * q ∧ Nat.FermatPsp (p * q) b}.ncard

/-- **When the strong pseudoprime bases form a subgroup.** Let $n > 1$ be an odd number that is
not prime, let $r$ be the number of distinct prime factors of $n$, and let $v$ be the least
exponent of $2$ in $p - 1$ over the prime factors $p$ of $n$. Then the following are equivalent:
(a) there is a subgroup of the unit group $(\mathbb{Z}/n\mathbb{Z})^\times$ whose elements are
exactly the units $u$ such that $n$ is a strong pseudoprime to the base $u$; (b) the number of
$b$ with $1 \le b < n$ such that $n$ is a strong pseudoprime to the base $b$ divides the number
of $b$ with $1 \le b < n$ such that $n$ is a Fermat pseudoprime to the base $b$, that is,
$n \mid b^{n-1} - 1$; (c) $v = 1$ or $r = 1$; (d) some prime $p \equiv 3 \pmod 4$ divides $n$,
or $n$ is a prime power.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 4 (`integers-2024-A23-thm-4`). -/
public theorem_wanted strongPseudoprime_bases_subgroup_tfae {n : ℕ} (hn : 1 < n)
    (hcomp : ¬n.Prime) (hodd : Odd n) :
    let r := n.primeFactors.card
    let v := sInf ((fun p => (p - 1).factorization 2) '' (n.primeFactors : Set ℕ))
    [∃ H : Subgroup (ZMod n)ˣ, ∀ u : (ZMod n)ˣ, u ∈ H ↔ IsStrongPseudoprime n (u : ZMod n),
      {b : ℕ | 1 ≤ b ∧ b < n ∧ IsStrongPseudoprime n b}.ncard ∣
        {b : ℕ | 1 ≤ b ∧ b < n ∧ Nat.FermatPsp n b}.ncard,
      v = 1 ∨ r = 1,
      (∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3) ∨ IsPrimePow n].TFAE

/-- **Strong pseudoprime bases almost always form a subgroup.** The set of odd composite natural
numbers $n$ for which the units $b$ of $\mathbb{Z}/n\mathbb{Z}$ such that $n$ is a strong
pseudoprime to the base $b$ do not form a subgroup of the unit group has natural density $0$.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 2 (`integers-2024-A23-cor-2`). -/
public theorem_wanted hasDensity_zero_strongPseudoprime_bases_not_subgroup :
    Set.HasDensity {n : ℕ | 1 < n ∧ ¬n.Prime ∧ Odd n ∧
      ¬∃ H : Subgroup (ZMod n)ˣ, ∀ u : (ZMod n)ˣ, u ∈ H ↔ IsStrongPseudoprime n (u : ZMod n)} 0

/-- **The subgroup criteria for strong pseudoprime bases hold almost always.** For an odd
composite natural number $n$, let $r$ be the number of distinct prime divisors of $n$, let $v$ be
the least of the $2$-adic valuations of $p - 1$ over the prime divisors $p$ of $n$, and consider
the conditions: (a) the units $b$ of $\mathbb{Z}/n\mathbb{Z}$ such that $n$ is a strong
pseudoprime to the base $b$ form a subgroup of the unit group; (b) the number of integers $b$
with $1 \le b < n$ to which $n$ is a strong pseudoprime divides the number of integers $b$ with
$1 \le b < n$ to which $n$ is a Fermat pseudoprime; (c) $v = 1$ or $r = 1$; (d) some prime
$p \equiv 3 \pmod 4$ divides $n$, or $n$ is a prime power. Then the set of odd composite natural
numbers $n$ for which at least one of (a)–(d) fails has natural density $0$.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 3 (`integers-2024-A23-cor-3`). -/
public theorem_wanted hasDensity_zero_strongPseudoprime_bases_conditions_fail :
    Set.HasDensity {n : ℕ | 1 < n ∧ ¬n.Prime ∧ Odd n ∧
      ¬((∃ H : Subgroup (ZMod n)ˣ, ∀ u : (ZMod n)ˣ, u ∈ H ↔ IsStrongPseudoprime n (u : ZMod n)) ∧
        {b : ℕ | 1 ≤ b ∧ b < n ∧ IsStrongPseudoprime n b}.ncard ∣
          {b : ℕ | 1 ≤ b ∧ b < n ∧ Nat.FermatPsp n b}.ncard ∧
        (sInf ((fun p => (p - 1).factorization 2) '' (n.primeFactors : Set ℕ)) = 1 ∨
          n.primeFactors.card = 1) ∧
        ((∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3) ∨ IsPrimePow n))} 0

end

end MetaMathlibExt
