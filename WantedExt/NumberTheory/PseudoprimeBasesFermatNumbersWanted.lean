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
public import MathlibExt.NumberTheory.StrongPseudoprimeZPowNeg

/-!
# Pseudoprime bases and Fermat numbers

Statements from Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24
(2024), Article A23. The paper's `F_n` (pseudoprime bases `1 ≤ b < n`) is written with
Mathlib's `Nat.FermatPsp`, and its `R_n` (strong pseudoprime bases `1 ≤ b < n`) with the
predicate `MetaMathlibExt.IsStrongPseudoprime` (`MathlibExt/NumberTheory/StrongPseudoprime.lean`),
which follows the paper's Congruences (2) and (3). Theorems 1 and 9 (polynomial-time factoring
algorithms) are not
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

/-- **Composite divisors of primitive parts without the intrinsic factor are strong pseudoprimes to
every power of the base.** Let $b > 1$ and $m > 2$ be natural numbers, write $\Phi_j(b)$ for the
value at $b$ of the $j$-th cyclotomic polynomial over $\mathbb{Z}$, and let $c > 1$ be a natural
number that is not prime. If $c$ divides $\Phi_m(b) / \gcd(\Phi_m(b), m)$ or
$\Phi_{2m}(b) / \gcd(\Phi_{2m}(b), m)$, then for every unit $u$ of $\mathbb{Z}/c\mathbb{Z}$ equal
to the residue class of $b$ and every integer $t$, $c$ is a strong pseudoprime to the base $u^t$.

These two quotients are the primitive parts of $b^m - 1$ and $b^m + 1$ with the intrinsic factor
removed.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 4 (`integers-2024-A23-cor-4`). -/
public theorem_wanted isStrongPseudoprime_zpow_of_dvd_primitivePart {b m c : ℕ} (hb : 1 < b)
    (hm : 2 < m) (hc : 1 < c) (hcomp : ¬c.Prime) :
    let Φ : ℕ → ℤ := fun j => (Polynomial.cyclotomic j ℤ).eval (b : ℤ)
    ((c : ℤ) ∣ Φ m / (Int.gcd (Φ m) m : ℤ) ∨ (c : ℤ) ∣ Φ (2 * m) / (Int.gcd (Φ (2 * m)) m : ℤ)) →
      ∀ u : (ZMod c)ˣ, (u : ZMod c) = b → ∀ t : ℤ,
        IsStrongPseudoprime c ((u ^ t : (ZMod c)ˣ) : ZMod c)

/-- **A subgroup of strong pseudoprime bases of a composite Fermat number.** Let $k$ be a natural
number such that the Fermat number $F_k = 2^{2^k} + 1$ is composite, and let $S_k$ be the set of
residues modulo $F_k$ of the form $2^t$, $2^{2^{k-1}+t} + 2^t$ or $2^{2^{k-1}+t} - 2^t$ with $t$ a
natural number. Then the units of $\mathbb{Z}/F_k\mathbb{Z}$ that lie in $S_k$ form a subgroup of
the unit group of order $2^{k+2}$, and $F_k$ is a strong pseudoprime to every base in $S_k$.

The source also asserts that this subgroup is isomorphic to $C_{2^{k+1}} \times C_2$. This is
false: the residue $2^{16} + 1$ has multiplicative order $128 = 2^{k+2}$ modulo $F_5$, so the
subgroup is cyclic for $k = 5$.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 8 (`integers-2024-A23-thm-8`). -/
public theorem_wanted fermatNumber_strongPseudoprime_bases_subgroup {k : ℕ}
    (hk : ¬(Nat.fermatNumber k).Prime) :
    let S : Set (ZMod (Nat.fermatNumber k)) :=
      {x | (∃ t : ℕ, x = 2 ^ t) ∨
        ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨ x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t}
    ∃ H : Subgroup (ZMod (Nat.fermatNumber k))ˣ,
      (∀ u : (ZMod (Nat.fermatNumber k))ˣ, u ∈ H ↔ (u : ZMod (Nat.fermatNumber k)) ∈ S) ∧
      Nat.card H = 2 ^ (k + 2) ∧
      ∀ x ∈ S, IsStrongPseudoprime (Nat.fermatNumber k) x

end

end MetaMathlibExt
