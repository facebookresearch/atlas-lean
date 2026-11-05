/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Defs
public import Mathlib.Data.Nat.Prime.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Consecutive primes.** Natural numbers $p$ and $q$ are consecutive primes when $p$ and $q$
are prime, $p < q$, and every prime $r$ satisfies $r \le p$ or $q \le r$; that is, no prime
lies strictly between $p$ and $q$.

This is the usual meaning of successive primes $p_k, p_{k+1}$ used in the source papers.

Source: JIS concept `jis_sem_36fb078a6414434f9cc22b4a` ("consecutive prime").

Sources:
* <https://cs.uwaterloo.ca/journals/JIS/VOL25/Krizek/krizek3.tex>
* <https://cs.uwaterloo.ca/journals/JIS/VOL14/Noe/noe12.tex>
* <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.tex>
-/
def AreConsecutivePrimes (p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ ∀ r, Nat.Prime r → r ≤ p ∨ q ≤ r

/-- **Block of consecutive primes.** A list $l$ of natural numbers is a block of consecutive
primes when $l$ is nonempty, every entry of $l$ is prime, $l$ is strictly increasing, and every
two adjacent entries of $l$ are consecutive primes.

Source: see the sources cited on `AreConsecutivePrimes` for occurrences of blocks
`pₖ, pₖ₊₁, …, pₘ` of consecutive primes.
-/
def IsConsecutivePrimeBlock (l : List ℕ) : Prop :=
  l ≠ [] ∧ (∀ p ∈ l, Nat.Prime p) ∧ List.Pairwise (· < ·) l ∧
    ∀ x ∈ l.consecutivePairs, AreConsecutivePrimes x.1 x.2

/-- **Restricted block of consecutive primes.** Let $P$ be a predicate on natural numbers. A list
$l$ of natural numbers is a block of consecutive primes restricted by $P$ when $l$ is a block of
consecutive primes and every entry of $l$ satisfies $P$.

This covers, for example, the factorial- and primorial-bounded blocks in the source papers by
choosing the corresponding predicate $P$.
-/
def IsRestrictedConsecutivePrimeBlock (P : ℕ → Prop) (l : List ℕ) : Prop :=
  IsConsecutivePrimeBlock l ∧ ∀ p ∈ l, P p

end

end MetaMathlibExt
