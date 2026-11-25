/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.NumberTheory.CoveringSystem
public import MathlibExt.NumberTheory.CoveringSystem.DiscardPrimePower
public import MathlibExt.NumberTheory.CoveringSystem.SwapResidues
public import MathlibExt.NumberTheory.CoveringSystem.Translate
public import MathlibExt.NumberTheory.CoveringSystem.TrifonovCovering

/-!
# Distinct covering systems with minimum modulus five, six and seven

Statements from Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and
Trifonov*, INTEGERS 26 (2026), Article A38 (arXiv `2508.18062`, TeX source read).

A covering system is a finite set of residue classes `a mod m` covering `ℤ`; it is encoded as
`classes : Finset (ℤ × ℕ)` of pairs `(a, m)` with `Int.IsCoveringSystem classes`. It is *distinct*
when no two classes share a modulus (`Set.InjOn Prod.snd`). "The smallest modulus is `m`" means
every modulus is `≥ m` and some modulus equals `m`; the least common multiple of the moduli is
`classes.lcm Prod.snd`.

Theorem 2, `exists_distinct_covering_min_six_max_168`, is proved in
`MathlibExt.NumberTheory.CoveringSystem.TrifonovCovering`, which this module imports.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Krukenberg's conjecture for minimum modulus five.** Let $C$ be a distinct covering
system: a finite set of congruences $x \equiv r \pmod m$ with $r \in \mathbb{Z}$ and
$m \in \mathbb{N}$, no two with the same modulus, such that every integer satisfies at least one
of them. If every modulus of $C$ is at least $5$ and some modulus equals $5$, then some modulus
of $C$ is at least $108$.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Theorem 1 (`integers-2026-A38-thm-1`). -/
public theorem_wanted exists_modulus_ge_108_of_distinct_covering_min_five
    (classes : Finset (ℤ × ℕ)) (hcov : Int.IsCoveringSystem classes)
    (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ))) (hmin : ∀ c ∈ classes, 5 ≤ c.2)
    (hfive : ∃ c ∈ classes, c.2 = 5) : ∃ c ∈ classes, 108 ≤ c.2

/-- **Least common multiple of a covering system with minimum modulus five.** Let $C$ be a
distinct covering system: a finite set of congruences $x \equiv r \pmod m$ with
$r \in \mathbb{Z}$ and $m \in \mathbb{N}$, no two with the same modulus, such that every integer
satisfies at least one of them. If every modulus of $C$ is at least $5$ and some modulus equals
$5$, then the least common multiple of the moduli of $C$ is at least $1440$.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Theorem 3 (`integers-2026-A38-thm-3`). -/
public theorem_wanted lcm_moduli_ge_1440_of_distinct_covering_min_five
    (classes : Finset (ℤ × ℕ)) (hcov : Int.IsCoveringSystem classes)
    (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ))) (hmin : ∀ c ∈ classes, 5 ≤ c.2)
    (hfive : ∃ c ∈ classes, c.2 = 5) : 1440 ≤ classes.lcm Prod.snd

/-- **Least common multiple of a covering system with minimum modulus six.** Let $C$ be a
distinct covering system: a finite set of congruences $x \equiv r \pmod m$ with
$r \in \mathbb{Z}$ and $m \in \mathbb{N}$, no two with the same modulus, such that every integer
satisfies at least one of them. If every modulus of $C$ is at least $6$ and some modulus equals
$6$, then the least common multiple of the moduli of $C$ is at least $5040$.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Theorem 4 (`integers-2026-A38-thm-4`). -/
public theorem_wanted lcm_moduli_ge_5040_of_distinct_covering_min_six
    (classes : Finset (ℤ × ℕ)) (hcov : Int.IsCoveringSystem classes)
    (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ))) (hmin : ∀ c ∈ classes, 6 ≤ c.2)
    (hsix : ∃ c ∈ classes, c.2 = 6) : 5040 ≤ classes.lcm Prod.snd

/-- **A distinct covering system with minimum modulus 7 and moduli of lcm 15120.** There is a
distinct covering system, that is, a finite set of congruences $x \equiv r \pmod m$ with
$r \in \mathbb{Z}$, $m \in \mathbb{N}$ and no two with the same modulus, such that every
integer satisfies at least one of them, whose moduli are all at least $7$, include $7$, and have
least common multiple $15120$.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Theorem 5 (`integers-2026-A38-thm-5`). -/
public theorem_wanted exists_distinct_covering_min_seven_lcm_15120 :
    ∃ classes : Finset (ℤ × ℕ), Int.IsCoveringSystem classes ∧
      Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)) ∧ (∀ c ∈ classes, 7 ≤ c.2) ∧
      (∃ c ∈ classes, c.2 = 7) ∧ classes.lcm Prod.snd = 15120

/-- **Merging the p classes whose modulus is divisible by a prime power.** Let $C$ be a
covering system with positive moduli: a finite set of congruences $x \equiv r \pmod m$ with
$r \in \mathbb{Z}$ and $m \ge 1$ such that every integer satisfies at least one of them. Let $p$
be a prime and $a \ge 1$, and suppose exactly $p$ congruences of $C$ have modulus divisible by
$p^a$, with moduli $p^a m_1, \dots, p^a m_p$. Then for some $r \in \mathbb{Z}$, replacing these
$p$ congruences by the single congruence $x \equiv r \pmod{p^{a-1} \operatorname{lcm}(m_1,
\dots, m_p)}$ still gives a covering system.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 2 (`integers-2026-A38-lem-2`), quoting Dalton–Trifonov,
Corollary 9. -/
public theorem_wanted exists_isCoveringSystem_merge_prime_power (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (hpos : ∀ c ∈ classes, 0 < c.2) {p a : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hcard : (classes.filter fun c => p ^ a ∣ c.2).card = p) :
    ∃ r : ℤ, Int.IsCoveringSystem
      (insert (r, p ^ (a - 1) * (classes.filter fun c => p ^ a ∣ c.2).lcm fun c => c.2 / p ^ a)
        (classes.filter fun c => ¬ p ^ a ∣ c.2))

/-- **Mirsky–Newman bound for distinct covering systems.** Let $a_1 \bmod m_1, \dots,
a_k \bmod m_k$ be residue classes that cover $\mathbb{Z}$, that is, every integer lies in at
least one of them. If the moduli $m_1, \dots, m_k$ are pairwise distinct and all at least $2$,
then $\sum_{i=1}^{k} 1/m_i > 1$.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 5 (`integers-2026-A38-lem-5`), quoting Mirsky and
Newman. -/
public theorem_wanted one_lt_sum_inv_moduli_of_distinct_covering (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)))
    (htwo : ∀ c ∈ classes, 2 ≤ c.2) : (1 : ℚ) < ∑ c ∈ classes, (1 : ℚ) / c.2

/-- **Replacing the largest prime factor of the modulus set.** Let $m, L \in \mathbb{N}$, let
$p \ge m$ be a prime with $p \nmid L$, let $q > p$ be the largest prime dividing $L$, and write
$\nu_q(L)$ for the exponent of $q$ in $L$. Suppose there are residues $r_d \in \mathbb{Z}$, one
for each divisor $d \ge m$ of $L$, such that every integer $x$ satisfies $x \equiv r_d \pmod d$
for some such $d$. Then the same holds with $L$ replaced by $p^{\nu_q(L)} L / q^{\nu_q(L)}$:
there are residues $s_d \in \mathbb{Z}$, one for each divisor $d \ge m$ of
$p^{\nu_q(L)} L / q^{\nu_q(L)}$, such that every integer $x$ satisfies $x \equiv s_d \pmod d$
for some such $d$.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 6 (`integers-2026-A38-lem-6`). -/
public theorem_wanted exists_covering_divisors_replace_largest_prime {m p q L : ℕ}
    (hp : p.Prime) (hmp : m ≤ p) (hpL : ¬ p ∣ L) (hq : q.Prime) (hqL : q ∣ L)
    (hpq : p < q) (hqmax : ∀ r : ℕ, r.Prime → r ∣ L → r ≤ q)
    (h : ∃ res : ℕ → ℤ, Int.IsCoveringSystem
      ((L.divisors.filter fun d => m ≤ d).image fun d => (res d, d))) :
    ∃ res : ℕ → ℤ, Int.IsCoveringSystem
      (((p ^ L.factorization q * (L / q ^ L.factorization q)).divisors.filter
        fun d => m ≤ d).image fun d => (res d, d))

end

end MetaMathlibExt
