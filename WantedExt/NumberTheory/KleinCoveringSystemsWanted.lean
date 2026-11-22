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

/-!
# Distinct covering systems with minimum modulus five, six and seven

Statements from Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and
Trifonov*, INTEGERS 26 (2026), Article A38 (arXiv `2508.18062`, TeX source read).

A covering system is a finite set of residue classes `a mod m` covering `ℤ`; it is encoded as
`classes : Finset (ℤ × ℕ)` of pairs `(a, m)` with `Int.IsCoveringSystem classes`. It is *distinct*
when no two classes share a modulus (`Set.InjOn Prod.snd`). "The smallest modulus is `m`" means
every modulus is `≥ m` and some modulus equals `m`; the least common multiple of the moduli is
`classes.lcm Prod.snd`.
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

/-- **A distinct covering system with moduli from 6 to 168.** There is a distinct covering
system, that is, a finite set of congruences $x \equiv r \pmod m$ with $r \in \mathbb{Z}$,
$m \in \mathbb{N}$ and no two with the same modulus, such that every integer satisfies at least
one of them, whose moduli all lie between $6$ and $168$ and include both $6$ and $168$.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Theorem 2 (`integers-2026-A38-thm-2`); the paper's witness is
due to Ognian Trifonov. -/
public theorem_wanted exists_distinct_covering_min_six_max_168 :
    ∃ classes : Finset (ℤ × ℕ), Int.IsCoveringSystem classes ∧
      Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)) ∧ (∀ c ∈ classes, 6 ≤ c.2 ∧ c.2 ≤ 168) ∧
      (∃ c ∈ classes, c.2 = 6) ∧ ∃ c ∈ classes, c.2 = 168

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

/-- **Discarding the classes whose modulus is divisible by a large prime power.** Let $C$ be a
distinct covering system: a finite set of congruences $x \equiv r \pmod m$ with
$r \in \mathbb{Z}$ and $m \in \mathbb{N}$ (where $x \equiv r \pmod 0$ means $x = r$), no two
with the same modulus, such that every integer satisfies at least one of them. Let
$B \in \mathbb{N}$ be at least every modulus of $C$, let $p$ be a prime and $a \ge 1$. If
$B < p^a (p + 1)$, then the congruences of $C$ whose modulus is not divisible by $p^a$ still
cover every integer.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 1 (`integers-2026-A38-lem-1`), quoting Krukenberg,
Corollary 2.3, and Dalton–Trifonov, Corollary 8. -/
public theorem_wanted isCoveringSystem_filter_not_dvd_of_lt (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)))
    (B : ℕ) (hB : ∀ c ∈ classes, c.2 ≤ B) {p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hpa : B < p ^ a * (p + 1)) :
    Int.IsCoveringSystem (classes.filter fun c => ¬ p ^ a ∣ c.2)

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

/-- **Translating a covering system.** Let $C$ be a covering system: a finite set of
congruences $x \equiv a_i \pmod{m_i}$ with $a_i \in \mathbb{Z}$ and $m_i \in \mathbb{N}$ (where
$x \equiv a_i \pmod 0$ means $x = a_i$) such that every integer satisfies at least one of them.
Then for every $t \in \mathbb{Z}$ the congruences $x \equiv a_i + t \pmod{m_i}$ also form a
covering system.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 3 (`integers-2026-A38-lem-3`). -/
public theorem_wanted isCoveringSystem_translate (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (t : ℤ) :
    Int.IsCoveringSystem (classes.image fun c => (c.1 + t, c.2))

/-- **Swapping two residues modulo a prime in a covering system.** Let $C$ be a covering system
with positive moduli: a finite set of congruences $x \equiv a \pmod m$ with $a \in \mathbb{Z}$
and $m \ge 1$ such that every integer satisfies at least one of them. Let $L$ be the least
common multiple of its moduli, $p$ a prime dividing $L$, and $a_1 < a_2 \le p - 1$ natural
numbers. For a prime $\ell$ write $\nu_\ell(L)$ for the exponent of $\ell$ in $L$, and let
$C_p(\alpha)$ be the set of congruences $x \equiv a \pmod m$ in $C$ with $p \mid m$ and
$a \equiv \alpha \pmod p$. Let $t \in \mathbb{Z}$ satisfy $t \equiv a_2 - a_1 \pmod{p^{\nu_p(L)}}$
and $t \equiv 0 \pmod{q^{\nu_q(L)}}$ for every prime $q \ne p$ dividing $L$. Then the
congruences of $C$ outside $C_p(a_1) \cup C_p(a_2)$, together with $x \equiv a + t \pmod m$ for
each $x \equiv a \pmod m$ in $C_p(a_1)$ and $x \equiv a - t \pmod m$ for each
$x \equiv a \pmod m$ in $C_p(a_2)$, form a covering system.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 4 (`integers-2026-A38-lem-4`), from the author's thesis,
Lemma 2.13. -/
public theorem_wanted isCoveringSystem_swap_residues_mod_prime (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (hpos : ∀ c ∈ classes, 0 < c.2) {L p : ℕ}
    (hL : L = classes.lcm Prod.snd) (hp : p.Prime) (hpL : p ∣ L) {a₁ a₂ : ℕ} (h₁₂ : a₁ < a₂)
    (h₂ : a₂ ≤ p - 1) (t : ℤ)
    (htp : t ≡ (a₂ : ℤ) - a₁ [ZMOD ((p ^ L.factorization p : ℕ) : ℤ)])
    (htq : ∀ q : ℕ, q.Prime → q ∣ L → q ≠ p → t ≡ 0 [ZMOD ((q ^ L.factorization q : ℕ) : ℤ)]) :
    Int.IsCoveringSystem
      ((classes.filter fun c => ¬ (p ∣ c.2 ∧ (c.1 ≡ a₁ [ZMOD p] ∨ c.1 ≡ a₂ [ZMOD p]))) ∪
        (classes.filter fun c => p ∣ c.2 ∧ c.1 ≡ a₁ [ZMOD p]).image (fun c => (c.1 + t, c.2)) ∪
        (classes.filter fun c => p ∣ c.2 ∧ c.1 ≡ a₂ [ZMOD p]).image (fun c => (c.1 - t, c.2)))

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
public theorem_wanted exists_covering_divisors_replace_largest_prime {m p q L : ℕ} (hp : p.Prime) (hmp : m ≤ p)
    (hpL : ¬ p ∣ L) (hq : q.Prime) (hqL : q ∣ L)
    (hpq : p < q) (hqmax : ∀ r : ℕ, r.Prime → r ∣ L → r ≤ q)
    (h : ∃ res : ℕ → ℤ, Int.IsCoveringSystem
      ((L.divisors.filter fun d => m ≤ d).image fun d => (res d, d))) :
    ∃ res : ℕ → ℤ, Int.IsCoveringSystem
      (((p ^ L.factorization q * (L / q ^ L.factorization q)).divisors.filter
        fun d => m ≤ d).image fun d => (res d, d))

end

end MetaMathlibExt
