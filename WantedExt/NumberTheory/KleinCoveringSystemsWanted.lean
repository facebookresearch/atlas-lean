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

/-- **Theorem 1** (Krukenberg's conjecture). If the smallest modulus of a distinct covering
system is `5`, then its largest modulus is at least `108`.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Theorem 1 (`integers-2026-A38-thm-1`). -/
public theorem_wanted exists_modulus_ge_108_of_distinct_covering_min_five
    (classes : Finset (ℤ × ℕ)) (hcov : Int.IsCoveringSystem classes)
    (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ))) (hmin : ∀ c ∈ classes, 5 ≤ c.2)
    (hfive : ∃ c ∈ classes, c.2 = 5) : ∃ c ∈ classes, 108 ≤ c.2

/-- **Theorem 2.** There is a distinct covering system with smallest modulus `6` and largest
modulus `168`.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Theorem 2 (`integers-2026-A38-thm-2`); the paper's witness is
due to Ognian Trifonov. -/
public theorem_wanted exists_distinct_covering_min_six_max_168 :
    ∃ classes : Finset (ℤ × ℕ), Int.IsCoveringSystem classes ∧
      Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)) ∧ (∀ c ∈ classes, 6 ≤ c.2 ∧ c.2 ≤ 168) ∧
      (∃ c ∈ classes, c.2 = 6) ∧ ∃ c ∈ classes, c.2 = 168

/-- **Theorem 3** (Dalton–Trifonov problem, `m = 5`). If the smallest modulus of a distinct
covering system is `5`, then the least common multiple of its moduli is at least `1440`.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Theorem 3 (`integers-2026-A38-thm-3`). -/
public theorem_wanted lcm_moduli_ge_1440_of_distinct_covering_min_five
    (classes : Finset (ℤ × ℕ)) (hcov : Int.IsCoveringSystem classes)
    (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ))) (hmin : ∀ c ∈ classes, 5 ≤ c.2)
    (hfive : ∃ c ∈ classes, c.2 = 5) : 1440 ≤ classes.lcm Prod.snd

/-- **Theorem 4** (`m = 6`). If the smallest modulus of a distinct covering system is `6`, then
the least common multiple of its moduli is at least `5040`.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Theorem 4 (`integers-2026-A38-thm-4`). -/
public theorem_wanted lcm_moduli_ge_5040_of_distinct_covering_min_six
    (classes : Finset (ℤ × ℕ)) (hcov : Int.IsCoveringSystem classes)
    (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ))) (hmin : ∀ c ∈ classes, 6 ≤ c.2)
    (hsix : ∃ c ∈ classes, c.2 = 6) : 5040 ≤ classes.lcm Prod.snd

/-- **Theorem 5.** There is a distinct covering system with smallest modulus `7` whose moduli
have least common multiple `15120`.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Theorem 5 (`integers-2026-A38-thm-5`). -/
public theorem_wanted exists_distinct_covering_min_seven_lcm_15120 :
    ∃ classes : Finset (ℤ × ℕ), Int.IsCoveringSystem classes ∧
      Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)) ∧ (∀ c ∈ classes, 7 ≤ c.2) ∧
      (∃ c ∈ classes, c.2 = 7) ∧ classes.lcm Prod.snd = 15120

/-- **Lemma 1** (Krukenberg; Dalton–Trifonov). Let `C` be a distinct covering system with all
moduli at most `B`, `p` prime and `a ≥ 1`. If `p^a (p + 1) > B`, the classes whose modulus is
divisible by `p^a` can be discarded and the rest still covers `ℤ`.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 1 (`integers-2026-A38-lem-1`), quoting Krukenberg,
Corollary 2.3, and Dalton–Trifonov, Corollary 8. -/
public theorem_wanted isCoveringSystem_filter_not_dvd_of_lt (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)))
    (B : ℕ) (hB : ∀ c ∈ classes, c.2 ≤ B) {p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hpa : B < p ^ a * (p + 1)) :
    Int.IsCoveringSystem (classes.filter fun c => ¬ p ^ a ∣ c.2)

/-- **Lemma 2** (Dalton–Trifonov). Let `C` be a covering system with positive moduli, `p` prime,
`a ≥ 1`, and suppose exactly `p` classes of `C` have modulus divisible by `p^a`, with moduli
`p^a m_1, …, p^a m_p`. Replacing these `p` classes by a single class with modulus
`p^{a-1} lcm(m_1, …, m_p)` (for a suitable residue) still gives a covering system.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 2 (`integers-2026-A38-lem-2`), quoting Dalton–Trifonov,
Corollary 9. -/
public theorem_wanted exists_isCoveringSystem_merge_prime_power (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (hpos : ∀ c ∈ classes, 0 < c.2) {p a : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hcard : (classes.filter fun c => p ^ a ∣ c.2).card = p) :
    ∃ r : ℤ, Int.IsCoveringSystem
      (insert (r, p ^ (a - 1) * (classes.filter fun c => p ^ a ∣ c.2).lcm fun c => c.2 / p ^ a)
        (classes.filter fun c => ¬ p ^ a ∣ c.2))

/-- **Lemma 3** (translation). If `{a_i mod m_i}` is a covering system and `t ∈ ℤ`, then
`{a_i + t mod m_i}` is a covering system.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 3 (`integers-2026-A38-lem-3`). -/
public theorem_wanted isCoveringSystem_translate (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (t : ℤ) :
    Int.IsCoveringSystem (classes.image fun c => (c.1 + t, c.2))

/-- **Lemma 4.** Let `C` be a covering system with positive moduli and `L` the least common
multiple of its moduli, `p` a prime dividing `L`, `0 ≤ a₁ < a₂ ≤ p - 1`, and
`C_p(α) = {a mod m ∈ C : p ∣ m, a ≡ α (mod p)}`. If `t ≡ a₂ - a₁ (mod p^{ν_p(L)})` and
`t ≡ 0 (mod q^{ν_q(L)})` for every other prime `q ∣ L`, then
`(C \ (C_p(a₁) ∪ C_p(a₂))) ∪ (C_p(a₁) + t) ∪ (C_p(a₂) - t)` is a covering system.

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

/-- **Lemma 5** (Mirsky–Newman). For a distinct covering system with all moduli at least `2`,
`∑ 1/m_i > 1`.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 5 (`integers-2026-A38-lem-5`), quoting Mirsky and
Newman. -/
public theorem_wanted one_lt_sum_inv_moduli_of_distinct_covering (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)))
    (htwo : ∀ c ∈ classes, 2 ≤ c.2) : (1 : ℚ) < ∑ c ∈ classes, (1 : ℚ) / c.2

/-- **Lemma 6.** Let `p ≥ m` be a prime, `p ∤ L`, and `q > p` the largest
prime dividing `L`. If some distinct covering system uses as moduli exactly the divisors of `L`
that are at least `m`, then some distinct covering system uses exactly the divisors of
`p^{ν_q(L)} L / q^{ν_q(L)}` that are at least `m`.

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
