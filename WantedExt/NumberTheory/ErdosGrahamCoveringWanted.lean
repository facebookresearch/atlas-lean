/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A question of Erdős and Graham on covering systems

Statement from Sarosh Adenwalla, "A Question of Erdős
and Graham on Covering Systems", *INTEGERS* 26 (2026),
Article A52
(<https://math.colgate.edu/~integers/vol26.html>).

Theorem 3.2: a non-intersecting integer `n` admits
no covering system of divisor form
`{a_d (mod d) : d ∣ n, d > 1}` at all, where
non-intersecting means some such system has distinct
classes overlapping (having a common integer) only
for coprime moduli. This reading of "overlap" as
CRT-compatibility was checked by exhaustive search
for `n ≤ 30`: the two kinds of assignments never
coexist for the same `n` (covering assignments exist
exactly at `n = 12, 24` in range, where no
overlap assignment exists), while prime powers admit
many overlap assignments, matching the paper's
Proposition 4.1 that prime powers are
non-intersecting.

Lemma 2.1, Proposition 2.3, Lemma 3.1 and
Propositions 4.1 and 4.2 use the paper's Section 1
definitions (`IsCDCongruenceSetOf`, `IsNonIntersecting`)
and its Section 2 density
`δ(A) = lim_{N → ∞} A(N) / N`, where `A(N)` counts the
integers in `[1, N]` covered by `A`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.GCD.Basic
public import MathlibExt.NumberTheory.CoveringSystem
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Nat.Factorization.Defs

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosGrahamCoveringWanted

/-- **Theorem 3.2**: there does not exist any `n` such
that a congruence set of the form
`{a_d (mod d) : d ∣ n, d > 1}`, where `a_d (mod d)` and
`a_{d'} (mod d')` overlap only if `gcd d d' = 1`, is a
covering set. In the paper's terminology: a
non-intersecting integer (one admitting a congruence
set of divisor form whose distinct classes overlap
only at coprime moduli) admits no covering congruence
set of divisor form at all; the two witnesses are
quantified independently below.

Source: Sarosh Adenwalla, "A Question of Erdős and
Graham on Covering Systems", Theorem 3.2. -/
theorem_wanted not_covering_of_nonintersecting (n : ℕ)
    (hnonint : ∃ a : ℕ → ℤ,
      ∀ d d' : ℕ, d ∣ n → d' ∣ n → 1 < d → 1 < d' →
        d ≠ d' →
          (∃ x : ℤ, x ≡ a d [ZMOD (d : ℤ)] ∧
            x ≡ a d' [ZMOD (d' : ℤ)]) →
          Nat.Coprime d d') :
    ¬ ∃ b : ℕ → ℤ, Int.IsCoveringSystem
        ((n.divisors.filter (fun d => 1 < d)).image
          (fun d => (b d, d)))

/-- **Lemma 2.2**: for any covering set
`{a_1 (mod d_1), …, a_t (mod d_t)}`,
`∑_{i=1}^t 1 / d_i ≥ 1`.

Source: Sarosh Adenwalla, "A Question of Erdős and
Graham on Covering Systems", Lemma 2.2. -/
theorem_wanted one_le_sum_inv_moduli {t : ℕ}
    (moduli : Fin t → ℕ) (residues : Fin t → ℤ)
    (hpos : ∀ i, 0 < moduli i)
    (hcov : Int.IsCoveringSystem
      (Int.indexedCoveringClasses moduli residues)) :
    (1 : ℚ) ≤ ∑ i, (1 : ℚ) / (moduli i : ℚ)

/-- `a` gives a CD congruence set of `n`: the classes
`a d (mod d)` for the divisors `d > 1` of `n`, where
two distinct classes overlap (share an integer) only
if their moduli are coprime.

Source: Sarosh Adenwalla, "A Question of Erdős and
Graham on Covering Systems", INTEGERS 26 (2026),
Article A52, Section 1 (CD congruence set of `n`). -/
def IsCDCongruenceSetOf (n : ℕ) (a : ℕ → ℤ) : Prop :=
  ∀ d ∈ n.divisors, ∀ d' ∈ n.divisors, 1 < d → 1 < d' → d ≠ d' →
    (∃ x : ℤ, x ≡ a d [ZMOD (d : ℤ)] ∧ x ≡ a d' [ZMOD (d' : ℤ)]) →
      Nat.Coprime d d'

/-- `n` is non-intersecting if it has a CD congruence
set.

Source: Sarosh Adenwalla, "A Question of Erdős and
Graham on Covering Systems", INTEGERS 26 (2026),
Article A52, Section 1. -/
def IsNonIntersecting (n : ℕ) : Prop :=
  ∃ a : ℕ → ℤ, IsCDCongruenceSetOf n a

/-- Characteristic example: a prime is
non-intersecting (its only divisor `d > 1` is itself).

Source: Sarosh Adenwalla, "A Question of Erdős and
Graham on Covering Systems", INTEGERS 26 (2026),
Article A52, Section 1. -/
theorem isNonIntersecting_of_prime {p : ℕ} (hp : p.Prime) :
    IsNonIntersecting p := by
  refine ⟨fun _ => 0, fun d hd d' hd' h1 h1' hne _ => ?_⟩
  rw [Nat.Prime.divisors hp, Finset.mem_insert, Finset.mem_singleton] at hd hd'
  omega

/-- **Lemma 2.1**: a CD congruence set
`{a_i (mod d_i)}` covers the integers with density
`∑_{s ≥ 1} (-1)^(s+1) ∑_{S ∈ I_s} 1 / ∏_{i ∈ S} d_i`,
the inner sum over the `s`-element index sets with
pairwise coprime moduli.

Source: Sarosh Adenwalla, "A Question of Erdős and
Graham on Covering Systems", INTEGERS 26 (2026),
Article A52, Lemma 2.1 (`integers-2026-A52-lem-2-1`). The
sets `I_s` are taken as index sets (as in the
paper's proof), and the density is the paper's
`lim A(N) / N`. -/
theorem_wanted tendsto_coveredCount_div_of_coprimeDisjoint {t : ℕ}
    (d : Fin t → ℕ) (a : Fin t → ℤ) (hd : ∀ i, 0 < d i)
    (hCD : ∀ i j, i ≠ j →
      (∃ x : ℤ, x ≡ a i [ZMOD (d i : ℤ)] ∧ x ≡ a j [ZMOD (d j : ℤ)]) →
        Nat.Coprime (d i) (d j)) :
    Filter.Tendsto
      (fun N : ℕ => ((((Finset.Icc 1 N).filter fun x : ℕ =>
        ∃ i, (x : ℤ) ≡ a i [ZMOD (d i : ℤ)]).card : ℕ) : ℝ) / N)
      Filter.atTop
      (nhds (∑ S ∈ (Finset.univ : Finset (Fin t)).powerset.filter (fun S =>
          S.Nonempty ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (d i) (d j)),
        (-1 : ℝ) ^ (S.card + 1) / ∏ i ∈ S, (d i : ℝ)))

/-- **Proposition 2.3** (folklore): for `n ≥ 1`,
`∑_{d ∣ n, d > 1} 1/d = -1 + ∑_{d ∣ n} 1/d
= -1 + ∏_i ∑_{j=0}^{α_i} 1/p_i^j`, where
`n = ∏ p_i^{α_i}`.

Source: Sarosh Adenwalla, "A Question of Erdős and
Graham on Covering Systems", INTEGERS 26 (2026),
Article A52, Proposition 2.3 (`integers-2026-A52-prop-2-3`). -/
theorem_wanted sum_inv_divisors_one_lt_eq (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors.filter (1 < ·), (1 : ℚ) / d =
        -1 + ∑ d ∈ n.divisors, (1 : ℚ) / d ∧
      -1 + ∑ d ∈ n.divisors, (1 : ℚ) / d =
        -1 + ∏ p ∈ n.primeFactors,
          ∑ j ∈ Finset.range (n.factorization p + 1), (1 : ℚ) / (p : ℚ) ^ j

/-- **Lemma 3.1**: if `n > 1` is non-intersecting and
`p` is the smallest prime dividing `n`, then `n / p`
has fewer than `p` distinct prime divisors.

Source: Sarosh Adenwalla, "A Question of Erdős and
Graham on Covering Systems", INTEGERS 26 (2026),
Article A52, Lemma 3.1 (`integers-2026-A52-lem-3-1`). -/
theorem_wanted card_primeFactors_div_minFac_lt (n : ℕ) (hn : 1 < n)
    (h : IsNonIntersecting n) :
    (n / n.minFac).primeFactors.card < n.minFac

/-- **Proposition 4.1**: `p ^ k` (`p` prime, `k ≥ 1`)
is non-intersecting, and every CD congruence set of
`p ^ k` covers the integers with density
`(p ^ k - 1) / (p ^ k (p - 1))`.

Source: Sarosh Adenwalla, "A Question of Erdős and
Graham on Covering Systems", INTEGERS 26 (2026),
Article A52, Proposition 4.1 (`integers-2026-A52-prop-4-1`). -/
theorem_wanted isNonIntersecting_prime_pow_and_density (p k : ℕ) (hp : p.Prime)
    (hk : 1 ≤ k) :
    IsNonIntersecting (p ^ k) ∧ ∀ a : ℕ → ℤ, IsCDCongruenceSetOf (p ^ k) a →
      Filter.Tendsto
        (fun N : ℕ => ((((Finset.Icc 1 N).filter fun x : ℕ =>
          ∃ d ∈ (p ^ k).divisors, 1 < d ∧ (x : ℤ) ≡ a d [ZMOD (d : ℤ)]).card : ℕ) : ℝ) / N)
        Filter.atTop
        (nhds (((p : ℝ) ^ k - 1) / ((p : ℝ) ^ k * ((p : ℝ) - 1))))

/-- **Proposition 4.2**: for distinct primes `p, q` and
`k ≥ 1`, `q p ^ k` is non-intersecting if and only if
`k = 1` or `p > 2`, and every CD congruence set of
`q p ^ k` covers the integers with density
`1 / q + (p ^ k - 1) / (p ^ k (p - 1))`.

Source: Sarosh Adenwalla, "A Question of Erdős and
Graham on Covering Systems", INTEGERS 26 (2026),
Article A52, Proposition 4.2 (`integers-2026-A52-prop-4-2`). -/
theorem_wanted isNonIntersecting_prime_mul_prime_pow_iff_and_density (p q k : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hk : 1 ≤ k) :
    (IsNonIntersecting (q * p ^ k) ↔ k = 1 ∨ 2 < p) ∧
      ∀ a : ℕ → ℤ, IsCDCongruenceSetOf (q * p ^ k) a →
      Filter.Tendsto
        (fun N : ℕ => ((((Finset.Icc 1 N).filter fun x : ℕ =>
          ∃ d ∈ (q * p ^ k).divisors, 1 < d ∧ (x : ℤ) ≡ a d [ZMOD (d : ℤ)]).card : ℕ) : ℝ) / N)
        Filter.atTop
        (nhds (1 / (q : ℝ) + ((p : ℝ) ^ k - 1) / ((p : ℝ) ^ k * ((p : ℝ) - 1))))

end MathlibExt.NumberTheory.ErdosGrahamCoveringWanted
