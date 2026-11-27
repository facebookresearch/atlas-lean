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
public import MathlibExt.NumberTheory.CoveringSystem.MinSeven
public import MathlibExt.NumberTheory.CoveringSystem.MirskyNewman
public import MathlibExt.NumberTheory.CoveringSystem.SwapResidues
public import MathlibExt.NumberTheory.CoveringSystem.Translate
public import MathlibExt.NumberTheory.CoveringSystem.TrifonovCovering
public import MathlibExt.NumberTheory.KleinCoveringSystems

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

end

end MetaMathlibExt
