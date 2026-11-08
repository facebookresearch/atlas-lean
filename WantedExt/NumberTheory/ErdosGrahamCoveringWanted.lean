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

Not stated (see the source audit table): Lemmas 2.1
and 3.1 and Propositions 2.3, 4.1, 4.2, which use
the paper's CD congruence sets, `I_s` families,
non-intersecting integers and densities, none of
which are defined in the extracted statements
(Proposition 2.3's formula, the density formulas
and Lemma 3.1's conclusion are also garbled in the
extraction).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.GCD.Basic
public import MathlibExt.NumberTheory.CoveringSystem

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

end MathlibExt.NumberTheory.ErdosGrahamCoveringWanted
