/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Empty

namespace MetaMathlibExt

@[expose] public section

/-- **Callan sequences.** Let $k$ and $n$ be natural numbers. Form the blue base set
$\{1, \dots, k\} \cup \{\star_B\}$ and the red base set $\{1, \dots, n\} \cup \{\star_R\}$,
where the blue star $\star_B$ and the red star $\star_R$ are new elements. An (unbarred)
Callan sequence of size $k \times n$ consists of a natural number $m \le n$ together with a
sequence of $m + 1$ pairs $(B_0, R_0), \dots, (B_m, R_m)$ such that the blue blocks
$B_0, \dots, B_m$ are nonempty subsets of the blue base set and every element of the blue base
set lies in exactly one of them, the red blocks $R_0, \dots, R_m$ are nonempty subsets of the
red base set and every element of the red base set lies in exactly one of them, and the last
pair contains both stars: $\star_B \in B_m$ and $\star_R \in R_m$.

Source: concept `jis_term_ce5e63b2f9fff90839347b2c`, statement
`jis_9bd5ee64b3776e07257d0f5f`, source `jis_source_076226dadb590961d2a14ace`, lines 159-190. -/
structure CallanSequence (k n : ℕ) where
  /-- Number of ordinary Callan pairs. -/
  m : ℕ
  /-- Pair-count bound from the source definition. -/
  m_le_n : m ≤ n
  /-- Blue blocks indexed by `Fin (m + 1)`. -/
  blue : Fin (m + 1) → Finset (Option (Fin k))
  /-- Red blocks indexed by `Fin (m + 1)`. -/
  red : Fin (m + 1) → Finset (Option (Fin n))
  /-- Every blue block is nonempty. -/
  blue_nonempty : ∀ i, (blue i).Nonempty
  /-- Every red block is nonempty. -/
  red_nonempty : ∀ i, (red i).Nonempty
  /-- The blue blocks partition the blue base set. -/
  blue_covers : ∀ x, ∃! i, x ∈ blue i
  /-- The red blocks partition the red base set. -/
  red_covers : ∀ x, ∃! i, x ∈ red i
  /-- The blue star lies in the extra blue block. -/
  blue_mem_star : (none : Option (Fin k)) ∈ blue (Fin.last m)
  /-- The red star lies in the extra red block. -/
  red_mem_star : (none : Option (Fin n)) ∈ red (Fin.last m)

end

end MetaMathlibExt
