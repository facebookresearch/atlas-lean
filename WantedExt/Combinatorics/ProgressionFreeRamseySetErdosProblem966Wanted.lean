/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Progression-free sets that are Ramsey for shorter progressions (Erdős Problem 966)

Erdős Problem 966: let `k, r ≥ 2`. Does there exist a set `A ⊆ ℕ` that contains no non-trivial
arithmetic progression of length `k + 1`, yet in any `r`-colouring of `A` there must exist a
monochromatic non-trivial arithmetic progression of length `k`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.AP.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.ProgressionFreeRamseySetErdosProblem966Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #966, https://www.erdosproblems.com/966 (status PROVED
(LEAN)). UnsolvedMath record UM-30007103 (`EP-966`), dataset ulamai/UnsolvedMath v1.8.0.

Non-trivial progressions have distinct terms: MathlibExt's `Set.IsAPOfLength t l` requires `t` to
have exactly `l` elements, and `Set.IsAPOfLengthFree A l` says that `A` contains no such `t`. An
`r`-colouring of `A` is a function `ℕ → Fin r` (its values off `A` are irrelevant). Compared with
the formal-conjectures statement `ErdosProblems/966.lean` (equivalent; no code imported).
-/

/-- **Erdős Problem 966: progression-free sets that are Ramsey for shorter progressions.** This
is the statement that for all natural numbers $k \ge 2$ and $r \ge 2$ there is a set $A$ of
natural numbers that contains no arithmetic progression of $k + 1$ distinct terms and such that
for every colouring $c$ of the natural numbers with $r$ colours there are a subset
$t \subseteq A$ that is an arithmetic progression of $k$ distinct terms and a colour $i$ with
$c(x) = i$ for every $x \in t$.

Only the colours of elements of $A$ matter, so the colouring condition says that every
colouring of $A$ with $r$ colours has a monochromatic progression of $k$ distinct terms. -/
def progressionFreeRamseySet : Prop :=
  ∀ k r : ℕ, 2 ≤ k → 2 ≤ r → ∃ A : Set ℕ, A.IsAPOfLengthFree (k + 1) ∧
    ∀ c : ℕ → Fin r, ∃ t ⊆ A, t.IsAPOfLength k ∧ ∃ i : Fin r, ∀ x ∈ t, c x = i

/--
**Erdős Problem 966 holds.** For all natural numbers $k \ge 2$ and $r \ge 2$ there is a set $A$
of natural numbers that contains no arithmetic progression of $k + 1$ distinct terms and such
that for every colouring $c$ of the natural numbers with $r$ colours there are a subset
$t \subseteq A$ that is an arithmetic progression of $k$ distinct terms and a colour $i$ with
$c(x) = i$ for every $x \in t$.

Source: T. F. Bloom, Erdős
Problems, Problem #966, https://www.erdosproblems.com/966 (status PROVED (LEAN)); resolution: formal
proof linked from erdosproblems.com/966 (found with Aristotle, posted in the comment thread); P.
Erdős, Problems and results in combinatorial number theory (1975), 295-310, reports that Spencer had
shown that such a sequence exists, erdosproblems.com/966 status 'proved (Lean)'; formal proof cited
by formal-conjectures ErdosProblems/966.lean,
https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos966.lean.
-/
public theorem_wanted progressionFreeRamseySet_holds : progressionFreeRamseySet

end MathlibExt.Combinatorics.ProgressionFreeRamseySetErdosProblem966Wanted
