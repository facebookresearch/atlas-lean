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

/-- Erdős Problem 966: for all `k, r ≥ 2` there is a set `A ⊆ ℕ` with no arithmetic progression of
`k + 1` distinct terms such that every `r`-colouring of `A` has a monochromatic arithmetic
progression of `k` distinct terms (`Set.IsAPOfLength`, `Set.IsAPOfLengthFree`, MathlibExt). -/
def progressionFreeRamseySet : Prop :=
  ∀ k r : ℕ, 2 ≤ k → 2 ≤ r → ∃ A : Set ℕ, A.IsAPOfLengthFree (k + 1) ∧
    ∀ c : ℕ → Fin r, ∃ t ⊆ A, t.IsAPOfLength k ∧ ∃ i : Fin r, ∀ x ∈ t, c x = i

/--
Resolved true: erdosproblems.com/966 lists the problem as proved (Lean), on the strength of a formal
proof found with Aristotle and posted in the comments that constructs such sets for all `k, r ≥ 2`;
Erdős had reported that Spencer had shown that such a sequence exists. Source: T. F. Bloom, Erdős
Problems, Problem #966, https://www.erdosproblems.com/966 (status PROVED (LEAN)); resolution: formal
proof linked from erdosproblems.com/966 (found with Aristotle, posted in the comment thread); P.
Erdős, Problems and results in combinatorial number theory (1975), 295-310, reports that Spencer had
shown that such a sequence exists, erdosproblems.com/966 status 'proved (Lean)'; formal proof cited
by formal-conjectures ErdosProblems/966.lean,
https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos966.lean.
-/
public theorem_wanted progressionFreeRamseySet_holds : progressionFreeRamseySet

end MathlibExt.Combinatorics.ProgressionFreeRamseySetErdosProblem966Wanted
