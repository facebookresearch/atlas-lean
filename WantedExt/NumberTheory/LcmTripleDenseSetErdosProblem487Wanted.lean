/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Least common multiples in sets of positive density (Erdős Problem 487)

Erdős Problem 487: if `A ⊆ ℕ` has positive density, must there be distinct `a, b, c ∈ A` with
`lcm(a, b) = c`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.NumberTheory.LcmTripleDenseSetErdosProblem487Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #487, https://www.erdosproblems.com/487 (status PROVED
(LEAN)). UnsolvedMath record UM-30006896 (`EP-487`), dataset ulamai/UnsolvedMath v1.8.0.

"Positive density" is positive natural density, the repository's `Set.HasPosDensity`: the proportion
of `A` in `[0, N)` tends to some `α > 0`. Positive upper density would make the statement false:
Besicovitch's primitive sets (no element divides another, so no such triple) have positive upper
density. Compared with the formal-conjectures statement `ErdosProblems/487.lean` (the same statement
through `Set.HasPosDensity`; no code imported).
-/

/-- Erdős Problem 487: every `A ⊆ ℕ` of positive natural density (`Set.HasPosDensity`) contains
distinct `a, b, c` with `lcm(a, b) = c`. -/
def positiveDensityHasLcmTriple : Prop :=
  ∀ A : Set ℕ, A.HasPosDensity →
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ Nat.lcm a b = c

/--
Resolved true: erdosproblems.com/487 records the answer yes, as a consequence of Kleitman's solution
of Erdős Problem 447 on families of sets with no three distinct members `A ∪ B = C`. Source: T. F.
Bloom, Erdős Problems, Problem #487, https://www.erdosproblems.com/487 (status PROVED (LEAN));
resolution: D. Kleitman, Collections of subsets containing no two sets and their union, Proceedings
of the LA Meeting AMS (1971), 153-155, erdosproblems.com/487: true, a consequence of Kleitman's
positive solution of Erdős Problem 447, https://www.erdosproblems.com/487.
-/
public theorem_wanted positiveDensityHasLcmTriple_holds : positiveDensityHasLcmTriple

end MathlibExt.NumberTheory.LcmTripleDenseSetErdosProblem487Wanted
