/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sidon sets meeting every infinite progression (Erdős Problem 198)

Erdős Problem 198: if `A ⊆ ℕ` is a Sidon set, must the complement of `A` contain an infinite
arithmetic progression?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Notation
public import MathlibExt.Combinatorics.Additive.Sidon

@[expose] public section

namespace MathlibExt.Combinatorics.SidonSetComplementProgressionErdosProblem198Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #198, https://www.erdosproblems.com/198 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006760 (`EP-198`), dataset ulamai/UnsolvedMath v1.8.0.

Sidon sets are the canonical `Set.IsSidon` of MathlibExt (`a + b = c + d` forces `{a, b} = {c, d}`,
repeated summands included); an infinite progression is `a, a + d, a + 2d, …` with `d ≥ 1`. Compared
with the formal-conjectures statement `ErdosProblems/198.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 198: the complement of every Sidon set `A ⊆ ℕ` (`Set.IsSidon`: `a + b = c + d`
with `a, b, c, d ∈ A` forces `{a, b} = {c, d}`) contains an infinite arithmetic progression
`a, a + d, a + 2d, …` with `d ≥ 1`. -/
def sidonComplementContainsProgression : Prop :=
  ∀ A : Set ℕ, A.IsSidon → ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∉ A

/--
Resolved false: enumerate the infinite progressions `P₁, P₂, …` and pick `aₙ ∈ Pₙ` with `aₙ > 2
aₙ₋₁`; the resulting lacunary set is Sidon and meets every infinite progression.
erdosproblems.com/198 records this construction (implicit in Baumgartner's paper) and the explicit
example `{(n + 1)! + n : n ≥ 0}`. Source: T. F. Bloom, Erdős Problems, Problem #198,
https://www.erdosproblems.com/198 (status DISPROVED (LEAN)); resolution: J. E. Baumgartner,
Partitioning vector spaces, J. Combin. Theory Ser. A 18 (1975), 231-233; construction recorded on
erdosproblems.com/198, erdosproblems.com/198: answered no; a lacunary set with one element in each
infinite progression (implicit in [Ba75]), or explicitly A = {(n + 1)! + n : n ≥ 0},
https://www.erdosproblems.com/198.
-/
public theorem_wanted sidonComplementContainsProgression_refuted :
    ¬ sidonComplementContainsProgression

end MathlibExt.Combinatorics.SidonSetComplementProgressionErdosProblem198Wanted
