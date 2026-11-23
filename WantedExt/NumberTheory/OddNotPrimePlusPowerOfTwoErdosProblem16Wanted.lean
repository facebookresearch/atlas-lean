/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Odd integers not of the form `2^k + p` (Erdős Problem 16)

Erdős Problem 16: is the set of odd integers not of the form `2^k + p` the union of an infinite
arithmetic progression and a set of density `0`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.NumberTheory.OddNotPrimePlusPowerOfTwoErdosProblem16Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #16, https://www.erdosproblems.com/16 (status DISPROVED
(LEAN)). UnsolvedMath record UM-30006681 (`EP-16`), dataset ulamai/UnsolvedMath v1.8.0.

`k ≥ 0` and `p` prime; an infinite arithmetic progression is `{a + m d : m ∈ ℕ}` with `d > 0`;
density is natural density (`Set.HasDensity`). Compared with the formal-conjectures statement
`ErdosProblems/16.lean` (equivalent; no code imported).
-/

/-- The odd integers that are not of the form `2^k + p` with `k ≥ 0` and `p` prime. -/
def oddNotPrimePlusPowerOfTwo : Set ℕ :=
  {n | Odd n ∧ ¬ ∃ k p : ℕ, p.Prime ∧ n = 2 ^ k + p}

/-- Erdős Problem 16: this set is the union of an infinite arithmetic progression and a set of
natural density `0`. -/
def oddNotPrimePlusPowerOfTwoIsProgressionPlusNull : Prop :=
  ∃ A B : Set ℕ, oddNotPrimePlusPowerOfTwo = A ∪ B ∧
    (∃ a d : ℕ, 0 < d ∧ A = {x | ∃ m : ℕ, x = a + m * d}) ∧ B.HasDensity 0

/--
Resolved false: Chen proved that the positive odd integers not of the form `p + 2^k` are not the
union of finitely many infinite arithmetic progressions and a set of asymptotic density `0`;
erdosproblems.com/16 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#16, https://www.erdosproblems.com/16 (status DISPROVED (LEAN)); resolution: Y.-G. Chen, A
conjecture of Erdős on p + 2^k, arXiv:2312.04120 (2023), abstract: the positive odd integers not of
the form p + 2^k are not a union of finitely many infinite arithmetic progressions and a set of
asymptotic density zero, https://arxiv.org/abs/2312.04120.
-/
public theorem_wanted oddNotPrimePlusPowerOfTwoIsProgressionPlusNull_refuted :
    ¬ oddNotPrimePlusPowerOfTwoIsProgressionPlusNull

end MathlibExt.NumberTheory.OddNotPrimePlusPowerOfTwoErdosProblem16Wanted
