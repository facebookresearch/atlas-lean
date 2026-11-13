/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dense sets with no sum a power of two (Erdős Problem 1136)

Erdős Problem 1136: does there exist `A ⊆ ℕ` with lower density `> 1/3` such that `a + b ≠ 2^k` for
all `a, b ∈ A` and `k ≥ 0`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.NumberTheory.PowerOfTwoSumFreeDensityErdosProblem1136Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1136, https://www.erdosproblems.com/1136 (status
PROVED (LEAN)). UnsolvedMath record UM-30007177 (`EP-1136`), dataset ulamai/UnsolvedMath v1.8.0.

`a = b` is allowed, as in the source (`a, b ∈ A`). Lower density is the repository's
`Set.lowerDensity`. Compared with the formal-conjectures statement `ErdosProblems/1136.lean`
(equivalent; no code imported).
-/

/-- No sum `a + b` of two elements of `A` (equal elements allowed) is a power of two `2 ^ k`,
`k ≥ 0`. -/
def AvoidsPowerOfTwoSums (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ k : ℕ, a + b ≠ 2 ^ k

/-- Erdős Problem 1136: some `A ⊆ ℕ` of lower density greater than `1/3` has no two elements
summing to a power of two. -/
def powerOfTwoSumFreeLowerDensityAboveThird : Prop :=
  ∃ A : Set ℕ, 1 / 3 < A.lowerDensity ∧ AvoidsPowerOfTwoSums A

/--
Resolved true: Müller showed that the set of integers congruent to `3·2^i` modulo `2^{i+2}` for some
`i ≥ 0` has density `1/2` and contains no `a, b` with `a + b` a power of two (and that `1/2` is
optimal); erdosproblems.com/1136 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #1136, https://www.erdosproblems.com/1136 (status PROVED (LEAN)); resolution: H. Müller,
Über ein additiv-zahlentheoretisches Problem von P. Erdős, Mitt. Math. Ges. Hamburg (2011), 75-78,
erdosproblems.com/1136: the integers congruent to 3·2^i modulo 2^{i+2} for some i ≥ 0 have density
1/2 and no two sum to a power of two; density 1/2 is optimal.
-/
public theorem_wanted powerOfTwoSumFreeLowerDensityAboveThird_holds :
    powerOfTwoSumFreeLowerDensityAboveThird

end MathlibExt.NumberTheory.PowerOfTwoSumFreeDensityErdosProblem1136Wanted
