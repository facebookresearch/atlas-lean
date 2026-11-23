/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets with pairwise least common multiples at most N (Erdős Problem 441)

Erdős Problem 441: let `N ≥ 1`. What is the size of the largest `A ⊆ {1, …, N}` with `lcm(a, b) ≤ N`
for all `a, b ∈ A`? Is it attained by all integers in `[1, (N/2)^{1/2}]` together with all even
integers in `[(N/2)^{1/2}, (2N)^{1/2}]`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosConstructionExcessErdosProblem441Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #441, https://www.erdosproblems.com/441 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006872 (`EP-441`), dataset ulamai/UnsolvedMath v1.8.0.

The target is Chen and Dai's Theorem 1 (ii), the result erdosproblems.com/441 cites against the
second question, as the paper states it: `R₁(N) ≥ loc N - 2` for infinitely many positive integers
`N`, written `|B_N| + loc N ≤ |C_N| + 2`. Here `B_N` is Erdős's construction, `C_N` a largest set
containing `B_N` with every pairwise least common multiple at most `N`, `R₁(N) = |C_N| - |B_N|`, and
`loc x` the number of iterated natural logarithms that bring `x` into `[0, 1)`. As only finitely
many `N` have `loc N ≤ k`, the statement makes `R₁` unbounded, and the largest admissible set (of
size at least `|C_N|`) exceeds the construction by at least `loc N - 2` for infinitely many `N`; the
page quotes this bound without the `- 2`. The first question (the size of the largest set) is not
stated. The yes/no question alone has an elementary negative answer: for `N = 2b² - 1` with `b ≥ 3`
odd, adding `b` to the construction keeps every pairwise lcm at most `N`.

Sets are subsets of `{1, …, N}` with `lcm(a, b) ≤ N` for all `a, b`, `a = b` included; for `N ≥ 2`,
`1 ∈ B_N` forces every element of a set containing `B_N` to be at most `N`, so these are Chen and
Dai's sets. The construction is the filter `2a² ≤ N ∨ (2 ∣ a ∧ a² ≤ 2N)` of `{1, …, N}`. Compared
with the formal-conjectures statement `erdos_441.variants.chen_dai_infinitely_often`, which bounds
the overall maximum instead of `|C_N|` (no code imported).
-/

/-- Erdős's construction `B_N`: the integers in `[1, (N/2)^(1/2)]` together with the even integers
in `[(N/2)^(1/2), (2N)^(1/2)]`. -/
def erdosConstruction (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun a => 2 * a ^ 2 ≤ N ∨ (2 ∣ a ∧ a ^ 2 ≤ 2 * N)

/-- `|C_N|`: the largest size of a set `C ⊆ {1, …, N}` that contains Erdős's construction and has
`lcm(a, b) ≤ N` for all `a, b ∈ C`. -/
noncomputable def maxLcmBoundedSupersetSize (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ C : Finset ℕ, erdosConstruction N ⊆ C ∧ C ⊆ Finset.Icc 1 N ∧
    (∀ a ∈ C, ∀ b ∈ C, Nat.lcm a b ≤ N) ∧ C.card = k}

/-- Chen and Dai's `loc x`: the least `r` such that the `r`-fold iterated natural logarithm of `x`
lies in `[0, 1)`. -/
noncomputable def iteratedLogCount (x : ℝ) : ℕ :=
  sInf {r : ℕ | 0 ≤ Real.log^[r] x ∧ Real.log^[r] x < 1}

/-- Erdős Problem 441, Chen and Dai's Theorem 1 (ii): `|C_N| - |B_N| ≥ loc N - 2` for infinitely
many `N`. -/
def erdosConstructionExcessFrequently : Prop :=
  ∃ᶠ N : ℕ in Filter.atTop,
    (erdosConstruction N).card + iteratedLogCount N ≤ maxLcmBoundedSupersetSize N + 2

/--
Resolved true: Chen and Dai proved (Theorem 1 (ii)) that `R₁(x) ≥ loc x - 2` for infinitely many
positive integers `x`, where `|C_x| = |B_x| + R₁(x)`, `B_x` is Erdős's construction, `C_x` is a set
of positive integers with the least common multiple of each pair of terms at most `x`, `B_x ⊆ C_x`
and `|C_x|` largest, and `loc x` is the nonnegative integer `r` with `0 ≤ log log ⋯ log x < 1` (`r`
logarithms); erdosproblems.com/441 cites this result for the second question and lists the problem
as disproved. Source: T. F. Bloom, Erdős Problems, Problem #441, https://www.erdosproblems.com/441
(status DISPROVED (LEAN)); resolution: Y.-G. Chen and L.-X. Dai, Sequences with bounded l.c.m. of
each pair of terms, III, Acta Arith. 128 (2007), 125-133, Theorem 1 (ii): R₁(x) ≥ loc x - 2 for
infinitely many positive integers x, https://doi.org/10.4064/aa128-2-3.
-/
public theorem_wanted erdosConstructionExcessFrequently_holds : erdosConstructionExcessFrequently

end MathlibExt.NumberTheory.ErdosConstructionExcessErdosProblem441Wanted
