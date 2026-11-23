/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Distinct consecutive sums of permutations (Erdős Problem 34)

Erdős Problem 34: for a permutation `π` of `{1, …, n}` let `S(π)` be the number of distinct sums
`∑_{u ≤ i ≤ v} π(i)`. Is `S(π) = o(n²)` for all `π ∈ S_n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

namespace MathlibExt.NumberTheory.PermutationConsecutiveSumsErdosProblem34Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #34, https://www.erdosproblems.com/34 (status DISPROVED
(LEAN)). UnsolvedMath record UM-30006691 (`EP-34`), dataset ulamai/UnsolvedMath v1.8.0.

"`S(π) = o(n²)` for all `π`" is read uniformly, `max_{π ∈ S_n} S(π) = o(n²)` (equivalently, for
every choice `π_n ∈ S_n`). Position `i : Fin n` holds the value `p i + 1`. Compared with the
formal-conjectures statement `ErdosProblems/34.lean` (equivalent; no code imported).
-/

open Filter

/-- `S(π)`: the number of distinct consecutive sums `π(u) + ⋯ + π(v)`, `1 ≤ u ≤ v ≤ n`, of a
permutation `π` of `{1, …, n}` (position `i : Fin n` holds the value `p i + 1`). -/
def consecutiveSumCount (n : ℕ) (p : Equiv.Perm (Fin n)) : ℕ :=
  (((Finset.univ : Finset (Fin n × Fin n)).filter fun q => q.1 ≤ q.2).image
    fun q => ∑ i ∈ Finset.Icc q.1 q.2, ((p i : ℕ) + 1)).card

/-- Erdős Problem 34: `S(π) = o(n²)` for all `π ∈ S_n`, i.e. `max_{π ∈ S_n} S(π) = o(n²)`. -/
def consecutiveSumCountLittleO : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ p : Equiv.Perm (Fin n),
    (consecutiveSumCount n p : ℝ) ≤ ε * n ^ 2

/--
Resolved false: Hegyvári constructed permutations with `S(π) ≥ (1/18 + o(1)) n²`, and Konieczny
showed that a random permutation has `((1 + e^{-2})/4 + o(1)) n²` distinct consecutive sums with
high probability. erdosproblems.com/34 lists the problem as disproved. Source: T. F. Bloom, Erdős
Problems, Problem #34, https://www.erdosproblems.com/34 (status DISPROVED (LEAN)); resolution: N.
Hegyvári, On consecutive sums in sequences, Acta Math. Hungar. (1986), 193-200; J. Konieczny, On
consecutive sums in permutations, arXiv:1504.07156 (2015), Hegyvári: a permutation with S(π) ≥ (1/18
+ o(1)) n²; Konieczny (abstract): a random permutation has ((1 + e^{-2})/4 + o(1)) n² distinct sums
with high probability, https://arxiv.org/abs/1504.07156.
-/
public theorem_wanted consecutiveSumCountLittleO_refuted : ¬ consecutiveSumCountLittleO

end MathlibExt.NumberTheory.PermutationConsecutiveSumsErdosProblem34Wanted
