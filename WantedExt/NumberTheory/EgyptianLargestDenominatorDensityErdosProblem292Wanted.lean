/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Largest denominators of Egyptian fractions for 1 have density one (Erdős Problem 292)

Erdős Problem 292: let `A` be the set of `n` such that `1 = 1/m₁ + ⋯ + 1/m_k` for some `1 ≤ m₁ < ⋯ <
m_k = n`. Does `A` have density `1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.EgyptianLargestDenominatorDensityErdosProblem292Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #292, https://www.erdosproblems.com/292 (status
PROVED); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980), p. 35. UnsolvedMath record UM-30006809 (`EP-292`), dataset ulamai/UnsolvedMath v1.8.0.

"Explore `A`" is open-ended; the density question is stated, with natural density over `[1, N]`.
Compared with the formal-conjectures statement `ErdosProblems/292.lean` (equivalent; no code
imported).
-/

open Filter Topology

/-- `n` is the largest denominator of some `1 = 1/m₁ + ⋯ + 1/m_k` with
`1 ≤ m₁ < ⋯ < m_k = n`. -/
def IsLargestUnitDenominator (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ n ∈ S ∧ ∑ m ∈ S, (1 : ℚ) / m = 1

/-- Erdős Problem 292: the set `A` of such `n` has natural density `1`. -/
def largestUnitDenominatorsDensityOne : Prop :=
  Tendsto (fun N : ℕ => (({n | IsLargestUnitDenominator n} ∩ Set.Icc 1 N).ncard : ℝ) / N)
    atTop (𝓝 1)

/--
Resolved true: Martin proved that the complement `B` of `A` has `|B ∩ [1, x]| / x ≍ log log x / log
x`, so `A` has density `1`. erdosproblems.com/292 lists the problem as proved. Source: T. F. Bloom,
Erdős Problems, Problem #292, https://www.erdosproblems.com/292 (status PROVED); P. Erdős and R. L.
Graham, Old and new problems and results in combinatorial number theory (1980), p. 35; resolution:
G. Martin, Denser Egyptian fractions, Acta Arith. (2000), 231-260, erdosproblems.com/292: proved by
Martin, who shows that B = ℕ \ A satisfies |B ∩ [1, x]| / x ≍ log log x / log x,
https://www.erdosproblems.com/292.
-/
public theorem_wanted largestUnitDenominatorsDensityOne_holds : largestUnitDenominatorsDensityOne

end MathlibExt.NumberTheory.EgyptianLargestDenominatorDensityErdosProblem292Wanted
