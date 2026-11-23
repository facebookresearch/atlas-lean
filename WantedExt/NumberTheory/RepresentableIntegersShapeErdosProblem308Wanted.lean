/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integers that are sums of distinct unit fractions up to `1/N` (Erdős Problem 308)

Erdős Problem 308: let `N ≥ 1`. What is the smallest integer not representable as a sum of distinct
unit fractions with denominators in `{1, …, N}`? Is the set of representable integers of the shape
`{1, …, m}` for some `m`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Rat.Floor
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.RepresentableIntegersShapeErdosProblem308Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #308, https://www.erdosproblems.com/308 (status
PROVED); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980). UnsolvedMath record UM-30006819 (`EP-308`), dataset ulamai/UnsolvedMath v1.8.0.

Integers are positive integers. Both questions are stated for all sufficiently large `N`, which is
what Croot's bounds give; the version for every `N ≥ 1` is open (formal-conjectures records it as
`erdos_308.variants.all_N`). `m_N = ⌊∑_{n ≤ N} 1/n⌋` uses Mathlib's `harmonic`. Compared with the
formal-conjectures statement `ErdosProblems/308.lean` (equivalent to `erdos_308.parts.i` and
`erdos_308.parts.ii`; no code imported).
-/

open Filter

/-- The positive integers that are sums of distinct unit fractions with denominators in
`{1, …, N}`. -/
def representableIntegers (N : ℕ) : Set ℕ :=
  {m | 0 < m ∧ ∃ S ⊆ Finset.Icc 1 N, ∑ n ∈ S, (1 : ℚ) / n = m}

/-- The smallest positive integer that is not such a sum. -/
noncomputable def leastNonRepresentable (N : ℕ) : ℕ :=
  sInf {m | 0 < m ∧ m ∉ representableIntegers N}

/-- Erdős Problem 308, first question: for all large `N` the smallest non-representable positive
integer is `m_N` or `m_N + 1`, where `m_N = ⌊∑_{n ≤ N} 1/n⌋`. -/
def leastNonRepresentableNearHarmonic : Prop :=
  ∀ᶠ N : ℕ in atTop, leastNonRepresentable N = ⌊harmonic N⌋₊ ∨
    leastNonRepresentable N = ⌊harmonic N⌋₊ + 1

/-- Erdős Problem 308, second question: for all large `N` the representable positive integers
form an initial segment `{1, …, m}`. -/
def representableIntegersInitialSegment : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ m : ℕ, representableIntegers N = Set.Icc 1 m

/--
Resolved true: Croot's bounds on the smallest non-representable integer show that for all large `N`
it is `m_N` or `m_N + 1`, where `m_N = ⌊∑_{n ≤ N} 1/n⌋`. erdosproblems.com/308 lists the problem as
proved. Source: T. F. Bloom, Erdős Problems, Problem #308, https://www.erdosproblems.com/308 (status
PROVED); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980); resolution: E. S. Croot III, On some questions of Erdős and Graham about Egyptian fractions,
Mathematika (1999), 359-372, erdosproblems.com/308 (essentially solved by Croot): Croot's bounds
imply that for all large N the representable integers are {1, …, m_N - 1} or {1, …, m_N}, m_N =
⌊∑_{n ≤ N} 1/n⌋, https://www.erdosproblems.com/308.
-/
public theorem_wanted leastNonRepresentableNearHarmonic_holds : leastNonRepresentableNearHarmonic

/--
Resolved true: by Croot's bounds, for all large `N` the representable positive integers are `{1, …,
m_N - 1}` or `{1, …, m_N}`, an initial segment. erdosproblems.com/308 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #308, https://www.erdosproblems.com/308 (status
PROVED); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980); resolution: E. S. Croot III, On some questions of Erdős and Graham about Egyptian fractions,
Mathematika (1999), 359-372, erdosproblems.com/308 (essentially solved by Croot): Croot's bounds
imply that for all large N the representable integers are {1, …, m_N - 1} or {1, …, m_N}, m_N =
⌊∑_{n ≤ N} 1/n⌋, https://www.erdosproblems.com/308.
-/
public theorem_wanted representableIntegersInitialSegment_holds :
    representableIntegersInitialSegment

end MathlibExt.NumberTheory.RepresentableIntegersShapeErdosProblem308Wanted
