/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# How many integers are sums of distinct unit fractions up to `1/N` (Erdős Problem 309)

Erdős Problem 309: let `N ≥ 1`. How many integers can be written as a sum of distinct unit fractions
with denominators in `{1, …, N}`? Are there `o(log N)` such integers?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.RepresentableIntegersCountErdosProblem309Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #309, https://www.erdosproblems.com/309 (status
DISPROVED (LEAN)); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial
number theory (1980). UnsolvedMath record UM-30006820 (`EP-309`), dataset ulamai/UnsolvedMath
v1.8.0.

Integers are positive integers (counting `0` changes the count by one). Two targets: the count `F(N)
= (1 + o(1)) log N` and the question `F(N) = o(log N)` (answered no). Compared with the
formal-conjectures statement `ErdosProblems/309.lean` (equivalent; formal-conjectures also counts
`0`; no code imported).
-/

open Filter Topology Asymptotics

/-- The positive integers that are sums of distinct unit fractions with denominators in
`{1, …, N}`. -/
def representableIntegers (N : ℕ) : Set ℕ :=
  {m | 0 < m ∧ ∃ S ⊆ Finset.Icc 1 N, ∑ n ∈ S, (1 : ℚ) / n = m}

/-- `F(N)`: the number of such integers (a finite set, bounded by `∑_{n ≤ N} 1/n`). -/
noncomputable def representableCount (N : ℕ) : ℕ :=
  (representableIntegers N).ncard

/-- Erdős Problem 309, first question: `F(N) = (1 + o(1)) log N`. -/
def representableCountAsymptotic : Prop :=
  Tendsto (fun N : ℕ => (representableCount N : ℝ) / Real.log N) atTop (𝓝 1)

/-- Erdős Problem 309, second question: `F(N) = o(log N)`. -/
def representableCountLittleO : Prop :=
  (fun N : ℕ => (representableCount N : ℝ)) =o[atTop] fun N : ℕ => Real.log N

/--
Resolved true: `F(N) ≤ ∑_{n ≤ N} 1/n = log N + O(1)` trivially, and Yokota proved `F(N) ≥ log N -
O(log log N)`, so `F(N) = (1 + o(1)) log N`. erdosproblems.com/309 lists the problem as disproved.
Source: T. F. Bloom, Erdős Problems, Problem #309, https://www.erdosproblems.com/309 (status
DISPROVED (LEAN)); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial
number theory (1980); resolution: H. Yokota, On number of integers representable as a sum of unit
fractions. II, J. Number Theory (1997), 162-169; E. S. Croot III, On some questions of Erdős and
Graham about Egyptian fractions, Mathematika (1999), 359-372, erdosproblems.com/309: trivially F(N)
≤ log N + O(1); Yokota proved F(N) ≥ log N - O(log log N); Croot showed every integer up to ∑_{n≤N}
1/n - (9/2 + o(1))(log log N)^2/log N is representable, https://www.erdosproblems.com/309.
-/
public theorem_wanted representableCountAsymptotic_holds : representableCountAsymptotic

/--
Resolved false: Yokota's bound `F(N) ≥ log N - O(log log N)` shows `F(N)` is not `o(log N)`.
erdosproblems.com/309 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#309, https://www.erdosproblems.com/309 (status DISPROVED (LEAN)); P. Erdős and R. L. Graham, Old
and new problems and results in combinatorial number theory (1980); resolution: H. Yokota, On number
of integers representable as a sum of unit fractions. II, J. Number Theory (1997), 162-169; E. S.
Croot III, On some questions of Erdős and Graham about Egyptian fractions, Mathematika (1999),
359-372, erdosproblems.com/309: trivially F(N) ≤ log N + O(1); Yokota proved F(N) ≥ log N - O(log
log N); Croot showed every integer up to ∑_{n≤N} 1/n - (9/2 + o(1))(log log N)^2/log N is
representable, https://www.erdosproblems.com/309.
-/
public theorem_wanted representableCountLittleO_refuted : ¬ representableCountLittleO

end MathlibExt.NumberTheory.RepresentableIntegersCountErdosProblem309Wanted
