/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lower bounds for the off-diagonal Ramsey numbers R(s, k) (Erdős Problem 986)

Erdős Problem 986: for any fixed `s ≥ 3`, `R(s, k) ≫ k^{s-1} / (log k)^c` for some constant `c =
c(s) > 0`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey

@[expose] public section

namespace MathlibExt.GraphTheory.OffDiagonalRamseyLowerBoundErdosProblem986Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #986, https://www.erdosproblems.com/986 (status
PROVED). UnsolvedMath record UM-00002426 (`EP-986`), dataset ulamai/UnsolvedMath v1.8.0.

`R(s, k)` is MathlibExt's `SimpleGraph.graphRamsey s k`, the least `N` such that every graph on `N`
vertices contains `K_s` or has `K_k` in its complement; `≫` is a constant `C > 0` depending on `s`,
and the bound is required for all large `k`. Compared with the formal-conjectures statement
`ErdosProblems/986.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 986: for every fixed `s ≥ 3` there are `c = c(s) > 0` and `C > 0` with
`R(s, k) ≥ C k^{s-1} / (log k)^c` for all large `k`, where `R(s, k)` is MathlibExt's
`SimpleGraph.graphRamsey s k`. -/
def offDiagonalRamseyLowerBound : Prop :=
  ∀ s : ℕ, 3 ≤ s → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ k : ℕ in Filter.atTop,
    C * (k : ℝ) ^ (s - 1) / Real.log k ^ c ≤ (SimpleGraph.graphRamsey s k : ℝ)

/--
Resolved true: Bradač proved that for every fixed `s ≥ 3`, `R(s, k) ≥ Ω(k^{s-1} / (log k)^{2s-4})`,
the statement with `c = 2s - 4` (Spencer and Mattheus-Verstraëte had the cases `s = 3, 4`);
erdosproblems.com/986 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#986, https://www.erdosproblems.com/986 (status PROVED); resolution: D. Bradač, Off-diagonal Ramsey
numbers, arXiv:2605.28793 (2026; erdosproblems.com cites it as 'Nearly tight exponents for
off-diagonal Ramsey numbers'), abstract: for any fixed s ≥ 3, r(s, k) ≥ Ω(k^{s-1} / (log k)^{2s-4});
erdosproblems.com/986 (an earlier version had exponent s - 2; the step to s - 1 was observed by an
OpenAI model), https://arxiv.org/abs/2605.28793.
-/
public theorem_wanted offDiagonalRamseyLowerBound_holds : offDiagonalRamseyLowerBound

end MathlibExt.GraphTheory.OffDiagonalRamseyLowerBoundErdosProblem986Wanted
