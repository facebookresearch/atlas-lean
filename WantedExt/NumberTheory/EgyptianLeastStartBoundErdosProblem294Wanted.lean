/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The least start of an impossible Egyptian fraction (Erdős Problem 294)

Erdős Problem 294: let `t(N)` be the least `t` such that `1 = 1/n₁ + ⋯ + 1/n_k` has no solution with
`t = n₁ < ⋯ < n_k ≤ N`. Estimate `t(N)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.EgyptianLeastStartBoundErdosProblem294Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #294, https://www.erdosproblems.com/294 (status
PROVED). UnsolvedMath record UM-30006810 (`EP-294`), dataset ulamai/UnsolvedMath v1.8.0.

The estimate is stated as the bounds recorded as the solution (up to `(log log N)^{O(1)}`): `N /
((log N)(log log N)³ (log log log N)^K) ≪ t(N) ≪ N / log N` for some constant `K`, with `≪` as
`IsBigO` at infinity. `t(N)` ranges over positive `t` (`t(N) ≤ N + 1`). Compared with the
formal-conjectures statement `ErdosProblems/294.lean` (equivalent; no code imported).
-/

open Filter Asymptotics

/-- `1 = 1/n₁ + ⋯ + 1/n_k` has a solution with `t = n₁ < ⋯ < n_k ≤ N`. -/
def HasSolutionFrom (t N : ℕ) : Prop :=
  ∃ S : Finset ℕ, t ∈ S ∧ (∀ n ∈ S, t ≤ n ∧ n ≤ N) ∧ ∑ n ∈ S, (1 : ℚ) / n = 1

/-- `t(N)`: the least positive integer `t` for which there is no such solution (`t(N) ≤ N + 1`). -/
noncomputable def leastStartWithoutSolution (N : ℕ) : ℕ :=
  sInf {t | 0 < t ∧ ¬ HasSolutionFrom t N}

/-- Erdős Problem 294, as estimated by Liu and Sawhney:
`N / ((log N) (log log N)³ (log log log N)^K) ≪ t(N) ≪ N / log N` for some constant `K`. -/
def leastStartWithoutSolutionBounds : Prop :=
  (∃ K : ℝ, (fun N : ℕ => (N : ℝ) / (Real.log N * Real.log (Real.log N) ^ 3 *
      Real.log (Real.log (Real.log N)) ^ K)) =O[atTop]
      fun N : ℕ => (leastStartWithoutSolution N : ℝ)) ∧
    (fun N : ℕ => (leastStartWithoutSolution N : ℝ)) =O[atTop] fun N : ℕ => (N : ℝ) / Real.log N

/--
Resolved true: Erdős and Graham showed `t(N) ≪ N / log N`, and Liu and Sawhney proved `t(N) ≫ N /
((log N)(log log N)³ (log log log N)^{O(1)})`. erdosproblems.com/294 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #294, https://www.erdosproblems.com/294 (status
PROVED); resolution: Y. P. Liu and M. Sawhney, On further questions regarding unit fractions,
arXiv:2404.07113 (2024), Theorem 1.6; erdosproblems.com/294: solved by Liu and Sawhney up to (log
log N)^{O(1)}: N/((log N)(log log N)^3 (log log log N)^{O(1)}) ≪ t(N) ≪ N/log N, the upper bound due
to Erdős and Graham [ErGr80], https://arxiv.org/abs/2404.07113.
-/
public theorem_wanted leastStartWithoutSolutionBounds_holds : leastStartWithoutSolutionBounds

end MathlibExt.NumberTheory.EgyptianLeastStartBoundErdosProblem294Wanted
