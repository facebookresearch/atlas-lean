/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The off-diagonal Ramsey numbers R(4, k) (Erdős Problem 166)

Erdős Problem 166: prove that `R(4, k) ≫ k³ / (log k)^{O(1)}`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey

@[expose] public section

namespace MathlibExt.GraphTheory.RamseyFourCubicErdosProblem166Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #166, https://www.erdosproblems.com/166 (status
PROVED). UnsolvedMath record UM-30006747 (`EP-166`), dataset ulamai/UnsolvedMath v1.8.0.

`R(4, k)` is MathlibExt's `SimpleGraph.graphRamsey 4 k`, the least `N` such that every graph on `N`
vertices contains `K_4` or its complement contains `K_k` (the set is nonempty by Ramsey's theorem);
the bound is stated for all large `k` with constants `c, C > 0`. Compared with the
formal-conjectures statement `ErdosProblems/166.lean` (equivalent to `erdos_166`; no code imported).
-/

open Filter

/-- Erdős Problem 166: `R(4, k) ≫ k³ / (log k)^{O(1)}`: there are `c, C > 0` such that
`R(4, k) ≥ c k³ / (log k)^C` for all large `k`, where `R(4, k) = SimpleGraph.graphRamsey 4 k`. -/
def ramseyFourCubicLowerBound : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
    c * k ^ 3 / Real.log k ^ C ≤ (SimpleGraph.graphRamsey 4 k : ℝ)

/--
Resolved true: Mattheus and Verstraëte proved `R(4, k) = Ω(k³ / (log k)⁴)`, which is the statement
with `C = 4`; erdosproblems.com/166 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #166, https://www.erdosproblems.com/166 (status PROVED); resolution: S. Mattheus
and J. Verstraëte, The asymptotics of r(4, t), Ann. of Math. (2024), arXiv:2306.04007, abstract:
r(4, t) = Ω(t³ / log⁴ t); erdosproblems.com/166, https://arxiv.org/abs/2306.04007.
-/
public theorem_wanted ramseyFourCubicLowerBound_holds : ramseyFourCubicLowerBound

end MathlibExt.GraphTheory.RamseyFourCubicErdosProblem166Wanted
