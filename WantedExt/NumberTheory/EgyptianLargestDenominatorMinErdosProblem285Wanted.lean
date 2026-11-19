/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Least largest denominator of an Egyptian fraction for 1 (Erdős Problem 285)

Erdős Problem 285: let `f(k)` be the least `n_k` such that `1 = 1/n₁ + ⋯ + 1/n_k` with `n₁ < ⋯ <
n_k`. Is `f(k) = (1 + o(1)) e k / (e - 1)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

namespace MathlibExt.NumberTheory.EgyptianLargestDenominatorMinErdosProblem285Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #285, https://www.erdosproblems.com/285 (status PROVED
(LEAN)). UnsolvedMath record UM-30006805 (`EP-285`), dataset ulamai/UnsolvedMath v1.8.0.

`f(k)` is an infimum, `0` when `1` has no `k`-term representation (only `k = 0, 2`, irrelevant for
the limit). Compared with the formal-conjectures statement `ErdosProblems/285.lean` (equivalent,
stated there with an explicit `o(1)` function; no code imported).
-/

open Filter Topology

/-- `f(k)`: the least `n_k` such that `1 = 1/n₁ + ⋯ + 1/n_k` with integers `0 < n₁ < ⋯ < n_k`
(`0` when there is no such representation, which happens only for `k = 0` and `k = 2`). -/
noncomputable def minLargestDenominator (k : ℕ) : ℕ :=
  sInf {m | ∃ S : Finset ℕ, S.card = k ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℚ) / n = 1 ∧ m ∈ S ∧
    ∀ n ∈ S, n ≤ m}

/-- Erdős Problem 285: `f(k) = (1 + o(1)) e k / (e - 1)`. -/
def minLargestDenominatorAsymptotic : Prop :=
  Tendsto (fun k : ℕ => (minLargestDenominator k : ℝ) / (Real.exp 1 / (Real.exp 1 - 1) * k))
    atTop (𝓝 1)

/--
Resolved true: the lower bound is trivial and Martin proved the matching upper bound `f(k) ≤ (1 +
o(1)) e k/(e - 1)`. erdosproblems.com/285 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #285, https://www.erdosproblems.com/285 (status PROVED (LEAN)); resolution: G.
Martin, Denser Egyptian fractions, Acta Arith. (2000), 231-260, erdosproblems.com/285: proved by
Martin [Ma00]; the lower bound f(k) ≥ (1 + o(1)) e k/(e - 1) is trivial,
https://www.erdosproblems.com/285.
-/
public theorem_wanted minLargestDenominatorAsymptotic_holds : minLargestDenominatorAsymptotic

end MathlibExt.NumberTheory.EgyptianLargestDenominatorMinErdosProblem285Wanted
