/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Largest denominators of Egyptian fractions (Erdős Problem 305)

Erdős Problem 305: for `1 ≤ a < b` let `D(a, b)` be the least possible `n_k` in `a / b = 1/n₁ + ⋯ +
1/n_k` with `1 ≤ n₁ < ⋯ < n_k`, and `D(b) = max_{1 ≤ a < b} D(a, b)`. Is `D(b) ≪ b (log b)^{1 +
o(1)}`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.EgyptianFractionDenominatorBoundErdosProblem305Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #305, https://www.erdosproblems.com/305 (status
PROVED); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980), p. 38. UnsolvedMath record UM-30006817 (`EP-305`), dataset ulamai/UnsolvedMath v1.8.0.

`D(a, b)` is the least `N` admitting a representation with all denominators at most `N`, which is
the least possible largest denominator; representations exist for every positive rational. `(log
b)^{1 + o(1)}` is read as: for every `ε > 0`, `D(b) ≤ C b (log b)^{1 + ε}` for all `b ≥ 2`. Compared
with the formal-conjectures statement `ErdosProblems/305.lean` (equivalent; no code imported).
-/

/-- `D(a, b)`: the least `N` such that `a / b = 1 / n₁ + ⋯ + 1 / n_k` with distinct positive
integers `n₁ < ⋯ < n_k ≤ N`, i.e. the least possible largest denominator. -/
noncomputable def egyptianLargestDenominator (a b : ℕ) : ℕ :=
  sInf {N | ∃ S : Finset ℕ, 0 ∉ S ∧ (∀ n ∈ S, n ≤ N) ∧ ∑ n ∈ S, (1 : ℚ) / n = (a : ℚ) / b}

/-- `D(b) = max_{1 ≤ a < b} D(a, b)`. -/
noncomputable def maxEgyptianLargestDenominator (b : ℕ) : ℕ :=
  (Finset.Ico 1 b).sup fun a => egyptianLargestDenominator a b

/-- Erdős Problem 305: `D(b) ≪ b (log b) ^ (1 + o(1))`, i.e. for every `ε > 0` there is `C` with
`D(b) ≤ C b (log b) ^ (1 + ε)` for all `b ≥ 2`. -/
def maxEgyptianLargestDenominatorNearLinear : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ b : ℕ, 2 ≤ b →
    (maxEgyptianLargestDenominator b : ℝ) ≤ C * b * Real.log b ^ (1 + ε)

/--
Resolved true: Yokota proved `D(b) ≪ b (log b)(log log b)^4 (log log log b)^2`, which is `b (log
b)^{1 + o(1)}`; Liu and Sawhney (arXiv:2404.07113) improved the exponent of `log log b` to 3.
erdosproblems.com/305 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#305, https://www.erdosproblems.com/305 (status PROVED); P. Erdős and R. L. Graham, Old and new
problems and results in combinatorial number theory (1980), p. 38; resolution: H. Yokota, On a
problem of Bleicher and Erdős, J. Number Theory 30 (1988), 198-207, D(b) ≪ b (log b)(log log b)^4
(log log log b)^2 (erdosproblems.com/305), https://doi.org/10.1016/0022-314X(88)90017-4.
-/
public theorem_wanted maxEgyptianLargestDenominatorNearLinear_holds :
    maxEgyptianLargestDenominatorNearLinear

end MathlibExt.NumberTheory.EgyptianFractionDenominatorBoundErdosProblem305Wanted
