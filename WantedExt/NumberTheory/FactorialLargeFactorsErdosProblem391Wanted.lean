/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Factoring n! into n large factors (Erdős Problem 391)

Erdős Problem 391: let `t(n)` be maximal such that `n! = a₁ ⋯ aₙ` with `t(n) = a₁ ≤ ⋯ ≤ aₙ`. Is `lim
t(n)/n = 1/e`? Is there `c > 0` with `t(n)/n ≤ 1/e - c/log n` for infinitely many `n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.FactorialLargeFactorsErdosProblem391Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #391, https://www.erdosproblems.com/391 (status PROVED
(LEAN)). UnsolvedMath record UM-30006849 (`EP-391`), dataset ulamai/UnsolvedMath v1.8.0.

`t(n)` is the largest `t` such that `n!` is a product of `n` factors that are all at least `t` (the
order of the factors is irrelevant). The two yes/no questions are separate targets; the request to
"obtain good bounds" (answered by the asymptotic below) is not stated. Compared with the
formal-conjectures statement `ErdosProblems/391.lean` (equivalent; no code imported).
-/

/-- `t(n)`: the largest `t` such that `n! = a₁ ⋯ aₙ` with every factor `aᵢ ≥ t`. -/
noncomputable def largestLeastFactor (n : ℕ) : ℕ :=
  sSup {t : ℕ | ∃ a : Fin n → ℕ, ∏ i, a i = Nat.factorial n ∧ ∀ i, t ≤ a i}

/-- Erdős Problem 391, first question: `t(n) / n → 1 / e`. -/
def largestLeastFactorRatioTendsto : Prop :=
  Filter.Tendsto (fun n : ℕ => (largestLeastFactor n : ℝ) / n) Filter.atTop
    (nhds (1 / Real.exp 1))

/-- Erdős Problem 391, second question: for some `c > 0`, `t(n) / n ≤ 1 / e - c / log n` for
infinitely many `n`. -/
def largestLeastFactorDeficit : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in Filter.atTop,
    (largestLeastFactor n : ℝ) / n ≤ 1 / Real.exp 1 - c / Real.log n

/--
Resolved true: Alexeev, Conway, Rosenfeld, Sutherland, Tao, Uhr and Ventullo proved `t(n)/n = 1/e -
c₀/log n + O((log n)^{-1-c})` with `c₀ = 0.3044…`, so `t(n)/n → 1/e`; erdosproblems.com/391 lists
the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #391,
https://www.erdosproblems.com/391 (status PROVED (LEAN)); resolution: B. Alexeev, E. Conway, M.
Rosenfeld, A. Sutherland, T. Tao, M. Uhr and K. Ventullo, Decomposing a factorial into large
factors, arXiv:2503.20170 (2025), t(n)/n = 1/e - c₀/log n + O((log n)^{-1-c}) with c₀ = 0.3044…
(erdosproblems.com/391), https://arxiv.org/abs/2503.20170.
-/
public theorem_wanted largestLeastFactorRatioTendsto_holds : largestLeastFactorRatioTendsto

/--
Resolved true: the same asymptotic gives `t(n)/n ≤ 1/e - c/log n` for all large `n` and any `0 < c <
c₀` (erdosproblems.com/391). Source: T. F. Bloom, Erdős Problems, Problem #391,
https://www.erdosproblems.com/391 (status PROVED (LEAN)); resolution: B. Alexeev, E. Conway, M.
Rosenfeld, A. Sutherland, T. Tao, M. Uhr and K. Ventullo, Decomposing a factorial into large
factors, arXiv:2503.20170 (2025), t(n)/n = 1/e - c₀/log n + O((log n)^{-1-c}) with c₀ = 0.3044…
(erdosproblems.com/391), https://arxiv.org/abs/2503.20170.
-/
public theorem_wanted largestLeastFactorDeficit_holds : largestLeastFactorDeficit

end MathlibExt.NumberTheory.FactorialLargeFactorsErdosProblem391Wanted
