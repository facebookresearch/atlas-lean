/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dense divisibility chains (Erdős Problem 1217)

Erdős Problem 1217: let `A = {a₁ < a₂ < ⋯}` be an infinite sequence of positive integers with
positive lower logarithmic density. Must there be `n₁ < n₂ < ⋯` with `a_{nᵢ} ∣ a_{nᵢ₊₁}` and
`limsup_x (1/log log x) #{i : a_{nᵢ} < x} ≥ limsup_x (1/log log x) ∑_{aₙ < x} 1/(aₙ log aₙ)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.DivisibilityChainLogLogErdosProblem1217Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1217, https://www.erdosproblems.com/1217 (status
PROVED). UnsolvedMath record UM-30007258 (`EP-1217`), dataset ulamai/UnsolvedMath v1.8.0.

Terms are `≥ 2`, so that `1/(aₙ log aₙ)` is defined. Positive lower logarithmic density is `∑_{aᵢ ≤
x} 1/aᵢ ≥ δ log x` for some `δ > 0` and all large `x` (the hypothesis is kept although the
resolution does not need it). `x` runs over the integers, and the limits superior are taken in
`EReal`, since the left side may be infinite. formal-conjectures has no statement.
-/

open Filter

/-- Erdős Problem 1217: let `a₀ < a₁ < ⋯` be integers `≥ 2` with positive lower logarithmic
density (`∑_{aᵢ ≤ x} 1/aᵢ ≥ δ log x` for some `δ > 0` and all large `x`). Then some subsequence
`a_{n₀}, a_{n₁}, …` (`n` strictly increasing) is a divisibility chain with
`limsup_x #{i : a_{nᵢ} < x} / log log x ≥ limsup_x (∑_{aᵢ < x} 1/(aᵢ log aᵢ)) / log log x`
(limits superior in `EReal`). -/
def divisibilityChainLogLogCount : Prop :=
  ∀ a : ℕ → ℕ, StrictMono a → 2 ≤ a 0 →
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x : ℕ in atTop,
      δ * Real.log x ≤ ∑ i ∈ (Finset.range x).filter (fun i => a i ≤ x), (1 : ℝ) / a i) →
    ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ i, a (n i) ∣ a (n (i + 1))) ∧
      limsup (fun x : ℕ => ((((Finset.range x).filter (fun i => a (n i) < x)).card /
          Real.log (Real.log x) : ℝ) : EReal)) atTop ≥
        limsup (fun x : ℕ => (((∑ i ∈ (Finset.range x).filter (fun i => a i < x),
          (1 : ℝ) / (a i * Real.log (a i))) / Real.log (Real.log x) : ℝ) : EReal)) atTop

/--
Resolved true: Alexeev, Barreto, Li, Lichtman, Price, Shah, Tang and Tao prove (Theorem 1.6) that if
`Δ = limsup_x (1/log log x) ∑_{a ∈ A, a ≤ x} 1/(a log a) > 0`, then `A` contains a strictly
increasing divisibility chain `n₀ ∣ n₁ ∣ ⋯` with `limsup_x (1/log log x) #{i : nᵢ ≤ x} ≥ Δ`.
Positive lower logarithmic density gives `Δ > 0` by partial summation, and replacing `≤ x` by `< x`
changes neither limit superior. erdosproblems.com/1217 lists the problem as proved on the strength
of this preprint (earlier: Davenport-Erdős gave an infinite divisibility chain,
Erdős-Sárközy-Szemerédi a chain with `limsup ≫_c 1`). Source: T. F. Bloom, Erdős Problems, Problem
#1217, https://www.erdosproblems.com/1217 (status PROVED); resolution: B. Alexeev, K. Barreto, Y.
Li, J. D. Lichtman, L. Price, J. I. Shah, Q. Tang and T. Tao, Primitive sets and von Mangoldt
chains: Erdős Problem #1196 and beyond, arXiv:2605.00301 (2026), Theorem 1.6: if Δ = limsup_x (1/log
log x) ∑_{a ∈ A, a ≤ x} 1/(a log a) > 0, then A contains a strictly increasing infinite divisibility
chain n₀ | n₁ | ⋯ with limsup_x (1/log log x) #{i : nᵢ ≤ x} ≥ Δ; erdosproblems.com/1217: proved in
the affirmative, without the positive lower logarithmic density assumption,
https://arxiv.org/abs/2605.00301.
-/
public theorem_wanted divisibilityChainLogLogCount_holds : divisibilityChainLogLogCount

end MathlibExt.NumberTheory.DivisibilityChainLogLogErdosProblem1217Wanted
