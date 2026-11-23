/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Consecutive terms with small least common multiple (Erdős Problem 440)

Erdős Problem 440: let `A = {a₁ < a₂ < ⋯} ⊆ ℕ` be infinite and `A(x)` the number of `i` with
`lcm(aᵢ, aᵢ₊₁) ≤ x`. Is `A(x) ≪ x^{1/2}`? How large can `liminf A(x)/x^{1/2}` be?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.NumberTheory.ConsecutiveLcmCountErdosProblem440Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #440, https://www.erdosproblems.com/440 (status
SOLVED). UnsolvedMath record UM-30006871 (`EP-440`), dataset ulamai/UnsolvedMath v1.8.0.

`A` is given by a strictly increasing sequence of positive integers and `x` runs over the naturals;
`A(x)` is finite. The answer to the second question, `1`, is stated without `liminf`: for every `A`
and `ε > 0`, `A(x) ≤ (1 + ε) x^{1/2}` infinitely often, and for some `A`, `A(x) ≥ (1 - ε) x^{1/2}`
eventually. Compared with the formal-conjectures statement `ErdosProblems/440.lean` (equivalent,
avoiding `liminf` on `ℝ`; no code imported).
-/

/-- `A(x)`: the number of indices `i` with `lcm(a i, a (i + 1)) ≤ x` (a finite number when `a` is
strictly increasing). -/
noncomputable def lcmCount (a : ℕ → ℕ) (x : ℕ) : ℕ :=
  {i : ℕ | Nat.lcm (a i) (a (i + 1)) ≤ x}.ncard

/-- Erdős Problem 440, first question: `A(x) ≪ x^(1/2)` for every infinite set
`A = {a 0 < a 1 < ⋯}` of positive integers. -/
def lcmCountSqrtBound : Prop :=
  ∀ a : ℕ → ℕ, StrictMono a → (∀ i, 0 < a i) →
    ∃ C : ℝ, ∀ x : ℕ, (lcmCount a x : ℝ) ≤ C * Real.sqrt x

/-- Erdős Problem 440, second question: the largest possible value of `liminf A(x) / x^(1/2)` is
`1`: the liminf is at most `1` for every `A`, and equals `1` for some `A`. -/
def maxLiminfLcmCountRatioEqOne : Prop :=
  (∀ a : ℕ → ℕ, StrictMono a → (∀ i, 0 < a i) → ∀ ε : ℝ, 0 < ε →
      ∃ᶠ x : ℕ in Filter.atTop, (lcmCount a x : ℝ) ≤ (1 + ε) * Real.sqrt x) ∧
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℕ in Filter.atTop, (1 - ε) * Real.sqrt x ≤ lcmCount a x

/--
Resolved true: Erdős and Szemerédi proved `A(x) ≤ (c + o(1)) x^{1/2}` with `c = ∑_{n ≥ 1} n^{-1/2}
(n + 1)^{-1} ≈ 1.86` (rediscovered by van Doorn), and Tao gave a short proof of `A(x) ≪ x^{1/2}`
(erdosproblems.com/440). Source: T. F. Bloom, Erdős Problems, Problem #440,
https://www.erdosproblems.com/440 (status SOLVED); resolution: P. Erdős and E. Szemerédi, Remarks on
a problem of the American Mathematical Monthly, Mat. Lapok (1980), 121-124, A(x) ≤ (c + o(1))
x^{1/2} with c = ∑_{n ≥ 1} n^{-1/2}(n + 1)^{-1} ≈ 1.86; liminf A(x)/x^{1/2} ≤ 1, attained by A = ℕ
(erdosproblems.com/440).
-/
public theorem_wanted lcmCountSqrtBound_holds : lcmCountSqrtBound

/--
Resolved true: Erdős and Szemerédi proved `liminf A(x)/x^{1/2} ≤ 1` for every `A`, and `A = ℕ`
attains `1` (erdosproblems.com/440). Source: T. F. Bloom, Erdős Problems, Problem #440,
https://www.erdosproblems.com/440 (status SOLVED); resolution: P. Erdős and E. Szemerédi, Remarks on
a problem of the American Mathematical Monthly, Mat. Lapok (1980), 121-124, A(x) ≤ (c + o(1))
x^{1/2} with c = ∑_{n ≥ 1} n^{-1/2}(n + 1)^{-1} ≈ 1.86; liminf A(x)/x^{1/2} ≤ 1, attained by A = ℕ
(erdosproblems.com/440).
-/
public theorem_wanted maxLiminfLcmCountRatioEqOne_holds : maxLiminfLcmCountRatioEqOne

end MathlibExt.NumberTheory.ConsecutiveLcmCountErdosProblem440Wanted
