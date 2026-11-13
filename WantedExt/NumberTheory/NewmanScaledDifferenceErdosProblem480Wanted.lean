/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Newman's conjecture on scaled differences in `[0, 1]` (Erdős Problem 480)

Erdős Problem 480 (Newman): for every sequence `x₁, x₂, … ∈ [0, 1]`, is `inf_n liminf_{m → ∞} n
|x_{m+n} - x_m| ≤ 5 ^ (-1/2)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace MathlibExt.NumberTheory.NewmanScaledDifferenceErdosProblem480Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #480, https://www.erdosproblems.com/480 (status PROVED
(LEAN)). UnsolvedMath record UM-30006891 (`EP-480`), dataset ulamai/UnsolvedMath v1.8.0.

The sequence is indexed from `0`. `inf_n liminf_m … ≤ c` is unfolded: for every `ε > 0` some `n ≥ 1`
has `n |x (m + n) - x m| < c + ε` for infinitely many `m`. Compared with the formal-conjectures
statement `ErdosProblems/480.lean` (equivalent; it uses `⨅` and `liminf`; no code imported).
-/

/-- Erdős Problem 480 (Newman): for every sequence `x` in `[0, 1]`,
`inf_{n ≥ 1} liminf_{m → ∞} n |x (m + n) - x m| ≤ 5 ^ (-1/2)`. Unfolded: for every `ε > 0` some
`n ≥ 1` has `n |x (m + n) - x m| < 5 ^ (-1/2) + ε` for infinitely many `m`. -/
def newmanScaledDifferenceBound : Prop :=
  ∀ x : ℕ → ℝ, (∀ m, x m ∈ Set.Icc (0 : ℝ) 1) → ∀ ε : ℝ, 0 < ε →
    ∃ n : ℕ, 0 < n ∧ ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧
      (n : ℝ) * |x (m + n) - x m| < 1 / Real.sqrt 5 + ε

/--
Resolved true: Chung and Graham proved `inf_n liminf_m n |x_{m+n} - x_m| ≤ 1/c ≈ 0.3944` with `c =
1 + ∑_{k ≥ 1} 1/F_{2k}` (Fibonacci numbers), which is below `5 ^ (-1/2) ≈ 0.447`; they also showed
`1/c` is best possible. Source: T. F. Bloom, Erdős Problems, Problem #480,
https://www.erdosproblems.com/480 (status PROVED (LEAN)); resolution: F. R. K. Chung and R. L.
Graham, On irregularities of distribution (1984), 181-222, erdosproblems.com/480: proved by Chung
and Graham with the better constant 1/c ≈ 0.3944, c = 1 + ∑_{k ≥ 1} 1/F_{2k},
https://www.erdosproblems.com/480.
-/
public theorem_wanted newmanScaledDifferenceBound_holds : newmanScaledDifferenceBound

end MathlibExt.NumberTheory.NewmanScaledDifferenceErdosProblem480Wanted
