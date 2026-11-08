/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A reverse Littlewood–Offord problem (Erdős Problem 395)

Erdős Problem 395: if `z₁, …, zₙ ∈ ℂ` with `|zᵢ| = 1`, is the probability that `|ε₁z₁ + ⋯ + εₙzₙ| ≤
√2`, for independent uniform signs `εᵢ ∈ {-1, 1}`, at least `≫ 1/n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Combinatorics.ReverseLittlewoodOffordErdosProblem395Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #395, https://www.erdosproblems.com/395 (status PROVED
(LEAN)). UnsolvedMath record UM-30006851 (`EP-395`), dataset ulamai/UnsolvedMath v1.8.0.

The probability is the proportion of the `2ⁿ` sign vectors, encoded as `Fin n → Bool`; the constant
is absolute and `n ≥ 1`. Compared with the formal-conjectures statement `ErdosProblems/395.lean`
(equivalent; no code imported).
-/

/-- The number of sign vectors `ε ∈ {-1, 1}ⁿ` (encoded as `Fin n → Bool`) with
`|ε₁ z₁ + ⋯ + εₙ zₙ| ≤ √2`. -/
noncomputable def smallSignedSumCount {n : ℕ} (z : Fin n → ℂ) : ℕ :=
  {ε : Fin n → Bool | ‖∑ i, (if ε i then (1 : ℂ) else -1) * z i‖ ≤ Real.sqrt 2}.ncard

/-- Erdős Problem 395: for unit complex numbers `z₁, …, zₙ`, uniformly random signs give
`|ε₁ z₁ + ⋯ + εₙ zₙ| ≤ √2` with probability `≫ 1 / n`. -/
def reverseLittlewoodOffordSqrtTwo : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ = 1) →
    c / n ≤ (smallSignedSumCount z : ℝ) / 2 ^ n

/--
Resolved true: He, Juškevičius, Narayanan and Spiro proved that for unit complex numbers `z₁, …, zₙ`
the probability that `|ε₁z₁ + ⋯ + εₙzₙ| ≤ √2` is `≫ 1/n`, which is sharp (half of the `zᵢ` equal to
`1`, the rest to `i`); erdosproblems.com/395 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #395, https://www.erdosproblems.com/395 (status PROVED (LEAN)); resolution: X. He,
T. Juškevičius, B. Narayanan and S. Spiro, The reverse Littlewood-Offord problem of Erdős,
arXiv:2408.11034 (2024), probability ≫ 1/n, sharp (erdosproblems.com/395),
https://arxiv.org/abs/2408.11034.
-/
public theorem_wanted reverseLittlewoodOffordSqrtTwo_holds : reverseLittlewoodOffordSqrtTwo

end MathlibExt.Combinatorics.ReverseLittlewoodOffordErdosProblem395Wanted
