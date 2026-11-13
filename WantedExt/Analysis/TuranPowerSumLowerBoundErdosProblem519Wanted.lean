/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Turán's power sum problem (Erdős Problem 519)

Erdős Problem 519 (Turán): for `z₁, …, zₙ ∈ ℂ` with `z₁ = 1`, is there an absolute `c > 0` with
`max_{1 ≤ k ≤ n} |∑ᵢ zᵢ ^ k| > c`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

namespace MathlibExt.Analysis.TuranPowerSumLowerBoundErdosProblem519Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #519, https://www.erdosproblems.com/519 (status PROVED
(LEAN)). UnsolvedMath record UM-30006915 (`EP-519`), dataset ulamai/UnsolvedMath v1.8.0.

The numbers are `z 0, …, z n` with `z 0 = 1`, so `k` ranges over `1, …, n + 1`. Compared with the
formal-conjectures statement `ErdosProblems/519.lean` (equivalent; no code imported). The open
question of the optimal constant is OpenConjectures/Analysis/TuranPurePowerSumConstant.
-/

/-- Erdős Problem 519 (Turán): there is an absolute `c > 0` such that for all complex
`z₀, …, zₙ` with `z₀ = 1`, some `1 ≤ k ≤ n + 1` has `|∑ᵢ zᵢ ^ k| > c`. -/
def powerSumMaxBoundedBelow : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (z : Fin (n + 1) → ℂ), z 0 = 1 →
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n + 1 ∧ c < ‖∑ i, z i ^ k‖

/--
Resolved true: Atkinson proved that `c = 1/6` works; Biró improved this to `1/2` and then to an
absolute constant above `1/2`. Source: T. F. Bloom, Erdős Problems, Problem #519,
https://www.erdosproblems.com/519 (status PROVED (LEAN)); resolution: F. V. Atkinson, On sums of
powers of complex numbers, Acta Math. Acad. Sci. Hungar. (1961), 185-188, erdosproblems.com/519:
solved by Atkinson with c = 1/6; Biró later c = 1/2 and some c > 1/2,
https://www.erdosproblems.com/519.
-/
public theorem_wanted powerSumMaxBoundedBelow_holds : powerSumMaxBoundedBelow

end MathlibExt.Analysis.TuranPowerSumLowerBoundErdosProblem519Wanted
