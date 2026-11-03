/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.HKA
import Mathlib.Tactic.NormNum

/-!
# Tests for the HKA expectations

Values at concrete parameters (`a₁(2) = 1`, `T = 0`, `f = 1`), positivity in the domain,
the estimating equations for two loci, and the boundary `T = 0`, `f → -1` documented as
outside the domain.
-/

@[expose] public section

open Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.HKA

open MathlibExt.Biology.PopulationGenetics.Coalescent

/-- Two genes: `E S = θ a₁(2) = θ`. -/
example (θ : ℝ) : hkaPolyMean θ 2 = θ := by
  simp [hkaPolyMean, tajimaA1]

/-- Two genes: `Var S = θ + θ²`. -/
example (θ : ℝ) : hkaPolyVar θ 2 = θ + θ ^ 2 := by
  simp [hkaPolyVar, tajimaA1, tajimaA2]

/-- Equal population sizes (`f = 1`) and no separation (`T = 0`): `E D = θ`,
`Var D = θ + θ²`, the moments of the pairwise differences in one population. -/
example (θ : ℝ) : hkaDivMean θ 0 1 = θ ∧ hkaDivVar θ 0 1 = θ + θ ^ 2 := by
  constructor
  · norm_num [hkaDivMean]
  · norm_num [hkaDivVar, hkaDivMean]

/-- Positivity in the domain. -/
example : 0 < hkaPolyVar 0.01 10 ∧ 0 < hkaDivVar 0.01 4 0.5 :=
  ⟨hkaPolyVar_pos (by norm_num) (by norm_num), hkaDivVar_pos (by norm_num) (by norm_num)
    (by norm_num)⟩

/-- The true parameters solve HKA's equations at the expected counts, for two loci. -/
example : hkaEquations 5 7 ![1, 2] 3 0.5 (fun i => hkaPolyMean (![1, 2] i) 5)
    (fun i => hkaPolyMean (0.5 * ![1, 2] i) 7) (fun i => hkaDivMean (![1, 2] i) 3 0.5) :=
  hkaEquations_expected 5 7 ![1, 2] 3 0.5

/-- Outside the domain (`f = -1`, no separation) the divergence variance degenerates to
`0`. -/
example (θ : ℝ) : hkaDivVar θ 0 (-1) = 0 := by
  simp [hkaDivVar, hkaDivMean]

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.HKA
