/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.StatisticalGenetics.PopulationAttributableFraction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open WantedExt.Biology.StatisticalGenetics.PopulationAttributableFractionWanted

-- Independently check the witness by adding the exposed and unexposed case masses.
-- Levin's implied risk instead mixes the two intervention risks at the marginal exposure rate.
example :
    let pz : Fin 2 → ℝ := ![1 / 2, 1 / 2]
    let e : Fin 2 → ℝ := ![1 / 4, 3 / 4]
    let r₀ : Fin 2 → ℝ := ![1 / 4, 1 / 2]
    let r₁ : Fin 2 → ℝ := ![1 / 2, 1 / 2]
    let prevalence := ∑ z, pz z * e z
    let baseline := ∑ z, pz z * r₀ z
    let exposed := ∑ z, pz z * r₁ z
    let observed := (∑ z, pz z * e z * r₁ z) + ∑ z, pz z * (1 - e z) * r₀ z
    let levinRisk := (1 - prevalence) * baseline + prevalence * exposed
    (∀ z, 0 < pz z ∧ 0 < e z ∧ e z < 1 ∧ 0 < r₀ z ∧ r₀ z ≤ 1 ∧ 0 < r₁ z ∧ r₁ z ≤ 1) ∧
      ∑ z, pz z = 1 ∧ e 0 ≠ e 1 ∧ r₀ 0 ≠ r₀ 1 ∧
      prevalence = 1 / 2 ∧ baseline = 3 / 8 ∧ exposed / baseline = 4 / 3 ∧ observed = 13 / 32 ∧
      1 - baseline / levinRisk = 1 / 7 ∧ 1 - baseline / observed = 1 / 13 ∧
      1 - baseline / levinRisk ≠ 1 - baseline / observed := by
  dsimp only
  constructor
  · intro z
    fin_cases z <;> norm_num
  · norm_num [Fin.sum_univ_two]

-- The public statement is available from the production import alone.
example :
    ∃ pz e r₀ r₁ : Fin 2 → ℝ, (∀ z, 0 < pz z) ∧ ∑ z, pz z = 1 ∧ (∀ z, 0 < e z) ∧
      (∀ z, e z < 1) ∧ (∀ z, 0 < r₀ z) ∧ (∀ z, r₀ z ≤ 1) ∧ (∀ z, 0 < r₁ z) ∧ (∀ z, r₁ z ≤ 1) ∧
      e 0 ≠ e 1 ∧ r₀ 0 ≠ r₀ 1 ∧
      levin (exposurePrevalence pz e) (totalStandardizedRR pz r₀ r₁) ≠ causalPAF pz e r₀ r₁ :=
  exists_levin_totalRR_ne_causalPAF
