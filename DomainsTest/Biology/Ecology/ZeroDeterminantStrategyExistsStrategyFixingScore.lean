/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Ecology.ZeroDeterminantStrategyExistsStrategyFixingScore
import Mathlib.Tactic.NormNum

/-!
# Tests for fixing any score of Y in the Prisoner's Dilemma

With the classic payoffs `T = 5`, `R = 3`, `P = 1`, `S = 0`, the equalizer theorem is
instantiated at an interior score `σ = 2` and at the two endpoints `σ = P = 1` and
`σ = R = 3`: in each case the obtained strategy fixes Y's long-run score, and the
nondegeneracy witness gives strategies with nonzero Press–Dyson determinant.
-/

@[expose] public section

namespace DomainsTest.Biology.Ecology.ZeroDeterminantStrategyExistsStrategyFixingScore

open WantedExt.Biology.Ecology.ZeroDeterminantStrategyWanted

example : ∃ p : Fin 4 → ℝ, IsStrategy p ∧ ∀ q : Fin 4 → ℝ, IsStrategy q →
    ∀ v : Fin 4 → ℝ, IsStationary (markovMatrix p q) v → v ⬝ᵥ payoffY 3 0 5 1 = 2 := by
  obtain ⟨p, hpstrat, _, _, _, _, _, hfix⟩ :=
    exists_strategy_fixing_score (R := 3) (S := 0) (T := 5) (P := 1) (σ := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨p, hpstrat, fun q hq v hv => hfix q hq v hv⟩

example : ∃ p : Fin 4 → ℝ, IsStrategy p ∧ ∀ q : Fin 4 → ℝ, IsStrategy q →
    ∀ v : Fin 4 → ℝ, IsStationary (markovMatrix p q) v → v ⬝ᵥ payoffY 3 0 5 1 = 1 := by
  obtain ⟨p, hpstrat, _, _, _, _, _, hfix⟩ :=
    exists_strategy_fixing_score (R := 3) (S := 0) (T := 5) (P := 1) (σ := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨p, hpstrat, fun q hq v hv => hfix q hq v hv⟩

example : ∃ p : Fin 4 → ℝ, IsStrategy p ∧ ∀ q : Fin 4 → ℝ, IsStrategy q →
    ∀ v : Fin 4 → ℝ, IsStationary (markovMatrix p q) v → v ⬝ᵥ payoffY 3 0 5 1 = 3 := by
  obtain ⟨p, hpstrat, _, _, _, _, _, hfix⟩ :=
    exists_strategy_fixing_score (R := 3) (S := 0) (T := 5) (P := 1) (σ := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨p, hpstrat, fun q hq v hv => hfix q hq v hv⟩

example : ∃ p q : Fin 4 → ℝ, IsStrategy p ∧ IsStrategy q ∧ pdDet p q 1 ≠ 0 := by
  obtain ⟨p, hpstrat, _, _, _, _, ⟨q, hqstrat, hdet⟩, _⟩ :=
    exists_strategy_fixing_score (R := 3) (S := 0) (T := 5) (P := 1) (σ := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨p, q, hpstrat, hqstrat, hdet⟩

end DomainsTest.Biology.Ecology.ZeroDeterminantStrategyExistsStrategyFixingScore
