/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.McDonaldKreitman
import Mathlib.Tactic.NormNum

/-!
# Tests for the McDonald–Kreitman test and the Smith–Eyre-Walker `α`

A model with one adaptive substitution per unit neutral divergence (`α = 2 / 3`), the neutral
case `A = 0` (`α = 0`, equal nonsynonymous proportions), the classical Adh table of McDonald &
Kreitman (`D_n = 7`, `D_s = 17`, `P_n = 2`, `P_s = 42`: `α̂ = 130 / 147`), and a junk value.
-/

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.McDonaldKreitman

open MathlibExt.Biology.PopulationGenetics.McDonaldKreitman

/-- A model with `L_s = L_n = 1`, `f₀ = 1 / 2`, unit rates and `A = 1` (non-vacuity). -/
noncomputable def adaptive : MKModel where
  Ls := 1
  Ln := 1
  f₀ := 1 / 2
  polyRate := 1
  divRate := 1
  A := 1
  Ls_pos := one_pos
  Ln_pos := one_pos
  f₀_pos := by norm_num
  f₀_le_one := by norm_num
  polyRate_pos := one_pos
  divRate_pos := one_pos
  A_nonneg := zero_le_one

/-- The same model without adaptive substitutions. -/
noncomputable def neutral : MKModel := { adaptive with A := 0, A_nonneg := le_rfl }

/-- `E D_n = 1 / 2 + 1`, so `α = 2 / 3`. -/
example : adaptive.alpha = 2 / 3 := by
  norm_num [MKModel.alpha, MKModel.EDn, adaptive]

/-- `α̂` at the expected counts recovers `α = 2 / 3`. -/
example : alphaHat adaptive.EDn adaptive.EDs adaptive.EPn adaptive.EPs = 2 / 3 := by
  rw [MKModel.alphaHat_expected]
  norm_num [MKModel.alpha, MKModel.EDn, adaptive]

/-- With adaptive substitutions the nonsynonymous proportions differ. -/
example : adaptive.EDn / (adaptive.EDn + adaptive.EDs) ≠
    adaptive.EPn / (adaptive.EPn + adaptive.EPs) := by
  rw [Ne, MKModel.propNonsyn_eq_iff]
  norm_num [adaptive]

/-- In the neutral model the nonsynonymous proportions agree and `α = 0`. -/
example : neutral.EDn / (neutral.EDn + neutral.EDs) =
      neutral.EPn / (neutral.EPn + neutral.EPs) ∧ neutral.alpha = 0 :=
  ⟨neutral.propNonsyn_eq_iff.mpr rfl, by simp [MKModel.alpha, neutral]⟩

/-- McDonald & Kreitman's Adh table: `α̂ = 1 - (17 · 2) / (7 · 42) = 130 / 147` and
`NI = 17 / 147`. -/
example : alphaHat 7 17 2 42 = 130 / 147 ∧ neutralityIndex 7 17 2 42 = 17 / 147 := by
  norm_num [alphaHat, neutralityIndex]

/-- Junk value: with no nonsynonymous fixed difference the denominator vanishes and
`α̂ = 1 - x / 0 = 1`. -/
example : alphaHat 0 17 2 42 = 1 := by
  norm_num [alphaHat]

end MathlibExtTest.Biology.PopulationGenetics.McDonaldKreitman
