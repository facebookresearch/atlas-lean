/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Classical.FullSibMating
import Mathlib.Tactic.NormNum

/-! # Regression tests for the full-sib non-identity recurrence -/

namespace MathlibExt.Biology.PopulationGenetics.Classical.FullSibMating

-- The non-inbred, unrelated starting pair gives the first steps of Figure 5.8.
example : nonIdentity 1 1 0 = (1, 1) ∧ nonIdentity 1 1 1 = (1, 3 / 4) ∧
    nonIdentity 1 1 2 = (3 / 4, 5 / 8) ∧ nonIdentity 1 1 3 = (5 / 8, 1 / 2) := by
  norm_num [nonIdentity]

-- Unequal starts distinguish the two parental contributions; the first coordinate can rise.
example : nonIdentity 0 1 0 = (0, 1) ∧ nonIdentity 0 1 1 = (1, 1 / 2) ∧
    nonIdentity 1 0 1 = (0, 1 / 4) ∧ nonIdentity 1 0 2 = (1 / 4, 1 / 8) := by
  norm_num [nonIdentity]

example (t : ℕ) : nonIdentity 0 0 t = (0, 0) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [nonIdentity, ih]

-- The asymmetric founder state exercises both coefficients in the closed form.
example :
    let p : ℝ := (1 + Real.sqrt 5) / 4
    let m : ℝ := (1 - Real.sqrt 5) / 4
    ∀ t : ℕ, (nonIdentity 0 1 t).2 =
      (1 / 2 - m) / (p - m) * p ^ t + (p - 1 / 2) / (p - m) * m ^ t := by
  obtain ⟨_, _, _, _, _, hClosed, _, _⟩ :=
    nonIdentity_formula (h₀ := 0) (k₀ := 1) (by simp) (by simp)
  simpa using hClosed

-- The nonzero hypothesis permits k₀ = 0. Check the coefficient and the generation shift in the
-- normalized within-individual limit against the concrete first-generation value 1/4.
example :
    let p : ℝ := (1 + Real.sqrt 5) / 4
    let m : ℝ := (1 - Real.sqrt 5) / 4
    Filter.Tendsto (fun t ↦ (nonIdentity 1 0 t).1 / p ^ t) Filter.atTop
      (nhds ((1 / 4 / (p - m)) / p)) := by
  obtain ⟨_, _, _, _, _, _, _, hAsymptotic⟩ :=
    nonIdentity_formula (h₀ := 1) (k₀ := 0) (by simp) (by simp)
  obtain ⟨_, _, hWithin⟩ := hAsymptotic (Or.inl one_ne_zero)
  simpa using hWithin

end MathlibExt.Biology.PopulationGenetics.Classical.FullSibMating
