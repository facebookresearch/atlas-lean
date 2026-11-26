/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GaussKuzminSymmetryStablePlusNontrivialSymmetry
import Mathlib.Tactic.NormNum

/-! # Tests for nontrivial symmetries from stable strings and the explicit Gauss–Kuzmin mass -/

namespace MathlibExtTest.NumberTheory.GaussKuzminSymmetryStablePlusNontrivialSymmetry

open MetaMathlibExt Real

-- The string `(1, 2)` is stable, so its symmetrized extension has a nontrivial symmetry.
example : HasNontrivialSymmetry [2, 1, 1, 3] := by
  have ha : ∀ x ∈ ([1, 2] : List ℕ), 0 < x := by decide
  have hne : ([1, 2] : List ℕ) ≠ [] := by decide
  have hst : IsStableString [1, 2] := by
    unfold IsStableString
    decide
  obtain ⟨hperm, hne1, hne2, hmass⟩ :=
    stable_plus_nontrivial_symmetry [1, 2] ha hne hst
  have hdrop : ([1, 2] : List ℕ).dropLast = [1] := by decide
  have hlast : ([1, 2] : List ℕ).getLast hne = 2 := rfl
  rw [hdrop, hlast] at hperm hne1 hne2 hmass
  exact ⟨[2, 3, 1, 1], hperm, hne1, hne2, hmass⟩

-- Reversal symmetry on a concrete two-digit string: `[1, 2]` reverses to `[2, 1]`.
example : gaussKuzminMass [1, 2] = gaussKuzminMass [2, 1] := by
  have h := (gaussKuzminMass_eq_abs_logb [1, 2] (by decide)).1
  have r : [1, 2].reverse = [2, 1] := rfl
  rw [r] at h
  exact h

-- The explicit formula on the one-digit string `[1]`: its convergent matrix is
-- `!![0, 1; 1, 1]`, so the mass is `|logb 2 (3 / 4)|`.
example : gaussKuzminMass [1] = |logb 2 (3 / 4 : ℝ)| := by
  have h := (gaussKuzminMass_eq_abs_logb [1] (by decide)).2
  have e01 : convergentMatrix [1] 0 1 = 1 := by decide
  have e11 : convergentMatrix [1] 1 1 = 1 := by decide
  have e10 : convergentMatrix [1] 1 0 = 1 := by decide
  simp only [e01, e11, e10, Int.cast_one, show [1].length = 1 from rfl, pow_one] at h
  norm_num at h
  exact h

-- Corollary: every Gauss–Kuzmin mass is nonnegative.
example (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) : 0 ≤ gaussKuzminMass a := by
  rw [(gaussKuzminMass_eq_abs_logb a ha).2]
  exact abs_nonneg _

end MathlibExtTest.NumberTheory.GaussKuzminSymmetryStablePlusNontrivialSymmetry
