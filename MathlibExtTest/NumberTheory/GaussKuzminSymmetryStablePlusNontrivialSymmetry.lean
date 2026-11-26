/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GaussKuzminSymmetryStablePlusNontrivialSymmetry

/-! # Tests for nontrivial symmetries from stable strings -/

namespace MathlibExtTest.NumberTheory.GaussKuzminSymmetryStablePlusNontrivialSymmetry

open MetaMathlibExt

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

end MathlibExtTest.NumberTheory.GaussKuzminSymmetryStablePlusNontrivialSymmetry
